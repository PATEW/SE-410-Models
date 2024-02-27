abstract sig LockComponent {}

sig Boat {}

abstract sig Wall extends LockComponent { 
    var state: one State 
}
one sig NorthWall, SouthWall extends Wall {}

sig State {} 
one sig Up, Down extends State {}

abstract sig Sensor extends LockComponent {
    var detects : set Boat
}
one sig NorthSensor, SouthSensor, LockSensor extends Sensor {}

sig Location {	
    var here : set Boat
}

one sig Lock extends Location {
    var hasSensor: one LockSensor,
    var hasWall: set Wall
}

one sig Downstream extends Location {
    var hasSensor: one SouthSensor
}
one sig Upstream extends Location {
    var hasSensor: one NorthSensor
}

fact BoatsCanOnlyBeInOneLocation {
    always { 
        disj [Downstream.here, Upstream.here, Lock.here]
    }
}

fact noBoatsInitiallyInsideLock {
    no Lock.here
}

fact setup {
    Lock.hasWall = NorthWall + SouthWall
    Lock.hasSensor = LockSensor
    Upstream.hasSensor = NorthSensor
    Downstream.hasSensor = SouthSensor
    all w: Wall | w.state = Up // Initial state for walls
    all s: Sensor | no s.detects // Initial state for sensors
}

pred AttemptToActivateSouthSensor[b : Boat] {
    b in Downstream.here

    Lock.hasWall' = Lock.hasWall
    Lock.hasSensor' = Lock.hasSensor
   
    NorthSensor.detects' = NorthSensor.detects
    LockSensor.detects' = LockSensor.detects
    SouthSensor.detects' = SouthSensor.detects + b

    Upstream.here' = Upstream.here
    Lock.here' = Lock.here
    Downstream.here' = Downstream.here
    
    NorthWall.state' = NorthWall.state
    SouthWall.state' = SouthWall.state
}

pred LowerSouthWall {
    LockSensor.detects = none
    SouthSensor.detects != none

    Lock.hasWall' = Lock.hasWall
    Lock.hasSensor' = Lock.hasSensor

    NorthSensor.detects' = NorthSensor.detects
    LockSensor.detects' = LockSensor.detects
    SouthSensor.detects' = SouthSensor.detects

    Upstream.here' = Upstream.here
    Lock.here' = Lock.here
    Downstream.here' = Downstream.here
    
    NorthWall.state' = NorthWall.state
    SouthWall.state' = Down
}

pred MoveIntoLockFromDownstream[b : Boat] {
    b in SouthSensor.detects
    SouthWall.state = Down

    Lock.hasWall' = Lock.hasWall
    Lock.hasSensor' = Lock.hasSensor

    NorthSensor.detects' = NorthSensor.detects
    LockSensor.detects' = LockSensor.detects + b 
    SouthSensor.detects' = SouthSensor.detects - b

    Upstream.here' = Upstream.here
    Lock.here' = Lock.here + b
    Downstream.here' = Downstream.here - b
    
    NorthWall.state' = NorthWall.state
    SouthWall.state' = SouthWall.state
}

let unchanged[r] { r = (r)' }
pred skip {
    unchanged[Downstream.here]
    unchanged[Upstream.here]
    unchanged[Lock.here]
    unchanged[Lock.hasWall]
    unchanged[Lock.hasSensor]
    unchanged[NorthWall.state]
    unchanged[SouthWall.state]
    unchanged[NorthSensor.detects]
    unchanged[SouthSensor.detects]
    unchanged[LockSensor.detects]
}

fact trans {
    always (skip or 
            some b : Boat | AttemptToActivateSouthSensor[b] or 
                            	        LowerSouthWall or 
                                        MoveIntoLockFromDownstream[b]
    )    
}

run example {} for 2
