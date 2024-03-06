let unchanged[r] { r = (r)' }

one sig AuctionHouse {
    var has: set Bidder
}

sig Bidder {
    var bids: set Bid
}

sig Item {}

abstract sig ItemSet {
    var has: set Item
}

one sig ActiveItems extends ItemSet {}
one sig WonItems extends ItemSet {}
one sig InactiveItems extends ItemSet {}

sig Bid {
    var on: lone Item  // 'lone' ensures that a Bid may be on at most one Item
}



fact ItemsCanOnlyBeInOneItemSet {
    always { 
        disj [ActiveItems.has, WonItems.has, InactiveItems.has]
    }
}

pred StartNewItemBid[i: Item] {
    i in InactiveItems.has
    InactiveItems.has = InactiveItems.has - i
    ActiveItems.has = ActiveItems.has + i
    unchanged[AuctionHouse.has]
    unchanged[WonItems.has]
    unchanged[Bidder.bids]
}

fact InitialState {
    all i: Item | i in InactiveItems.has
    no b: Bid | some b.on  // Ensuring no bid is initially on any item
    no b: Bidder | some b.bids  // Ensuring no bidder has any bids initially
}


pred PlaceBid[b: Bidder, i: Item] {
    i in ActiveItems.has  // The item must be active
    no b.bids.on & i  // Ensure no existing bid from this bidder is on this item
    some newBid: Bid | {  // Creating a new bid
        newBid.on = i
        b.bids = b.bids + newBid
    }
    unchanged[AuctionHouse.has]
    unchanged[ActiveItems.has - i]
    unchanged[WonItems.has]
    unchanged[InactiveItems.has]
}



pred skip {
    unchanged[AuctionHouse.has]
    unchanged[ActiveItems.has]
    unchanged[WonItems.has]
    unchanged[InactiveItems.has]
    unchanged[Bidder.bids]
}

pred setup {
    all bid: Bid | bid in Bidder.bids
    all b: Bidder | b in AuctionHouse.has
}

fact trans {
    setup
    always (skip or some i: Item | StartNewItemBid[i] or some b: Bidder, i: Item | PlaceBid[b, i])
}

run setup {} for 2
