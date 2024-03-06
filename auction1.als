let unchanged[r] { r = (r)' }

one sig AuctionHouse {
	var has : set Bidder
// one ActiveItem (for now)
}
//sig Auctioneer {} //not sure
sig Bidder {
	var bids : set Bid
}

sig Item {
// var currentBids
// lone maxBid
}

abstract sig ItemSet {
	var has : set Item
}

one sig ActiveItems extends ItemSet { }
one sig WonItems extends ItemSet { }
one sig InactiveItems extends ItemSet { }

//sig BidStates {} 
//one sig Pending, Accepted, Rejected, Won, Lost extends BidStates {}

sig Bid {
	var on : one Item
}

fact ItemsCanOnlyBeInOneItemSet {
    always { 
        disj [ActiveItems.has, WonItems.has, InactiveItems.has]
    }
}

pred StartNewItemBid[i : Item] {
	//i in InactiveItems.has	// for now, limit the items to one
	InactiveItems.has = InactiveItems.has - i
	ActiveItems.has = ActiveItems.has + i


	unchanged[AuctionHouse.has]
	unchanged[WonItems.has]
	unchanged[Bidder.bids]
}

// pred BidderSendNewBid

// pred AuctioneerCheckBid

pred skip {
	unchanged[AuctionHouse.has]
	unchanged[ActiveItems.has]
	unchanged[WonItems.has]
	unchanged[InactiveItems.has]
	unchanged[Bidder.bids]
}

pred setup {
	all bid : Bid | bid in Bidder.bids
	all b: Bidder | no b.bids
    	all b: Bidder | b in AuctionHouse.has
	//all i : Item | i in InactiveItems.has
}

fact trans {
    always ( skip or
            some i : Item | StartNewItemBid[i]
    )    
}

run setup {} for 2
