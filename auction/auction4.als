let unchanged[r] { r = (r)' }

one sig AuctionHouse {
	var has : set Bidder
// one ActiveItem (for now)
}
//sig Auctioneer {} //not sure
sig Bidder {
	var bids : set Item
}

sig Item {currentPrice: Int}
{
currentPrice = 1
// var currentBids
// lone maxBid
}

abstract sig ItemSet {
	var has : set Item
}

one sig InactiveItems extends ItemSet { }
one sig ActiveItems extends ItemSet { }
one sig WonItems extends ItemSet { }

//sig BidStates {} 
//one sig Pending, Accepted, Rejected, Won, Lost extends BidStates {}



fact ItemsCanOnlyBeInOneItemSet {
    always { 
        disj [ActiveItems.has, WonItems.has, InactiveItems.has]
    }
}

pred StartNewItemBid[i : Item] {
	i in InactiveItems.has
	
	InactiveItems.has' = InactiveItems.has - i
	ActiveItems.has' = ActiveItems.has + i

	unchanged[AuctionHouse.has]
	unchanged[WonItems.has]
	unchanged[Bidder.bids]
}

pred PlaceBid[b: Bidder, i: Item] {
    i in ActiveItems.has  // The item must be active

    b.bids' = b.bids + i

    unchanged[AuctionHouse.has]
    unchanged[ActiveItems.has]
    unchanged[WonItems.has]
    unchanged[InactiveItems.has]
}



// pred AuctioneerCheckBid

pred skip {
	unchanged[AuctionHouse.has]
	unchanged[ActiveItems.has]
	unchanged[WonItems.has]
	unchanged[InactiveItems.has]
	unchanged[Bidder.bids]
}

pred setup {
	//all bid : Bid | bid in Bidder.bids
	all b: Bidder | no b.bids
    	all b: Bidder | b in AuctionHouse.has
	all i : Item | i in InactiveItems.has
}

fact trans {
	setup
    always ( skip or
            some b : Bidder, i : Item | StartNewItemBid[i] or
				PlaceBid[b, i]
   )    
}

run setup {} for exactly 2 Item, exactly 3 Bidder
