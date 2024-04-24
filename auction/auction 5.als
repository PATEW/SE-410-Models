let unchanged[r] { r = (r)' }

one sig AuctionHouse {
	var has : set Bidder
}

sig Bidder {
	var bids : set Bid,
	var won : set Item
}

sig Bid in Bidder 
{
	bidValue: Int,
	var bidOn : set Item
}

sig Item {currentPrice: Int, currentBids: Int}
{
	currentPrice = 1
	currentBids = 0
}

abstract sig ItemSet {
	var has : set Item
}

one sig InactiveItems extends ItemSet { }
one sig ActiveItems extends ItemSet { }

//sig BidStates {} 
//one sig Pending, Accepted, Rejected, Won, Lost extends BidStates {}

fact NoBidsOnWonItems {
    all b: Bidder | no b.won & (b.bids.bidOn)
}

fact NoBidsOnInactiveItems {
    no i: InactiveItems.has, b: Bid | i in b.bidOn
}

//fact NoWinningInactiveItems {
//   no i : InactiveItems.has, b: Bidder | in b.won
//}

fact AllBidsMustBeOnItems {
    all b: Bidder | all bid: b.bids | some bid.bidOn
}


fact ItemsCanOnlyBeInOneItemSet {
    always { 
        disj [ActiveItems.has, InactiveItems.has]
    }
}

pred StartNewItemBid[i : Item] {
	i in InactiveItems.has
	
	InactiveItems.has' = InactiveItems.has - i
	ActiveItems.has' = ActiveItems.has + i

	unchanged[AuctionHouse.has]
	unchanged[Bidder.bids]
}

pred PlaceBid[b: Bidder, i: Item] {
    i in ActiveItems.has  // The item must be active

    b.bids.bidOn' = b.bids.bidOn + i

    unchanged[AuctionHouse.has]
    unchanged[ActiveItems.has]
    unchanged[InactiveItems.has]
}

pred skip {
	unchanged[AuctionHouse.has]
	unchanged[ActiveItems.has]
	unchanged[InactiveItems.has]
	unchanged[Bidder.bids]
}

pred setup {
    all b: Bidder | {
        b.bids = none
        b.won = none
        b in AuctionHouse.has
    }
    all i: Item | i in InactiveItems.has
}

fact trans {
	setup
    always ( skip or
            some i : Item | StartNewItemBid[i]
				//PlaceBid[b, i]
   )    
}

run example {} for exactly 1 Item, exactly 2 Bidder
