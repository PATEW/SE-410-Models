let unchanged[r] { r = (r)' }

one sig AuctionHouse {
	var has : set Bidder
}

sig Bidder {
	var bids : set Bid,
	var won : set Item
}

sig Bid in Bidder {
	bidValue: Int,
	var bidOn : set Item
}

sig Item {currentPrice: Int, currentBids: Int} {
	currentPrice = 1
	currentBids = 0
}

abstract sig ItemSet {
	var has : set Item
}

one sig InactiveItems extends ItemSet { }
one sig ActiveItems extends ItemSet { }

fact NoBidsOnWonItems {
    all b: Bidder | no b.won & (b.bids.bidOn)
}

fact NoBidsOnInactiveItems {
    no i: InactiveItems.has, b: Bid | i in b.bidOn
}

fact NoWonInactiveItems {
    all b: Bidder | no b.won & InactiveItems.has
}

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
	unchanged[Bidder.won]
}

pred PlaceBid[b: Bidder, i: Item] {
    i in ActiveItems.has  // The item must be active
    some bid: Bid | bid not in b.bids and bid.bidOn = none {
        b.bids' = b.bids + bid
        bid.bidOn' = bid.bidOn + i
        // Update bidValue as needed
        // bid.bidValue' = ...
    }
    unchanged[AuctionHouse.has]
    unchanged[ActiveItems.has]
    unchanged[InactiveItems.has]
    unchanged[Bidder.won]
}

pred skip {
	unchanged[AuctionHouse.has]
	unchanged[ActiveItems.has]
	unchanged[InactiveItems.has]
	unchanged[Bidder.bids]
	unchanged[Bidder.won]
}

pred setup {
    all b: Bidder | {
        b.bids = none  // Ensuring no bids for each bidder
        b.won = none   // Ensuring no won items for each bidder
        b in AuctionHouse.has // Ensuring each bidder is part of the AuctionHouse
    }
    all i: Item | i in InactiveItems.has // Ensuring all items start in InactiveItems
}

fact trans {
	setup
    always ( skip or
            some b: Bidder, i: Item | StartNewItemBid[i] or
            PlaceBid[b, i]
   )    
}

run example {} for exactly 1 Item, exactly 2 Bidder
