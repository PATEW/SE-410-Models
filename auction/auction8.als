open util/integer
let unchanged[r] { r = (r)' }

sig Auctioneer {
    var has : set Item
}

sig Bidder {
	var won : set Item,
	var bidOn : set Item,
	bidValue: Int
	// State: HighestBidder
}

sig Item {
    currentPrice: Int,
    currentBids: Int
}{
    currentPrice = 1
    currentBids = 0
}

// pred PollBidder
pred PlaceBid[b: Bidder, i: Item] {
    i in Auctioneer.has  // The item must be in Auctioneer's inventory
    b.bidOn' = i
    //i.currentBids.plus[1]
    unchanged[Bidder.won]
    unchanged[Auctioneer.has]
}


pred skip {
    unchanged[Auctioneer.has]
    unchanged[Bidder.won]
    unchanged[Bidder.bidOn]
}

pred init {
    no Bidder.won
    no Bidder.bidOn
    all b : Bidder | b.bidValue = 0
    all i : Item | Auctioneer.has = i
}

fact trans {
	init
	always (some b : Bidder, i: Item | PlaceBid[b, i])
}

run {} for exactly 1 Item, exactly 4 Bidder, exactly 1 Auctioneer

