let unchanged[r] { r = (r)' }

one sig AuctionHouse {
    var has: set Bidder
}

sig Bidder {
    var bids: set Bid,
    var won: set Item
}

sig Bid in Bidder {
    bidValue: Int,
    var bidOn: set Item  // Ensuring a bid is always associated with an item
} {
    some bidOn  // Adding constraint to ensure bid is on an item
}

sig Item {
    var currentPrice: Int,
    var currentBids: set Bid  // Changed to set of Bid
}

abstract sig ItemSet {
    var has: set Item
}

one sig InactiveItems extends ItemSet { }
one sig ActiveItems extends ItemSet { }

fact NoBidsOnWonItems {
    all b: Bidder | no b.won & b.bids.bidOn
}

fact NoBidsOnInactiveItems {
    no i: InactiveItems.has, b: Bid | i in b.bidOn
}

fact ItemsCanOnlyBeInOneItemSet {
    always { 
        disj [ActiveItems.has, InactiveItems.has]
    }
}

pred StartNewItemBid[i: Item] {
    i in InactiveItems.has
    
    InactiveItems.has' = InactiveItems.has - i
    ActiveItems.has' = ActiveItems.has + i
    i.currentBids' = none  // Ensure no bids on a newly activated item

    unchanged[AuctionHouse.has]
    unchanged[Bidder.bids]
    unchanged[Bidder.won]
}

pred PlaceBid[b: Bidder, i: Item, value: Int] {
    i in ActiveItems.has
    value > i.currentPrice  // Ensuring the bid value is greater than the current price
    no b.won & i  // Ensure the bidder has not won the item
    no i.currentBids & b.bids  // Ensure no existing bids on this item from this bidder
    one newBid: Bid | {
        newBid.bidValue = value
        newBid.bidOn = i
        b.bids' = b.bids + newBid
        i.currentBids' = i.currentBids + newBid  // Add bid to item's currentBids
    }

    unchanged[AuctionHouse.has]
    unchanged[ActiveItems.has]
    unchanged[InactiveItems.has]
}

fact AllBidsMustBeOnItems {
    all b: Bidder | all bid: b.bids | some bid.bidOn
}

pred skip {
    unchanged[AuctionHouse.has]
    unchanged[ActiveItems.has]
    unchanged[InactiveItems.has]
    unchanged[Bidder.bids]
    unchanged[Bidder.won]
    unchanged[Item.currentPrice]
    unchanged[Item.currentBids]
}

pred setup {
    all b: Bidder | {
        b.bids = none
        b.won = none
        b in AuctionHouse.has
    }
    all i: Item | {
        i in InactiveItems.has
        i.currentPrice = 1  // Initializing currentPrice
        i.currentBids = none  // Initializing currentBids
    }
}

fact trans {
    setup
    always (skip or
            some b: Bidder, i: Item | StartNewItemBid[i] or
                                      PlaceBid[b, i, 5]  // Example bid value
    )
}

run example {} for exactly 1 Item, exactly 2 Bidder
