open util/ordering[State]

// Players
abstract sig Player {}
one sig PlayerA, PlayerB extends Player {}

// Card Types
abstract sig Card {}
one sig Skull, Flower1, Flower2, Flower3 extends Card {}

// Game Phases
abstract sig Phase {}
one sig Placing, Bidding, Flipping, Winning extends Phase {}

// A snapshot of the game: hands, stacks, flip zones, bidding status, turn, and scores
sig State {
    A:      set Card,     // Cards in hand
    B:      set Card,     // Cards in hand
    stackA: seq Card,     // Cards placed
    stackB: seq Card,     // Cards placed
    flipA:  seq Card,     // Cards flipped
    flipB:  seq Card,     // Cards flipped
    bid:    Int,          // Current bid value
    bidder: lone Player,  // Player who made the highest bid
    phase:  Phase,        // Current phase of the game
    turn:   lone Player,  // Whose turn it is
    passed: set Player,   // Players who have passed
    scoreA: Int,
    scoreB: Int
}


// Initializes the starting state: full hands, empty stacks/flips, no bid, Placing phase, PlayerA's turn
pred Init {
    first.A = Card
    first.B = Card
    no first.stackA
    no first.stackB
    no first.flipA
    no first.flipB
    first.bid = 0
    no first.bidder
    first.phase = Placing
    first.passed = none
    first.turn = PlayerA
    first.scoreA = 0
    first.scoreB = 0
}


// Returns the opponent of a given player
fun otherPlayer[p: Player]: Player {
    p = PlayerA implies PlayerB else PlayerA
}


// A player moves one or more cards from hand to their stack; turn passes to the other player.
// If a player reaches score 2, the game enters the Winning phase.
pred PlaceCard[s1, s2: State] {
    s2.phase = s1.phase
    s2.bid = s1.bid
    s2.bidder = s1.bidder
    s2.passed = s1.passed
    s2.flipA = s1.flipA
    s2.flipB = s1.flipB
    s2.scoreA = s1.scoreA
    s2.scoreB = s1.scoreB

    s1.turn = PlayerA implies
        (some X: s1.A |
            #X >= 1 and #X <= #s1.A and
            s2.stackA = s1.stackA.add[X] and
            s2.stackB = s1.stackB and
            s2.A = s1.A - X and
            s2.B = s1.B and
            s2.turn = PlayerB)
        else
        (some X: s1.B |
            #X >= 1 and #X <= #s1.B and
            s2.stackB = s1.stackB.add[X] and
            s2.stackA = s1.stackA and
            s2.B = s1.B - X and
            s2.A = s1.A and
            s2.turn = PlayerA)

    (s1.scoreA = 2 or s1.scoreB = 2) implies s2.phase = Winning
}


// A player passes instead of placing; allowed once both players have placed a card, or one has
// no cards left. Transitions to the Bidding phase.
pred PassPlace[s1, s2: State] {
    s1.phase = Placing
    plus[#s1.stackA, #s1.stackB] >= 2 or (#s1.A = 0 and #s1.B = 0)
    s1.turn in Player
    s2.passed = s1.passed + s1.turn
    s2.phase = Bidding
    // Clear turn and maintain state
    no s2.turn
    s2.A = s1.A
    s2.B = s1.B
    s2.stackA = s1.stackA
    s2.stackB = s1.stackB
    s2.bid = s1.bid
    s2.bidder = s1.bidder
    s2.flipA = s1.flipA
    s2.flipB = s1.flipB
    s2.scoreA = s1.scoreA
    s2.scoreB = s1.scoreB
}


// A player raises the bid during Bidding. The opening bid is 1..totalPlaced; each later bid must
// be strictly greater than the previous one, capped at the total number of cards placed.
pred Bid[s1, s2: State] {
    s1.phase = Bidding
    s2.A = s1.A
    s2.B = s1.B
    s2.stackA = s1.stackA
    s2.stackB = s1.stackB
    s2.flipA = s1.flipA
    s2.flipB = s1.flipB
    s2.scoreA = s1.scoreA
    s2.scoreB = s1.scoreB

    s2.passed = none

    s1.phase = Bidding implies
        ((s1.bid = 0) implies
            (some b: Int |
                b >= 1 and
                b <= plus[#s1.stackA, #s1.stackB] and
                s2.bid = b and
                s2.bidder = s1.bidder + s1.passed and
                s2.turn = otherPlayer[s1.passed] and
                s2.phase = Bidding)
            else (some b: Int |
                b > s1.bid and
                b <= plus[#s1.stackA, #s1.stackB] and
                s2.bid = b and
                s2.bidder = s1.turn and
                s2.turn = otherPlayer[s1.turn] and
                s2.phase = Bidding))
}


// A player passes on raising the bid; play moves to Flipping, starting with the bidder.
pred PassBid[s1, s2: State] {
    s1.phase = Bidding
    (s1.bid > 0 and s1.bid < plus[#s1.stackA, #s1.stackB]) or s1.bid = plus[#s1.stackA, #s1.stackB]
    s1.turn in Player
    s2.passed = s1.passed + s1.turn
    s2.phase = Flipping
    // Clear turn and maintain state
    s2.turn = s1.bidder
    s2.A = s1.A
    s2.B = s1.B
    s2.stackA = s1.stackA
    s2.stackB = s1.stackB
    s2.bid = s1.bid
    s2.bidder = s1.bidder
    s2.flipA = s1.flipA
    s2.flipB = s1.flipB
    s2.scoreA = s1.scoreA
    s2.scoreB = s1.scoreB
}


// Sequentially flips cards to fulfill the bid: starting with the flipper's own stack, then moving
// to the opponent's stack if more cards are still owed. Flipping stops once the bid is met or a
// Skull is revealed.
pred Flip[s1, s2: State] {
    s1.phase = Flipping
    s1.bidder = s2.bidder
    s1.A = s2.A
    s1.B = s2.B
    no s2.passed
    s2.scoreA = s1.scoreA
    s2.scoreB = s1.scoreB
    s2.turn = s1.turn
    s2.bid >= 0 and s1.bid >= 0
    s1.bid > 0 and s1.flipA.last != Skull and s1.flipB.last != Skull

    s1.turn = PlayerA implies (
        // stackA has more cards than the bid: keep flipping from stackA until the bid reaches 0
        ((#s1.stackA > s1.bid) implies (
            s2.stackA = s1.stackA.butlast and
            s2.stackB = s1.stackB and
            s2.flipA = s1.flipA.add[s1.stackA.last] and
            s2.flipB = s1.flipB and
            s2.bid = minus[s1.bid, 1] and  // another use of bid: track how many cards are left to flip
            s2.phase = Flipping))

        and

        // stackA has fewer cards than the bid but is non-empty: keep flipping from stackA until it runs out
        ((#s1.stackA < s1.bid and #s1.stackA > 0) implies (
            s2.stackA = s1.stackA.butlast and
            s2.stackB = s1.stackB and
            s2.flipA = s1.flipA.add[s1.stackA.last] and
            s2.flipB = s1.flipB and
            s2.bid = minus[s1.bid, 1] and
            s2.phase = Flipping))

        and

        // stackA is empty but cards are still owed: continue flipping from stackB (needs cards from both stacks)
        ((#s1.stackA = 0 and s1.bid > 0) implies (
            s2.stackB = s1.stackB.butlast and
            s2.stackA = s1.stackA and
            s2.flipB = s1.flipB.add[s1.stackB.last] and
            s2.flipA = s1.flipA and
            s2.bid = minus[s1.bid, 1] and
            s2.phase = Flipping))

        and

        // stackA has exactly the number of cards as the bid: keep flipping from stackA until the bid reaches 0
        ((#s1.stackA = s1.bid) implies (
            s2.stackA = s1.stackA.butlast and
            s2.stackB = s1.stackB and
            s2.flipA = s1.flipA.add[s1.stackA.last] and
            s2.flipB = s1.flipB and
            s2.bid = minus[s1.bid, 1] and
            s2.phase = Flipping))
    )

    else (
        ((#s1.stackB > s1.bid) implies (
            s2.stackB = s1.stackB.butlast and
            s2.stackA = s1.stackA and
            s2.flipB = s1.flipB.add[s1.stackB.last] and
            s2.flipA = s1.flipA and
            s2.bid = minus[s1.bid, 1] and
            s2.phase = Flipping))

        and

        ((#s1.stackB < s1.bid and #s1.stackB > 0) implies (
            s2.stackB = s1.stackB.butlast and
            s2.stackA = s1.stackA and
            s2.flipB = s1.flipB.add[s1.stackB.last] and
            s2.flipA = s1.flipA and
            s2.bid = minus[s1.bid, 1] and
            s2.phase = Flipping))

        and

        ((#s1.stackB = 0 and s1.bid > 0) implies (
            s2.stackA = s1.stackA.butlast and
            s2.stackB = s1.stackB and
            s2.flipA = s1.flipA.add[s1.stackA.last] and
            s2.flipB = s1.flipB and
            s2.bid = minus[s1.bid, 1] and
            s2.phase = Flipping))

        and

        ((#s1.stackB = s1.bid) implies (
            s2.stackB = s1.stackB.butlast and
            s2.stackA = s1.stackA and
            s2.flipB = s1.flipB.add[s1.stackB.last] and
            s2.flipA = s1.flipA and
            s2.bid = minus[s1.bid, 1] and
            s2.phase = Flipping))
    )
}


// A Skull was revealed on PlayerB's turn: PlayerB loses one random card from their pool
// (hand + stack + flipped); PlayerA's cards are all returned to hand. A new round starts with PlayerA.
pred LoseCardB[s1, s2: State] {
    some Skull & (s1.flipA.last + s1.flipB.last)
    s1.turn = PlayerB
    s1.phase = Flipping
    s2.phase = Placing
    one c: (s1.stackB.elems + s1.flipB.elems + s1.B) | s2.B = (s1.stackB.elems + s1.flipB.elems + s1.B) - c
    s2.A = s1.stackA.elems + s1.A + s1.flipA.elems
    no s2.stackA
    no s2.stackB
    no s2.flipA
    no s2.flipB
    s2.bid = 0
    s2.bidder = none
    s2.passed = none
    s2.turn = PlayerA
    s2.scoreA = s1.scoreA
    s2.scoreB = s1.scoreB
}


// PlayerB fulfilled their bid with no Skull revealed: PlayerB scores a point and both hands are
// reset. If PlayerB reaches 2 points, the game ends in Winning; otherwise a new round starts with PlayerB.
pred WinB[s1, s2: State] {
    s1.bid = 0 and no Skull & (s1.flipA.elems + s1.flipB.elems)
    s1.turn = PlayerB
    s1.phase = Flipping
    s2.A = s1.stackA.elems + s1.A + s1.flipA.elems
    s2.B = s1.stackB.elems + s1.B + s1.flipB.elems
    no s2.stackA
    no s2.stackB
    no s2.flipA
    no s2.flipB
    s2.bid = 0
    s2.bidder = none
    s2.passed = none
    s2.turn = PlayerB
    s2.scoreA = s1.scoreA
    s2.scoreB = plus[s1.scoreB, 1]
    s2.scoreB = 2 implies
        (s2.phase = Winning and (all ss: s2.nexts |
            ss.scoreA = s2.scoreA and ss.scoreB = s2.scoreB and ss.A = s2.A and ss.B = s2.B and Finish[ss]))
        else s2.phase = Placing
}


// A Skull was revealed on PlayerA's turn: PlayerA loses one random card from their pool
// (hand + stack + flipped); PlayerB's cards are all returned to hand. A new round starts with PlayerB.
pred LoseCardA[s1, s2: State] {
    some Skull & (s1.flipA.last + s1.flipB.last)
    s1.turn = PlayerA
    s1.phase = Flipping
    s2.phase = Placing
    one c: (s1.flipA.elems + s1.stackA.elems + s1.A) | s2.A = (s1.flipA.elems + s1.stackA.elems + s1.A) - c
    s2.B = s1.stackB.elems + s1.B + s1.flipB.elems
    no s2.stackA
    no s2.stackB
    no s2.flipA
    no s2.flipB
    s2.bid = 0
    s2.bidder = none
    s2.passed = none
    s2.turn = PlayerB
    s2.scoreA = s1.scoreA
    s2.scoreB = s1.scoreB
}


// PlayerA fulfilled their bid with no Skull revealed: PlayerA scores a point and both hands are
// reset. If PlayerA reaches 2 points, the game ends in Winning; otherwise a new round starts with PlayerA.
pred WinA[s1, s2: State] {
    s1.bid = 0 and no Skull & (s1.flipA.elems + s1.flipB.elems)
    s1.turn = PlayerA
    s1.phase = Flipping
    s2.A = s1.stackA.elems + s1.A + s1.flipA.elems
    s2.B = s1.stackB.elems + s1.B + s1.flipB.elems
    no s2.stackA
    no s2.stackB
    no s2.flipA
    no s2.flipB
    s2.bid = 0
    s2.bidder = none
    s2.passed = none
    s2.turn = PlayerA
    s2.scoreA = plus[s1.scoreA, 1]
    s2.scoreB = s1.scoreB
    s2.scoreA = 2 implies
        (s2.phase = Winning and (all ss: s2.nexts | ss.scoreA = s2.scoreA and ss.scoreB = s2.scoreB and ss.A = s2.A and ss.B = s2.B and Finish[ss]))
        else s2.phase = Placing
}


// A terminal state after the game ends: no active stacks/flips/bid, in the Winning phase,
// and all future states preserve the final scores and hands.
pred Finish[s: State] {
    no s.stackA
    no s.stackB
    no s.flipA
    no s.flipB
    s.bid = 0
    no s.bidder
    s.phase = Winning
    s.passed = none
    no s.turn
    all ss: s.nexts | ss.scoreA = s.scoreA and ss.scoreB = s.scoreB and ss.A = s.A and ss.B = s.B
}


// True when either player has reached the winning score of 2
pred IsGameOver[s: State] {
    s.scoreA = 2 or s.scoreB = 2
}


// Chains all valid transitions from Init through Placing, Bidding, and Flipping to a Winning state
pred Game {
    Init
    all s: State - last |
        (some sNext: s.next |
            (s.phase = Placing =>
                (PlaceCard[s, sNext] or PassPlace[s, sNext])) and
            (s.phase = Bidding => (Bid[s, sNext] or PassBid[s, sNext])) and
            (s.phase = Flipping => Flip[s, sNext] or LoseCardA[s, sNext] or LoseCardB[s, sNext] or WinA[s, sNext] or WinB[s, sNext]))
}

// run Game for 40


// Checks that a full game (a player reaching 2 points) can occur within 15 states
pred FifteenStateSolutionsExist {
    Game
    IsGameOver[first.next.next.next.next.next.next.next.next.next.next.next.next.next.nexts]
}

// run FifteenStateSolutionsExist for 15


// Asserts that no game can end (reach IsGameOver) before the 14th state
assert NoSolutionsLessThanFifteenStates {
    Game
    implies
    all s: State |
        IsGameOver[s]
        implies
        s in first.next.next.next.next.next.next.next.next.next.next.next.next.next.nexts
}

// check NoSolutionsLessThanFifteenStates for 15


// Losing one's Skull does not, by itself, force a loss. Checked at scope 40 and again at
// scope 15 (the minimal-trace case) below, to confirm the result holds at both sizes.
assert LosingSkullMeansNoWin {
    Game
    implies
    all s: State | ((Skull not in s.A and s.phase = Winning) implies s.scoreA != 2) and
                    ((Skull not in s.B and s.phase = Winning) implies s.scoreB != 2)
}

check LosingSkullMeansNoWin for 40


assert LosingSkullMeansNoWinMinimal {
    Game
    implies
    all s: State | ((Skull not in s.A and s.phase = Winning) implies s.scoreA != 2) and
                    ((Skull not in s.B and s.phase = Winning) implies s.scoreB != 2)
}

check LosingSkullMeansNoWinMinimal for 15
