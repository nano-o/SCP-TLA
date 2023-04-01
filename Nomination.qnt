// -*- mode: Bluespec; -*-
// the above is for syntax highlighting on github

module Nomination {
    type V = str // validators
    type TxSet = str // transaction sets
    type Hash = str // hashes

    const Vs: Set[V] // the validators
    const TxSets: Set[TxSet] // the possible txsets we consider
    const HashFn: TxSet => Hash
    def Hashes: Set[Hash] = TxSets.map(x => HashFn(x))
    const Combine: Set[TxSet] => TxSet
    const Quorums: V => Set[Set[V]] // set of quorums of a validator
    const Blocking: V => Set[Set[V]] // set of blocking sets of a validator

    // state
    var votedNominated: V -> Set[TxSet]
    var acceptedNominated: V -> Set[TxSet]
    var round: V -> int
    var candidates: V -> Set[TxSet]
    var preImages: V -> Hash -> TxSet
    var leader: V -> V

    action Init = all {
        votedNominated' = Vs.mapBy(v => Set()),
        acceptedNominated' = Vs.mapBy(v => Set()),
        round' = Vs.mapBy(v => 0),
        candidates' = Vs.mapBy(v => Set()),
        preImages' = Vs.mapBy(v => Map()),
        leader' = Vs.mapBy(v => v)
    }

    // validator v enters its next round:
    action StartRound(v, r, l) = all {
        r == round.get(v)+1,
        round' = round.set(v, r), // increment v's round
        leader' = leader.set(v, l), // remember the leader v picked
        if (l == v) { // if v picked itself as the leader
            nondet txset = TxSets.oneOf() // pick a txset to nominate
            val h = HashFn(txset) // the hash ot the txset
            val newPimgs =  // the new set of preimages that v knows
                    if (preImages.keys().contains(h)) { preImages.get(v).set(h, txset) }
                    else { preImages.get(v).put(h, txset) }
            all {
                preImages' = preImages.set(v, newPimgs), // update known preimages of v
                votedNominated' = votedNominated.set(v, votedNominated.get(v).union(Set(h))) // vote
            }
        }
        else all {
            preImages' = preImages,
            votedNominated' = votedNominated
        },
        acceptedNominated' = acceptedNominated,
        candidates' = candidates
    }

    // NOTE: we vote for a hash even if we do not have the preimage
    action Vote(v) = {
        val l = leader.get(v)
        val hs = votedNominated.get(l)
        all {
            candidates.get(v) == Set(), // we only vote if we do not have a confirmed candidate yet
            // we vote for all txsets that the leader voted for:
            votedNominated' = votedNominated.set(v, votedNominated.get(v).union(hs)),
            // other variables unchanged:
            acceptedNominated' = acceptedNominated,
            round' = round,
            candidates' = candidates,
            preImages' = preImages,
            leader' = leader
        }
    }

    def VotedHashes =
        Vs.map(v => votedNominated.get(v))
          .fold(Set(), (x, y) => x.union(y))

    action GetTxSet(v, txset) = {
        val h = HashFn(txset)
        all {
            not(preImages.get(v).keys().contains(h)), // v does not have the preimage already
            VotedHashes.contains(h), // this txset has been voted for by someone
            // v records that it has the preimage of h:
            preImages' = preImages.set(v, preImages.get(v).put(h, txset)),
            // other variables unchanged:
            votedNominated' = votedNominated,
            acceptedNominated' = acceptedNominated,
            round' = round,
            candidates' = candidates,
            leader' = leader
        }
    }

    action AcceptCase1(v, h, q) = all {
        Quorums(v).contains(q),
        preImages.get(v).keys().contains(h), // v has the pre-image of h
        q.forall(w =>
            or {
                votedNominated.get(w).contains(h),
                acceptedNominated.get(w).contains(h)
            }), // all members of Q have voted to nominate h or accepted h
        acceptedNominated' = acceptedNominated.set(v, acceptedNominated.get(v).union(Set(h))),
        // other variables unchanged:
        votedNominated' = votedNominated,
        round' = round,
        candidates' = candidates,
        preImages' = preImages,
        leader' = leader
    }

    action AcceptCase2(v, h, B) = all {
        preImages.get(v).keys().contains(h), // v has the pre-image of h
        B.forall(w => acceptedNominated.get(w).contains(h)), // all members of B have accepted to nominate h
        acceptedNominated' = acceptedNominated.set(v, acceptedNominated.get(v).union(Set(h))),
        // other variables unchanged:
        votedNominated' = votedNominated,
        round' = round,
        candidates' = candidates,
        preImages' = preImages,
        leader' = leader
    }

    action Confirm(v, h, Q) = all {
        VotedHashes != Set(),
        all {
            preImages.get(v).keys().contains(h), // v has the pre-image of h
            Q.forall(w => acceptedNominated.get(w).contains(h)), // all members of Q have accepted to nominate h
            // add h to the confirmed candidates:
            candidates' = candidates.set(v, candidates.get(v).union(Set(h))),
            // other variables unchanged:
            votedNominated' = votedNominated,
            acceptedNominated' = acceptedNominated,
            leader' = leader,
            round' = round,
            preImages' = preImages
        }
    }

    action Step = {
        nondet v = Vs.oneOf()
        nondet l = Vs.oneOf()
        nondet r = Nat.oneOf()
        nondet h = Hashes.oneOf()
        nondet txset = TxSets.oneOf()
        nondet q = Quorums(v).oneOf()
        nondet b = Blocking(v).oneOf()
        any {
            StartRound(v,r,l),
            GetTxSet(v, txset),
            Vote(v),
            AcceptCase1(v, h, q),
            AcceptCase2(v, h, b),
            Confirm(v, h, q)
        }
    }
}

module Test {
    import Nomination(
        Vs = Set("v1", "v2"),
        TxSets = Set("txset1", "txset2"),
        HashFn = {(x) => x},
        Combine = {ss => ss.chooseSome()},
        Quorums = {v => Set(Nomination::Vs)},
        Blocking = {v => Nomination::Vs.powerset().filter(x => x.size() == 1)})
    as Nomination

    def noCandidate: bool = { // TODO: val or def?
        Nomination::Vs.forall(v => Nomination::candidates.get(v) == Set())
    }

    // seems like we have to redefine everything in this module.
    action Init = Nomination::Init
    action StartRound = Nomination::StartRound
    action Vote = Nomination::Vote
    action GetTxSet = Nomination::GetTxSet
    action AcceptCase1 = Nomination::AcceptCase1
    action AcceptCase2 = Nomination::AcceptCase2
    action Confirm = Nomination::Confirm
    action Step = Nomination::Step
    val state = {votedNominated: Nomination::votedNominated, acceptedNominated: Nomination::acceptedNominated, round: Nomination::round, candidates: Nomination::candidates, preImages: Nomination::preImages, leader: Nomination::leader}
    val VotedHashes = Nomination::VotedHashes

    run run1 = {
        Init.then(StartRound("v1", 1, "v1"))
            .then(StartRound("v2", 1, "v1"))
            .then(Vote("v2"))
            .then(AcceptCase1("v1", VotedHashes.oneOf(), Nomination::Vs))
            .then(GetTxSet("v2", VotedHashes.oneOf()))
            .then(AcceptCase2("v2", VotedHashes.oneOf(), Set("v1")))
            .then(Confirm("v2", VotedHashes.oneOf(), Nomination::Vs))
    }
}
