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
    val testVs = Set("v1", "v2") // we have two validators
    import Nomination(
        Vs = testVs,
        TxSets = Set("txset1", "txset2"),
        HashFn = {(x) => x}, // our hash function is just the identity function
        Combine = {ss => ss.chooseSome()},
        Quorums = {v => Set(testVs)}, // we have just one quorum consisting of both validators
        Blocking = {v => testVs.powerset().filter(x => x.size() == 1)}
    ).* // .* means we import everything as is

    // stateAsRecord is useful to print the whole state in the Quint REPL:
    val stateAsRecord = {votedNominated: votedNominated, acceptedNominated: acceptedNominated, round: round, candidates: candidates, preImages: preImages, leader: leader}

    // An example run:
    run run1 = {
        Init.then(StartRound("v1", 1, "v1")) // v1 starts round 1 and elects itself as leader and votes for a txset
            .then(StartRound("v2", 1, "v1")) // v2 starts round 1 and elects v1 as leader for round 1
            .then(Vote("v2"))// here v2 votes for the txset voted for by v1
            .then(
                nondet txs = VotedHashes.oneOf()
                AcceptCase1("v1", txs, Vs) // v1 accepts `txs` because {v1,v2} voted for it
                .then(GetTxSet("v2", txs)) // v2 dowloads the txset
                .then(AcceptCase2("v2", txs, Set("v1"))) // v2 accepts `txs` because v1 did and is a blocking set
                .then(Confirm("v2", txs, Vs))) // v2 confirms `txs` as nominated
    }
}
