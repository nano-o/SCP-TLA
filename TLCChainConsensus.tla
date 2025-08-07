------------- MODULE TLCChainConsensus -------------

EXTENDS ChainConsensus

CONSTANT MaxSeqLen, b1, b2, b3

BlockMC == {b1, b2, b3}
ChainMC ==
    {<<>>} \cup UNION {[1..n -> Block] : n \in 1..MaxSeqLen }
AppendMC(c, b) == LET c2 == c \o <<b>> IN
    IF c2 \in Chain THEN c2 ELSE c
InitDBMC == <<>>
ApplyMC(db, b) ==
    LET db2 == Append(db, b)
    IN  IF b = b2
        THEN FAILED \* let's say b2 is invalid
        ELSE
            IF Len(db2) <= MaxSeqLen
            THEN db2
            ELSE db

Falsy1 == \neg (
    \E c1, c2 \in proposedChains : \neg Compatible(c1, c2)
)

Falsy2 == \neg (
    \E c1 \in proposedChains : \E c2 \in {externalizeInterface[n] : n \in N} :
        \neg Compatible(c1 ,c2)
)

====================================================

