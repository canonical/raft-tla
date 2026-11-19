--------------------- MODULE proof_electionsafety ----------------------
\* proof_electionsafety.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_inductiveinvariant

LEMMA WonUnique ==
    VoteRecordInv =>
        \A candidate1 \in Server, candidate2 \in Server, term \in Nat:
            /\ Won(candidate1, term)
            /\ Won(candidate2, term)
            => candidate1 = candidate2
<1> USE DEF Won
<1> SUFFICES ASSUME VoteRecordInv,
                      NEW candidate1 \in Server, NEW candidate2 \in Server,
                      NEW term \in Nat,
                      Won(candidate1, term), Won(candidate2, term)
             PROVE  candidate1 = candidate2
    OBVIOUS
<1>1. \E Q1 \in Quorum:
        \A voter \in Q1: VoteFor(voter, candidate1, term)
    OBVIOUS
<1> PICK Q1 \in Quorum:
        \A voter \in Q1: VoteFor(voter, candidate1, term) BY <1>1
<1>2. \E Q2 \in Quorum:
        \A voter \in Q2: VoteFor(voter, candidate2, term)
    OBVIOUS
<1> PICK Q2 \in Quorum:
        \A voter \in Q2: VoteFor(voter, candidate2, term) BY <1>2
<1>3. Q1 \cap Q2 # {} BY QuorumsIntersect
<1> PICK voter \in Q1 \cap Q2: TRUE BY <1>3
<1>4. /\ voter \in Server
       /\ VoteFor(voter, candidate1, term)
       /\ VoteFor(voter, candidate2, term)
    BY DEF Quorum
<1>5. /\ Started(candidate1, term)
       /\ Started(candidate2, term)
    OBVIOUS
<1> QED BY <1>4, <1>5
    DEF VoteFor, VoteRecordInv, VoteUniqueInv, StartedGrantInv

LEMMA ActiveVotesInvUnchanged ==
    /\ ActiveVotesInv
    /\ UNCHANGED <<messages, currentTerm, state, votesGranted>>
    => ActiveVotesInv'
    BY DEF ActiveVotesInv, Started, VoteFor, Grant

LEMMA InductiveInvariantImpliesElectionSafety ==
    InductiveInvariant => ElectionSafetyInv
<1> SUFFICES ASSUME InductiveInvariant, NEW i \in Server,
                      state[i] = Leader, NEW j \in Server
             PROVE
                MaxOrZero({n \in DOMAIN log[i]:
                    log[i][n].term = currentTerm[i]}) >=
                MaxOrZero({n \in DOMAIN log[j]:
                    log[j][n].term = currentTerm[i]})
    BY Zenon DEF ElectionSafetyInv
<1> DEFINE leaderIndexes ==
        {n \in DOMAIN log[i]: log[i][n].term = currentTerm[i]}
<1> DEFINE otherIndexes ==
        {n \in DOMAIN log[j]: log[j][n].term = currentTerm[i]}
<1>1. /\ currentTerm[i] \in Nat
       /\ log[i] \in Seq(LogEntry)
       /\ log[j] \in Seq(LogEntry)
       /\ Len(log[i]) \in Nat
    BY LenProperties
    DEF InductiveInvariant, TypeOK,
        ServerVarsTypeOK, LogVarsTypeOK
<1>2. Won(i, currentTerm[i]) BY ActiveLeaderWon
<1>3. otherIndexes \subseteq leaderIndexes
    <2> SUFFICES ASSUME NEW index \in otherIndexes
                PROVE  index \in leaderIndexes
        OBVIOUS
    <2>1. /\ index \in DOMAIN log[j]
          /\ log[j][index].term = currentTerm[i]
        OBVIOUS
    <2>2. /\ index \in Nat
          /\ log[j][index].term \in Nat
        BY <1>1, <2>1, ElementOfSeq, LenProperties DEF LogEntry
    <2>3. \E owner \in Server:
            TermOwner(owner, currentTerm[i], index)
        BY <2>1 DEF InductiveInvariant, LogElectionInv, TermOwner
    <2> PICK owner \in Server:
            TermOwner(owner, currentTerm[i], index) BY <2>3
    <2>4. Won(owner, currentTerm[i]) BY DEF TermOwner
    <2>5. owner = i
        BY <1>1, <1>2, <2>4, WonUnique
        DEF InductiveInvariant
    <2>6. LogHasTermAt(i, currentTerm[i], index)
        BY <2>5 DEF TermOwner, OwnerActive
    <2> QED BY <2>6 DEF leaderIndexes, LogHasTermAt
<1>4. /\ leaderIndexes \in SUBSET (0..Len(log[i]))
       /\ otherIndexes \in SUBSET (0..Len(log[i]))
    BY <1>1, <1>3, LenProperties
<1> QED BY <1>1, <1>3, <1>4, MaxOrZeroSubset

------------------------------------------------------------------------

THEOREM Spec => []ElectionSafetyInv
    BY InductiveInvariantInvariant, InductiveInvariantImpliesElectionSafety, PTL

========================================================================
