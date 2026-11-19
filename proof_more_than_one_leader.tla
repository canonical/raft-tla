----------------- MODULE proof_more_than_one_leader -----------------
\* proof_more_than_one_leader.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS proof_inductiveinvariant

LEMMA VoteForUnique ==
    ASSUME VoteRecordInv,
           NEW voter \in Server,
           NEW left \in Server,
           NEW right \in Server,
           NEW term \in Nat,
           Started(left, term),
           Started(right, term),
           VoteFor(voter, left, term),
           VoteFor(voter, right, term)
    PROVE left = right
    BY SMT DEF VoteRecordInv, VoteUniqueInv, StartedGrantInv, VoteFor

LEMMA InductiveInvariantImpliesMoreThanOneLeader ==
    InductiveInvariant => MoreThanOneLeaderInv
<1> SUFFICES ASSUME InductiveInvariant,
                      NEW left \in Server, NEW right \in Server,
                      currentTerm[left] = currentTerm[right],
                      state[left] = Leader, state[right] = Leader
             PROVE  left = right
    BY DEF MoreThanOneLeaderInv
<1>1. PICK leftQuorum \in Quorum:
        leftQuorum \subseteq votesGranted[left]
    BY DEF InductiveInvariant, LeaderQuorumInv
<1>2. PICK rightQuorum \in Quorum:
        rightQuorum \subseteq votesGranted[right]
    BY DEF InductiveInvariant, LeaderQuorumInv
<1>3. PICK voter : voter \in leftQuorum \cap rightQuorum
    BY QuorumsIntersect
<1>4. /\ voter \in Server
       /\ voter \in votesGranted[left]
       /\ voter \in votesGranted[right]
    BY <1>1, <1>2, <1>3 DEF Quorum
<1>5. /\ Started(left, currentTerm[left])
       /\ Started(right, currentTerm[left])
       /\ VoteFor(voter, left, currentTerm[left])
       /\ VoteFor(voter, right, currentTerm[left])
    BY <1>4 DEF InductiveInvariant, ActiveVotesInv
<1>6. /\ VoteRecordInv
       /\ currentTerm[left] \in Nat
    BY DEF InductiveInvariant, TypeOK, ServerVarsTypeOK
<1> QED BY <1>4, <1>5, <1>6, VoteForUnique

---------------------------------------------------------------------

THEOREM MoreThanOneLeaderInvariant ==
    Spec => []MoreThanOneLeaderInv
    BY InductiveInvariantInvariant,
        InductiveInvariantImpliesMoreThanOneLeader, PTL

=====================================================================
