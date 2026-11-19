------------------ MODULE proof_library --------------------
\* proof_library.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS raft

THEOREM QuorumsIntersect ==
    ASSUME NEW Q1 \in Quorum, NEW Q2 \in Quorum
    PROVE  Q1 \cap Q2 # {}
<1>1. /\ Q1 \subseteq Server
       /\ Q2 \subseteq Server
    BY DEF Quorum
<1>2. /\ Cardinality(Q1) * 2 > Cardinality(Server)
       /\ Cardinality(Q2) * 2 > Cardinality(Server)
    BY DEF Quorum
<1>3. Cardinality(Q1) + Cardinality(Q2) > Cardinality(Server)
    BY <1>1, <1>2, FS_Subset, FS_CardinalityType, ServerOK
<1> QED BY <1>1, <1>3, FS_MajoritiesIntersect, ServerOK

THEOREM QuorumSuperset ==
    \A smaller \in Quorum, larger \in SUBSET Server:
        smaller \subseteq larger => larger \in Quorum
<1> SUFFICES ASSUME NEW smaller \in Quorum,
                      NEW larger \in SUBSET Server, smaller \subseteq larger
             PROVE larger \in Quorum
    OBVIOUS
<1>1. /\ smaller \subseteq Server
       /\ Cardinality(smaller) * 2 > Cardinality(Server)
    BY SMT DEF Quorum
<1>2. /\ IsFiniteSet(larger)
       /\ Cardinality(smaller) <= Cardinality(larger)
    BY <1>1, ServerOK, FS_Subset, SMT
<1>3. /\ Cardinality(smaller) \in Nat
       /\ Cardinality(larger) \in Nat
       /\ Cardinality(Server) \in Nat
    BY <1>1, <1>2, ServerOK, FS_Subset, FS_CardinalityType, SMT
<1> QED BY <1>1, <1>2, <1>3, SMT DEF Quorum

THEOREM BoundedNatSetHasMaximum ==
    \A n \in Nat:
    \A S \in SUBSET (0..n):
        S # {} => \E maximum \in S: \A value \in S: maximum >= value
<1> DEFINE P(n) ==
        \A S \in SUBSET (0..n):
            S # {} => \E maximum \in S: \A value \in S: maximum >= value
<1>1. P(0) BY DEF P
<1>2. \A n \in Nat: P(n) => P(n + 1)
    <2>1. ASSUME NEW n \in Nat, P(n),
                 NEW S \in SUBSET (0..(n + 1)), S # {}
          PROVE  \E maximum \in S: \A value \in S: maximum >= value
        <3>in. CASE n + 1 \in S
            <4>1. \A value \in S: n + 1 >= value
                BY <3>in
            <4> QED BY <3>in, <4>1
        <3>out. CASE n + 1 \notin S
            <4> USE n + 1 \notin S
            <4>1. S \in SUBSET (0..n)
                BY <3>out
            <4> QED BY <3>out, <4>1, <2>1 DEF P
        <3> QED BY <3>in, <3>out
    <2> QED BY <2>1 DEF P
<1>3. \A n \in Nat: P(n)
    BY <1>1, <1>2, NatInduction, Isa
<1> QED BY <1>3 DEF P

THEOREM MaxOfBoundedNatSet ==
    ASSUME NEW n \in Nat, NEW S \in SUBSET (0..n), S # {}
    PROVE  /\ Max(S) \in S
           /\ Max(S) \in Nat
    BY BoundedNatSetHasMaximum DEF Max

THEOREM MaxOrZeroSubset ==
    \A bound \in Nat:
    \A smaller, larger \in SUBSET (0..bound):
        smaller \subseteq larger =>
            MaxOrZero(smaller) <= MaxOrZero(larger)
<1> SUFFICES ASSUME NEW bound \in Nat,
                      NEW smaller \in SUBSET (0..bound),
                      NEW larger \in SUBSET (0..bound),
                      smaller \subseteq larger
             PROVE  MaxOrZero(smaller) <= MaxOrZero(larger)
    OBVIOUS
<1>empty. CASE smaller = {}
    <2> USE smaller = {}
    <2>larger_empty. CASE larger = {}
        <3> USE larger = {}
        <3> QED BY DEF MaxOrZero
    <2>larger_nonempty. CASE larger # {}
        <3> USE larger # {}
        <3>1. Max(larger) \in Nat
            BY MaxOfBoundedNatSet
        <3> QED BY <3>1 DEF MaxOrZero
    <2> QED BY <2>larger_empty, <2>larger_nonempty
<1>nonempty. CASE smaller # {}
    <2> USE smaller # {}
    <2>1. larger # {} OBVIOUS
    <2>2. /\ Max(smaller) \in smaller
           /\ Max(larger) \in larger
        BY <2>1, MaxOfBoundedNatSet
    <2>3. Max(smaller) <= Max(larger)
        BY <2>2, BoundedNatSetHasMaximum DEF Max
    <2> QED BY <2>1, <2>3 DEF MaxOrZero
<1> QED BY <1>empty, <1>nonempty

THEOREM NatLeqTransitive ==
    \A x, y, z \in Nat: x <= y /\ y <= z => x <= z
    BY SMT

THEOREM NatLtLeqPlusOne ==
    \A x, y, z \in Nat: x < y /\ y <= z => x + 1 <= z
    BY SMT

THEOREM MaxUpperBound ==
    \A x, y, upper \in Nat:
        x <= upper /\ y <= upper => Max({x, y}) <= upper
    BY DEF Max

THEOREM MinTypeOK ==
    \A x, y \in Nat:
        /\ Min({x, y}) \in Nat
        /\ Min({x, y}) <= x
        /\ Min({x, y}) <= y
<1>1. \A x, y \in Nat:
        \E minimum \in {x, y}: \A value \in {x, y}: minimum <= value
    OBVIOUS
<1> QED BY <1>1 DEF Min

THEOREM MaxTypeOK ==
    \A x, y \in Nat:
        /\ Max({x, y}) \in Nat
        /\ Max({x, y}) >= x
        /\ Max({x, y}) >= y
<1>1. \A x, y \in Nat:
        \E maximum \in {x, y}: \A value \in {x, y}: maximum >= value
    OBVIOUS
<1> QED BY <1>1 DEF Max


=======================================================================
