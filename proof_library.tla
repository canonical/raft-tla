------------------------------ MODULE proof_library ------------------------------
\* proof_library.tla © 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

EXTENDS raft

\* Reusable facts about arithmetic, finite sets, and sequences. Use only Raft operators
\* that do not depend on its constants or state.

LEMMA NatLeqTransitive ==
    \A x, y, z \in Nat: x <= y /\ y <= z => x <= z
    BY SMT

LEMMA FiniteNaturalSetHasMaximum ==
    ASSUME NEW indexes \in SUBSET Nat, IsFiniteSet(indexes), indexes # {}
    PROVE \E maximum \in indexes: \A index \in indexes: index <= maximum
<1> DEFINE P(subset) ==
        subset = {} \/ \E maximum \in subset: \A index \in subset: index <= maximum
<1>base. P({}) BY SMT DEF P
<1>step.
    ASSUME NEW subset \in SUBSET indexes, IsFiniteSet(subset), P(subset), NEW value \in indexes \ subset
    PROVE P(subset \cup {value})
    <2> USE IsFiniteSet(subset), P(subset)
    <2>empty. CASE subset = {}
        BY <2>empty, SMT DEF P
    <2>nonempty. CASE subset # {}
        <3>old. PICK maximum \in subset: \A index \in subset: index <= maximum
            BY <2>nonempty, SMT DEF P
        <3>types. maximum \in Nat /\ value \in Nat
            BY <3>old, SMT
        <3>smaller. CASE value <= maximum
            BY <3>old, <3>types, <3>smaller, SMT DEF P
        <3>larger. CASE maximum <= value
            BY <3>old, <3>types, <3>larger, SMT DEF P
        <3> QED BY <3>types, <3>smaller, <3>larger, SMT
    <2> QED BY <2>empty, <2>nonempty, SMT
<1> HIDE DEF P
<1>all. P(indexes)
    BY <1>base, <1>step, FS_Induction, IsaM("blast")
<1> QED BY <1>all, SMT DEF P

LEMMA BoundedIndexMaxProperties ==
    ASSUME NEW bound \in Nat, NEW indexes \in SUBSET (0..bound),
           indexes # {}
    PROVE /\ Max(indexes) \in indexes
          /\ \A index \in indexes: index <= Max(indexes)
<1>finite. IsFiniteSet(indexes) /\ indexes \subseteq Nat
    BY FS_Interval, FS_Subset, SMT
<1> QED BY <1>finite, FiniteNaturalSetHasMaximum, SMT DEF Max

LEMMA PositiveIndexMaxOrZeroProperties ==
    ASSUME NEW bound \in Nat, NEW indexes \in SUBSET (1..bound)
    PROVE /\ MaxOrZero(indexes) \in 0..bound
          /\ (MaxOrZero(indexes) = 0 <=> indexes = {})
          /\ (indexes # {} => MaxOrZero(indexes) \in indexes)
          /\ \A index \in indexes: index <= MaxOrZero(indexes)
<1>empty. CASE indexes = {}
    BY <1>empty, SMT DEF MaxOrZero
<1>nonempty. CASE indexes # {}
    <2>subset. indexes \subseteq 0..bound BY SMT
    <2>maximum.
            /\ Max(indexes) \in indexes
            /\ \A index \in indexes: index <= Max(indexes)
        BY <1>nonempty, <2>subset, BoundedIndexMaxProperties, SMT
    <2> QED BY <1>nonempty, <2>maximum, SMT DEF MaxOrZero
<1> QED BY <1>empty, <1>nonempty, SMT

LEMMA PositiveIndexMaxOrZeroSubsetMonotone ==
    ASSUME NEW bound \in Nat, NEW smaller \in SUBSET (1..bound),
           NEW larger \in SUBSET (1..bound), smaller \subseteq larger
    PROVE MaxOrZero(smaller) <= MaxOrZero(larger)
<1>maxima.
        /\ MaxOrZero(larger) \in 0..bound
        /\ (smaller # {} => MaxOrZero(smaller) \in smaller)
        /\ \A index \in larger: index <= MaxOrZero(larger)
    BY PositiveIndexMaxOrZeroProperties, SMT
<1> QED BY <1>maxima, SMT DEF MaxOrZero

LEMMA MaxOrZeroAddingLastIndex ==
    ASSUME NEW bound \in Nat, NEW indexes \in SUBSET (1..bound)
    PROVE MaxOrZero(indexes \cup {bound + 1}) = bound + 1
<1>maximum.
        /\ bound + 1 \in indexes \cup {bound + 1}
        /\ \A index \in indexes \cup {bound + 1}: index <= bound + 1
    BY SMT
<1> QED BY <1>maximum, SMT DEF MaxOrZero, Max


LEMMA MinTypeOK ==
    \A x, y \in Nat:
        /\ Min({x, y}) \in Nat
        /\ Min({x, y}) <= x
        /\ Min({x, y}) <= y
<1>1. \A x, y \in Nat:
        \E minimum \in {x, y}: \A value \in {x, y}: minimum <= value
    OBVIOUS
<1> QED BY <1>1 DEF Min

LEMMA MinOrderedPair ==
    \A smaller, larger \in Nat:
        smaller <= larger => Min({larger, smaller}) = smaller
    BY SMT DEF Min

LEMMA MaxTypeOK ==
    \A x, y \in Nat:
        /\ Max({x, y}) \in Nat
        /\ Max({x, y}) >= x
        /\ Max({x, y}) >= y
<1> SUFFICES ASSUME NEW x \in Nat, NEW y \in Nat
             PROVE /\ Max({x, y}) \in Nat
                   /\ Max({x, y}) >= x
                   /\ Max({x, y}) >= y
    BY SMT
<1>bound. {x, y} \subseteq 0..(x + y) /\ x + y \in Nat
    BY SMT
<1> QED BY <1>bound, BoundedIndexMaxProperties, SMT

LEMMA MaxUpperBound ==
    \A x, y, upper \in Nat:
        x <= upper /\ y <= upper => Max({x, y}) <= upper
    BY BoundedIndexMaxProperties, SMT

LEMMA FiniteSetSubsetsAreFinite ==
    ASSUME NEW CONSTANT universe, IsFiniteSet(universe)
    PROVE \A subset \in SUBSET universe: IsFiniteSet(subset)
    BY FS_Subset, SMT

LEMMA NonemptyFiniteSetIsQuorum ==
    ASSUME NEW CONSTANT members, IsFiniteSet(members), members # {}
    PROVE members \in Quorums(members)
    BY FS_EmptySet, FS_CardinalityType, SMT
    DEF Quorums

LEMMA ConfigurationQuorumProperties ==
    ASSUME NEW CONSTANT config, IsFiniteSet(config)
    PROVE \A quorum \in Quorums(config):
        /\ quorum \subseteq config
        /\ IsFiniteSet(quorum)
        /\ Cardinality(quorum) \in Nat
        /\ Cardinality(config) \in Nat
        /\ Cardinality(quorum) * 2 > Cardinality(config)
    BY FS_Subset, FS_CardinalityType, SMT DEF Quorums

LEMMA SameConfigurationQuorumsIntersect ==
    ASSUME NEW CONSTANT config, IsFiniteSet(config),
           NEW Q1 \in Quorums(config), NEW Q2 \in Quorums(config)
    PROVE Q1 \cap Q2 # {}
<1>properties.
        /\ Q1 \subseteq config /\ Q2 \subseteq config
        /\ Cardinality(Q1) \in Nat /\ Cardinality(Q2) \in Nat
        /\ Cardinality(config) \in Nat
        /\ Cardinality(Q1) * 2 > Cardinality(config)
        /\ Cardinality(Q2) * 2 > Cardinality(config)
    BY ConfigurationQuorumProperties, SMT
<1>size. Cardinality(Q1) + Cardinality(Q2) > Cardinality(config)
    BY <1>properties, SMT
<1> QED BY <1>properties, <1>size, FS_MajoritiesIntersect, SMT

LEMMA OneMemberExtensionQuorumsIntersect ==
    ASSUME NEW CONSTANT config, IsFiniteSet(config), NEW CONSTANT member,
           member \notin config, NEW Q1 \in Quorums(config),
           NEW Q2 \in Quorums(config \cup {member})
    PROVE Q1 \cap Q2 # {}
<1>extension.
        /\ IsFiniteSet(config \cup {member})
        /\ Cardinality(config \cup {member}) = Cardinality(config) + 1
    BY FS_AddElement, SMT
<1>quorums.
        /\ Q1 \subseteq config \cup {member}
        /\ Q2 \subseteq config \cup {member}
        /\ Cardinality(Q1) \in Nat
        /\ Cardinality(Q2) \in Nat
        /\ Cardinality(config) \in Nat
        /\ Cardinality(config \cup {member}) \in Nat
        /\ Cardinality(Q1) * 2 > Cardinality(config)
        /\ Cardinality(Q2) * 2 > Cardinality(config \cup {member})
    BY <1>extension, ConfigurationQuorumProperties, SMT
<1>size.
        Cardinality(Q1) + Cardinality(Q2) >
            Cardinality(config \cup {member})
    BY <1>extension, <1>quorums, SMT
<1> QED BY <1>extension, <1>quorums, <1>size, FS_MajoritiesIntersect, SMT

LEMMA WholeSequencePrefix ==
    ASSUME NEW CONSTANT elements
    PROVE \A entries \in Seq(elements): SubSeq(entries, 1, Len(entries)) = entries
    BY LenProperties, SubSeqProperties, ElementOfSeq, SeqEqual, SMT

LEMMA AppendPreservesSequencePrefix ==
    ASSUME NEW CONSTANT elements, NEW entries \in Seq(elements), NEW entry \in elements,
           NEW cut \in 0..Len(entries)
    PROVE SubSeq(Append(entries, entry), 1, cut) = SubSeq(entries, 1, cut)
<1>append.
        /\ Append(entries, entry) \in Seq(elements)
        /\ Len(Append(entries, entry)) = Len(entries) + 1
        /\ \A index \in 1..Len(entries):
                Append(entries, entry)[index] = entries[index]
    BY AppendProperties, LenProperties, SMT
<1>prefixes.
        /\ SubSeq(Append(entries, entry), 1, cut) \in Seq(elements)
        /\ SubSeq(entries, 1, cut) \in Seq(elements)
        /\ Len(SubSeq(Append(entries, entry), 1, cut)) = cut
        /\ Len(SubSeq(entries, 1, cut)) = cut
        /\ \A index \in 1..cut:
                SubSeq(Append(entries, entry), 1, cut)[index] =
                    SubSeq(entries, 1, cut)[index]
    BY <1>append, SubSeqProperties, ElementOfSeq, LenProperties, SMT
<1> QED BY <1>prefixes, SeqEqual, SMT

LEMMA PrefixesWithBoundedLength ==
    ASSUME NEW CONSTANT elements,
           NEW prefix \in Seq(elements), NEW longer \in Seq(elements),
           NEW entries \in Seq(elements), IsPrefix(prefix, entries),
           IsPrefix(longer, entries), Len(prefix) <= Len(longer)
    PROVE IsPrefix(prefix, longer)
<1>empty. CASE Len(prefix) = 0
    BY <1>empty, WholeSequencePrefix, SubSeqEmpty, LenProperties, SMT DEF IsPrefix
<1>nonempty. CASE Len(prefix) # 0
    <2>bounds.
            /\ Len(prefix) \in 1..Len(longer)
            /\ Len(longer) \in 1..Len(entries)
        BY <1>nonempty, LenProperties, SMT DEF IsPrefix
    <2>nested. SubSeq(longer, 1, Len(prefix)) = SubSeq(entries, 1, Len(prefix))
        BY <2>bounds, SubSeqOfSubSeq, SMT DEF IsPrefix
    <2> QED BY <2>nested, SMT DEF IsPrefix
<1> QED BY <1>empty, <1>nonempty, SMT

LEMMA PrefixContainsInitialSegment ==
    ASSUME NEW CONSTANT elements, NEW prefix \in Seq(elements), NEW entries \in Seq(elements),
           IsPrefix(prefix, entries), NEW cut \in 0..Len(prefix)
    PROVE SubSeq(prefix, 1, cut) = SubSeq(entries, 1, cut)
    BY SubSeqOfSubSeq, LenProperties, SMT DEF IsPrefix

LEMMA SequencePrefixTransitive ==
    ASSUME NEW CONSTANT elements, NEW prefix \in Seq(elements), NEW middle \in Seq(elements),
           NEW entries \in Seq(elements), IsPrefix(prefix, middle), IsPrefix(middle, entries)
    PROVE IsPrefix(prefix, entries)
    BY PrefixContainsInitialSegment, LenProperties, SMT DEF IsPrefix

LEMMA PrefixEntryEqual ==
    ASSUME CONSTANT elements,
            NEW prefix \in Seq(elements), NEW entries \in Seq(elements),
            IsPrefix(prefix, entries), NEW index \in 1..Len(prefix)
    PROVE /\ prefix[index] = entries[index]
          /\ SubSeq(prefix, 1, index) = SubSeq(entries, 1, index)
BY PrefixContainsInitialSegment, SMT DEF IsPrefix

LEMMA ComparablePrefixesWithOrderedLengths ==
    ASSUME NEW CONSTANT elements, NEW shorter \in Seq(elements), NEW longer \in Seq(elements),
           IsPrefix(shorter, longer) \/ IsPrefix(longer, shorter), Len(shorter) <= Len(longer)
    PROVE IsPrefix(shorter, longer)
    BY WholeSequencePrefix, LenProperties, SMT DEF IsPrefix

LEMMA PrefixOnAppend ==
    ASSUME NEW CONSTANT elements
    PROVE \A prefix, entries \in Seq(elements), entry \in elements:
        IsPrefix(prefix, entries) => IsPrefix(prefix, Append(entries, entry))
    BY AppendPreservesSequencePrefix, AppendProperties, LenProperties, SMT DEF IsPrefix

==================================================================================
