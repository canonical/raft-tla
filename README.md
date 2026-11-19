# Dqlite's TLA+ Raft spec and proof

TLA+ specification of the Raft consensus algorithm based on Ongaro's original
spec. The spec describes Raft with message passing and atomic actions which
only read each replica's state.

The repository contains a full safety proof for Raft plus some other interesting
proven results.

## Contents

- `raft.tla`: the spec itself and safety invariants.
- `proof_library.tla` and `proof_inductiveinvariant.tla`: shared lemmas and
  the inductive invariant underlying the safety proofs.
- The remaining `proof_*.tla` modules cover election safety, leader uniqueness,
  log matching, term ordering, commit indices, quorum agreement, committed
  log consistency, and leader completeness.

## Disclaimer on AI

The proofs here are the result of a multi-month human effort. AI was extremely
helpful in writing most proofs and finding counter-examples when the theorem
statements were wrong. However, AI could not prove the results autonomously, it
required significant guidance from us both for the proof strategy and steering
it in the proof itself when it got stuck. Moreover, some of the auxiliary proofs
were written almost completely by hand as AI could only fill the gaps but got
confused on the high-level ideas.

## More information

We will write a detailed report that describes the proof strategy, how we used
AI effectively, and most importantly, how we made sure our spec is faithful to
Ongaro's description of the algorithm. Stay tuned!

## License

© 2026 by Canonical Ltd. is licensed under CC BY-NC-SA 4.0.

Incorporated material from Diego Ongaro's Raft specification and the etcd
specification retains its original CC BY 4.0 and Apache 2.0 licenses,
respectively. See the header of [raft.tla](raft.tla) for attribution.
