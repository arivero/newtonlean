# Verification provenance

The primary evidence for a parametric theorem is successful Lean 4.19.0
elaboration and kernel checking, with its actual premises and axiom report.
An arithmetic example cannot certify a general statement or its historical
interpretation. All current results remain modern finite reconstructions.

The numeric pins disclosed before implementation (including the harmonic
one-block/two-block errors, the small-time boundary example and planned cover
radius/area) are production-side controls. Their exact arithmetic and false
variants check the intended definitions; they are not disjoint reference
oracles for the theorem that used them. Source interpretation is checked
separately against the stage-local passages and classifications.

Next holdout protocol, fixed before comparison: after the cover implementation
is complete and committed, a sequential verification worker chooses an unused
input, derives exact coordinates by standalone common-denominator integer
arithmetic, and records generator/version, inputs, exact outputs, date and
file hash before comparing with the project. The reference must import only
Std and must not call project recurrence, norm, determinant or cover code.
No expected holdout values are supplied to the implementation worker.

Failure means any exact cross-multiplied inequality/equality mismatch, an
unexpected compiler failure, or acceptance of the deliberately corrupted
comparison. There is no floating-point tolerance or digit claim. The project
snapshot remains fixed during this check; if reference data influences a
repair, its contact is recorded and it cannot certify that repair.

The deepest shared layers are integer arithmetic and the Lean logical kernel.
The distinct calculation checks project formulas, sample indexing, signs and
normalization; it does not independently check Lean itself or supply geometric
content/trajectory existence. The comparison's birth/contact record must be
linked here before it is described as a disjoint arithmetic check.

On 4 October a sequential nonauthor Luna worker checked frozen `15d50ad`.
The first two reference records were burned for harness indexing/copied-input
errors; neither certifies the result. The third fresh input passed every
exact coordinate/error/radius/budget comparison; its altered-radius control
failed specifically as a false equality. The successful generator, logs,
comparator and birth/contact/hash record are preserved unchanged in the
[runnable holdout artifact](verification/harmonic-cover-2026-10-04/README.md).
No reference-derived repair occurred. Shared update specification,
integer/kernel layers and the use of the proposed radius formula are disclosed
there. The check certifies neither the geometric proof nor a trajectory.
