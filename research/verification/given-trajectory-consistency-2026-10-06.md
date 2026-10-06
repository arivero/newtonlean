# Given-motion local consistency, 6 October 2026

This increment proves a conditional swept-fan law for an independently supplied
state curve. It does not certify the full historical Proposition I.

`TimeCalibration.run_sample_distance_le_source` compares Newton's actual
finite run with arbitrary rational candidate states sharing its initial
state. If each candidate step differs from the corresponding drift/kick by
at most D, and the two sampled forces differ by at most L times the arrival
distance plus E, the distance satisfies the already shared finite recurrence
with source `tau*abs(h)*E + D`. The calibrated short-window bound then gives
`2*n*(tau*abs(h)*E + D)`. Conversion to ordinary state distance multiplies
this by `1 + 1/tau`.

`GivenMotionComparison` specializes that estimate to the retained general
regional oracle. Actual polygon arrivals are proved to lie in the oracle
region using the existing confinement theorem. Only candidate drift-arrival
membership is supplied. No whole-plane or actual-run membership trace is
assumed. One full-grid budget controls every prefix, including both endpoints.

`GivenTrajectoryArea.Consistency` keeps the additional premises visible:

- The supplied curve has its own rational state samples, converging pointwise
  in each binary time address; this is representation of that curve, not
  convergence of Newton's polygon to it.
- Samples share the given initial state, have candidate arrivals in the
  force region, and satisfy the local residual bound.
- The scalar full-grid source budget tends to zero. In particular the
  residual per step must shrink faster than the reciprocal cell count.
  This is a local consistency rate, not a supplied motion-distance bound.

Finite stability and the two limits prove `equals_constructed`. The existing
constructed-curve theorem then proves `proportional_swept_area`: actual
unsigned fans of the supplied curve converge on every interval to
`abs(momentum(initial))*abs(elapsed)/2`. Neither this area law nor agreement
with the constructed curve is a premise. The supplied state curve also
provides velocity data; bare existence of a position curve is insufficient.

Separately, `between_path_content_tends_zero` constructs covers of the actual
matched region between the polygon and the supplied curve and proves that
their canonical outer contents tend to zero. It reuses the existing all-cover
quantity; it does not subtract two sector areas or introduce a new completion.

## Historical boundary and next obligation

These are modern reconstruction results. No new historical dependency edge
or stage wrapper is added. The separate De Motu, 1687 and 1713 source routes
in [the proof ledger](../PROP_I_REALIZATION.md#proof-dependencies-and-the-implementation-route)
remain unchanged. Taking existence as given does not establish the consistency
premises. Derive those from independently stated motion laws and regularity
next. Ordinary geometric sector-union area, Newton's invoked ultimate-area
passage and unrestricted intervals remain open. Force-specific work remains
held; historical completion scores are unchanged.

The source budget is stated as explicit rational arithmetic so its meaning
can be checked without interpreting a new abstract convergence interface.
Only the reusable generic recurrence, its finite bound and their client are
added; an unused regional wrapper was removed before verification.

## Verification

See the adjacent Lean harness for the equal-time consequence on arbitrary
supplied data and a control retaining a positive local residual even when
the oracle discrepancy is zero. All new theorem axioms are printed there.
Full checklist and API results are recorded after verification below.

All 16 README checklist commands passed, including `lake build`,
`lake build BarrowLib`, `lake build NewtonLimitDynamics`, generated catalogues,
source graph, edition comparison, rendered graphs, progress artifacts,
`CheckReferences.lean`, declaration/evidence/rendering tests, archived source
hashes and `git diff --check`. The adjacent scope harness passed separately.
All six new theorem axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`; no project axiom, sorry, admit or mathlib was added.

API inventory against `8c9ad34`: 2,244 prior public names preserved with no
statement changes; nine additions give 2,253 names and 1,735 theorem rows.
The source graph remains 88 nodes, 87 edges and 253 passages; 1,590 reference
checks were emitted. Inventory counts are not a proof-completion percentage.
Logs: `/tmp/newton-sol61-given-final-01.log` through `-16.log`,
`/tmp/newton-sol61-given-scope.log`, `/tmp/newton-sol61-given-api.json`.
The implementation worker reached its usage limit; the root completed the
regional client, curve theorems, integration and all verification. These checks
are not represented as an independent subagent review.
