# Handoff to Claude Code

Status: the bounded task below is implemented in `Polygon/PartialCell.lean`;
see PARTITION_CONTROL.md, STATE.md and VERIFICATION.md. Superseded by
[HANDOFF-2026-09-22-NEXT.md](HANDOFF-2026-09-22-NEXT.md).

## Authority and read order

The user explicitly requests that the upgraded Claude Code receive the next
bounded research task and the opportunity to make its own commit. Codex should
finish the current inertial-defect work, validate and commit this handoff, then
stop. Claude Code is authorized to implement, verify and commit the task below.
This overrides the old handoff's prohibition on Claude; do not ask again.

Read AGENTS.md, research/STATE.md, research/TASKS.md, this handoff, then only
the relevant Lean modules. Recover live HEAD and status before editing.
The present run is labelled **first Sol 6 run** at the user's request. The
preceding inertial-control commit `71d8cf6` was also implemented with GPT-6 Sol
and checked with GPT-6 Luna; the label must not erase that provenance.

## Governing constraints

- The approved programme is stage-separated De Motu, 1687 and 1713 arguments
  corresponding to Section II I–IV. Proposed 1694 and 1726 are comparisons.
  Supporting M1–M4 remain incomplete.
- The active geometry is the defect between constructed impulsive polygons,
  followed by trajectory realization. Do not substitute swept sectors.
- Start from finite constructions, never an assumed limiting trajectory.
  No integral calculus, imported analysis or ODE theorem. Lean 4.19.0,
  core/Std only, no mathlib, downloads, sorry or project axioms.
- Label coordinate diagnostics as modern reconstructions. Keep existence,
  partition independence, geometric area and force interpretation separate.
- Preserve the unrelated deletion `conversation-continue-planck-gap-analysis.md`
  and untracked `continue-planck-gap-analysis.md`; neither stage nor restore them.
- Keep execution sequential. Do not spawn parallel workers or silently fall
  back to an older model. The user says Claude Code has been upgraded; no
  exact Claude model identifier is inferred here.

## Established starting point

- `ZeroForce.lean`: actual finite recurrence agrees with `p+t*v`, including
  unequal partitions, different denominators, rest, restart and within-cell
  drifts. Zero defect alone does not identify timing; the example uses different
  initial velocities, not fixed-data nonuniqueness.
- `InertialControl.lean`: explicit positive rational epsilon-delta radius
  controls both coordinates of `h*v`, uniformly in base position and rational
  time, with an actual-cell corollary. No all-Euclidean-time extension follows.
- `PartitionControl.lean`: for positive common denominator D and natural cell
  weights, actual end-kick motion has position `p+(T/D)*v+(A/D²)*a` and velocity
  `v+(T/D)*a`. Finite recurrences prove `2*A+Q=T²`, `Q≤M*T` when each weight
  is at most M. Against the defined polynomial candidate, the exact endpoint
  residual is `(Q/(2D²))*a`. The candidate is constructed, not assumed physical.
- `TimeSubdivision.lean`: the two-cell mismatch is `h*k*a`. An explicit
  straight connector closes comparisons with nonmatching endpoints.
- The current inertial-defect result and validation are recorded in STATE.md,
  ZERO_FORCE.md and VERIFICATION.md. Inspect their final committed versions.

## Next bounded task: constant-force positions inside cells

Extend the actual finite partition construction to a partial final cell.
Given a prefix schedule with statistics T,A,Q, append a rational drift of
duration `u/D`, with `u` a natural numerator. Use the actual prefix position
and velocity, not an independent formula assumed to describe the motion.
The position of an end-kick step at that duration is the required drift
position; the terminal kick does not alter that position.

Prove the exact residual at the new sample time:

```
candidate p v a ((T+u)/D)
  ≈ actualPartialPosition + ((Q+u*u)/(2*D*D))*a.
```

For a designated next cell of weight w, make `0≤u≤w` explicit (the first
inequality follows from Nat). If prefix weights and w are at most M, derive

```
Q + u*u ≤ M*(T+u).
```

Express the corresponding Fraction coefficient bound. Link the construction
to appending `[u]` or directly to `endKick`; derive the statistics rather than
postulating the desired residual. Include u=0, u=w and a=0 boundaries via
general theorems or concise corollaries where useful. Do not assume old
vertices survive refinement or infer existence from signed-area convergence.

Deliverable: one checked module or a scoped extension, exact actual-motion
residual and within-cell mesh bound, integrated ledger/docs and one commit.
Stop after this task and report. This is a finite position estimate, not yet
convergence or a general central-force theorem. General Euclidean-time
realization remains an explicit open obligation; no dependency expansion is
authorized merely to close it. A later task may use these estimates to prove
partition-independent convergence on rational times.

## Verification and commit

Update scripts/catalogue_formal.py when adding a module, and the root import.
Run sequentially:

```
lake build
lake build NewtonLimitDynamics
python3 scripts/catalogue_formal.py
python3 scripts/check_graph.py
lake env lean research/CheckReferences.lean
git diff --check
```

Inspect axiom output; only standard Lean logical axioms are allowed. Record
actual counts and scope in VERIFICATION.md. Update STATE.md, TASKS.md and the
relevant research note, preserving historical stage boundaries. Do not rerun
archive downloads or manuscript audits for this arithmetic-only change.
Stage only scoped files and commit the checked result under Claude Code's
normal local workflow. Do not fabricate author details or publish anything.
