# Autonomous continuation: completion criteria

Latest handoff: [HANDOFF-2026-10-06-REWORKED-SOURCES.md](HANDOFF-2026-10-06-REWORKED-SOURCES.md).
The user retired the 4 October work order after the source refactor and
bookkeeping cleanup. The next agent should start from the replacement, using
the current historical Lean files and their exact proof paragraphs.

The user authorized continued work across the approved milestones on
22 September 2026. Updated model policy: use `gpt-6-sol` for bounded reasoning
and implementation, and `gpt-6-luna` for compilation and checking. Earlier
5.5/5.6 assignments are superseded; no silent v5 fallback. Work remains
sequential, with at most one subagent at a time. Preserve the unrelated
conversation exports. The refactor and cleanup are held for review; do not
commit or push until the user releases that hold.

The governing targets remain the stage-separated De Motu, 1687 and 1713
Section II arguments in GOALS.md. Supporting M1–M4 reports retain their
undischarged premises; a successful special case is not full completion.

The 6 October instruction supersedes the older construction-first ordering:
prioritize Proposition I, then II, III and IV, separately in the three stages.
The primary proof takes the trajectory as given and proves swept-sector area
proportional to time. The nonnegative region BETWEEN polygon and trajectory
is separate approximation control. Neither conclusion nor polygon agreement
is included in trajectory existence. Retain the constructed motions as support.

## Immediate mathematical route

Follow the replacement handoff's order: Lemma I's two missing source-local
proofs, the geometric area passage in Lemmas II–III, their invoked corollaries
and composition, then Proposition I's historical swept-sector conclusion.
Kepler and force-specific applications come after that general proof.

The former zero-force/constant-force queue remains supporting history:
finite recurrence, subdivision, restart and within-cell results are retained
in BarrowLib/Polygon/ZeroForce.lean; completed inertial control and signed
defect results are in ModernLib/Polygon/ZeroForce.lean, InertialControl.lean
and InertialDefect.lean. PartitionControl.lean and PartialCell.lean retain
constant-force residual/mesh estimates in ModernLib/Polygon. Their external
time and general-force extensions remain open, without overriding the active
historical proof order.

## Completion ledger

| Target | What would discharge the remaining obligation |
| --- | --- |
| Section II I | From a given central-force trajectory and separately stated mechanical/regularity premises, prove ordinary swept-sector area proportional to time through the edition's invoked results; justify polygon approximation and separate between-path control where used |
| Section II II | Derive the converse with explicit realized-curve, plane, nondegeneracy and limiting assumptions, preserving the different forward/converse premises |
| Section II III | Derive common-time relative motion and force composition, then connect to each edition's converse route |
| Section II IV | Construct circular comparisons and justify their force/ratio bridge through the edition's actual cited route |
| M1 | Resolve the stated source chronology boundary where evidence permits; discharge curved contact, mechanical enclosure and variable-force comparison obligations |
| M2 | Connect Newton's polygon families to the given trajectory and justify the geometric sector-area passage; scalar fan convergence alone is insufficient |
| M3 | Discharge the geometric and mechanical premises behind the existing conditional bounds, retaining explicit uniformity conditions |
| M4 | Resolve direct-source gaps where evidence permits and justify the general route comparison; keep proposed numbering and actual editions separate |

A bounded absence finding or unavailable historical witness is evidence about
the source search, not a fabricated proof. A missing premise must remain
visible while other authorized obligations advance. The separate action
hypothesis may be tested against the constructed residuals, but neither an
unfinished proof nor a nonzero finite defect selects a universal constant.
