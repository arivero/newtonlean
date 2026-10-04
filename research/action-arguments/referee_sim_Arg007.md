# Referee check of Arg007 and the first general-force increment

Verdict: the finite area and potential identities survive the checks below. Two scope edits are needed before Arg007 circulates. This review does not certify a polygon–curve area, a limiting trajectory, or a physical action constant.

| Reader | First correctness objection and answer | Novelty axis |
| --- | --- | --- |
| Lean/formal methods | Do the stated equations use the actual end-kick cell and exact rational arithmetic? Yes: `DeflectionPotential` uses `c=B+hv`, `C=c+h²a(B)`, signed doubled area, and potential at `C` minus potential at `c`. Independent direct evaluations gave Galilean doubled area `-1/2` and `ΔV=-3` for `m=3,g=2,h=1/2,v=(2,3)`, and harmonic `ΔV=-7/32` for `m=w=1,h=1/2,B=(1,0),v=(0,1)`. A deliberately false positive `7/32` statement failed in Lean. | None claimed. |
| Newton/source reader | Does the finite calculation close Proposition I in De Motu, 1687, or 1713? Arg007 labels every step `modern_reconstruction` and supplies no historical edge. Its triangle is explicitly distinct from `D_mesh`. | None claimed. |
| Geometry/dynamics reader | Is the kick displacement also the curve departure, and are signed/unsigned or doubled/ordinary areas confused? Arg007 separates these. The tangent triangle and chord–arc coefficients are written conditional expansions; neither has a constructed-curve Lean theorem. The radial `ell=0` exception and specific-versus-mass angular momentum are stated. | None claimed. |
| Physical-action reader | Does the ratio select a nonzero universal constant? Arg007 records zero-area cases, system-dependent `tau`, and mass rescaling. The Galilean identity gives a time-valued `tau` and an action dimension only. | None claimed. |

**Medium, Arg007 lines 28–30:** the condition `h ≥ 0` includes `h=0`, but `m Area/h` is then undefined. Require `h>0` for that displayed quotient; the preceding multiplication identity remains valid at zero duration.

**Low, Arg007 line 88:** the statement that the sum of `m Area/h` decreases with mesh needs nonnegative cell durations and the stated Galilean sign conditions, with “mesh” meaning refinement of a fixed interval. Under those conditions the sum is `(m g v_x/2) Σ h_i²`; splitting a cell decreases or preserves it. State these conditions beside the claim.

The Task A boundary is otherwise stated accurately: `ForceClasses` gives inward central samples, a uniform force-value Cauchy contract on a named region, and separate regularity predicates. `FiniteEstimates` proves local results for arbitrary maps under an explicit comparison contract, retaining `E` and the arrival-point displacement. There is not yet a theorem that turns `LipschitzOn` or `ContinuousOn` plus confinement into that contract along general polygon families, nor finite accumulation or general trajectory existence. The old `HarmonicComparison.cell_perturbation` name now calls generic amplification with `E=0`; it and `cell_bound` still elaborate. BarrowLib imports only BarrowLib modules and Std/core, so the inspected import graph has no Newton-side cycle.

Checks: `/tmp/newtonlean_arg007_referee_controls.lean` passed with Lean 4.19.0; `/tmp/newtonlean_arg007_referee_false_sign.lean` failed as intended because `decide` proved the proposed `+7/32` value false. The full build and repository validation belong to the separate verification pass.
