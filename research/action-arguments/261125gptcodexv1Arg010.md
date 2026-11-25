# Arg010 v1: which orbit restrictions turn equal areas into an action bound

- Proposer: GPT (Codex), 22 November 2026, from a discussion with the user
  (issue 5). Written up on 25 November 2026 by Claude Opus 5.5 (Claude Code)
  from the issue, with the review and the Lean scope of Fable 5.2.
- Verdict: **inconclusive for a universal constant; a bound appears only under
  an orbit restriction, and its value is system-dependent or imported.** Equal
  swept areas compare no two polygons without a common force. For the inverse
  cube `-k/r³` the action `√(m k)` bounds `|L|` from below only for
  collision-free orbits in both time directions, or for release from an apsis;
  over all orbits there is no bound, and at zero energy the bound turns around.
  The Planck matching of a Kepler areal velocity imports `ħ` through `ℓ_P` and
  bounds an areal velocity of the source's circle, not the test body's action.
- Layer: action diagnostic (GOALS.md). It adds no historical proof edge and
  supplies no premise to an edition-local theorem. The Lean checks are in
  [ArealBounds](../../ModernLib/Diagnostic/ArealBounds.lean).

## 1. Equal areas without a common force

Take `r₁² = R² + α sin θ` and `r₂² = R²` with `0 < α < R²`, each traversed with
`dt = m r_i² dθ / L` for the same `L > 0`. Both have areal velocity `L/(2m)`,
period `(m/L) ∮ r_i² dθ = 2π m R²/L` and enclosed area `π R²`. They start at
the same point (`θ = 0`), their signed area difference is
`(α/2) ∮ sin θ dθ = 0`, and their lobes have total area
`(α/2) ∮ |sin θ| dθ = 2α`. Their initial velocities differ by the radial
component `α L/(2 m R³)`.

Curve 1 is symmetric under `θ ↦ π - θ`, about its apsidal lines `θ = π/2` and
`3π/2`. Each radius in `[√(R² - α), √(R² + α)]` is reached at two reflected
angles with the same value of Binet's `u'' + u`, so curve 1 is an orbit of a
central force law `f₁(r)` on that interval, different from the force of the
circle. Equal areal velocity, period and area are kinematic data shared by
orbits of different forces.

The premise that separates them in the repository is the same-force clause of
`MotionSampling.Conditions`: `local_remainder` ties the given curve to the
field `a` of the polygon, with `force_comparison` (a Lipschitz bound for `a`)
and `short_window`. `sampled_agreement` is the conclusion that polygon and
curve agree. A finite control isolates the point: from one initial state the
zero field and the Hooke field `-p` sweep equal signed areas over every finite
schedule, while their polygons differ at the second vertex. The existing
`PathDefect.equal_Kepler_areas_positive_path_defect` gives equal Kepler areas
with a positive unsigned path defect.

*Status:* integrals and the Binet step are derivations
(`modern_reconstruction`); the premise naming is `editorial_interpretation`;
checked: `equal_swept_areas`, `different_polygons`, `freeField_central`,
`hookeField_central`.

## 2. The inverse cube and its orbit classes

With `Δ = L² - m k`, the radial energy of the force `-k/r³` is
`E = ½ m ṙ² + Δ/(2 m r²)`, checked in the form
`2 m r² E = (m r ṙ)² + Δ` (`EnergyRelation`). Circles have `L² = m k` at every
radius (`circular_action`).

| Class, force `-k/r³` fixed | Orbits that remain | Bound on `\|L\|` | Basis |
| --- | --- | --- | --- |
| All orbits | Zero-energy spirals into the centre for every `0 < \|L\| < √(mk)` | None: infimum 0 | `small_action_infall`; finite-time collision is a derivation |
| Periodic | Circles, at every radius | `= √(mk)` | `circular_action`; that no other orbit is periodic is a derivation |
| Collision-free in both time directions | Circles and the `Δ > 0` scattering orbits, `r² ≥ Δ/(2mE)` | `≥ √(mk)` | `supercritical_bound`, `critical_radial`, `subcritical_no_apsis`, `subcritical_bounded`; the global classification is a derivation |
| Collision-free in the future only | Also every outgoing orbit with `Δ < 0`, `E ≥ 0` or `Δ = 0`, `E > 0` | None | `subcritical_no_apsis`; escape is a derivation |
| Released from an apsis, `ṙ = 0` | `Δ < 0` falls in, `Δ = 0` is a circle, `Δ > 0` escapes | Collision-free exactly for `≥ √(mk)` | `apsis_energy_sign`, `critical_radial`; the motions after release are derivations |
| Zero energy | Circles and the spirals | `≤ √(mk)`: the bound turns around | `zero_energy_upper` |

The future collision condition reads: the orbit reaches the centre exactly
when `Δ < 0` and (`E < 0` or `ṙ < 0`), or `Δ = 0` and `ṙ < 0`. At `Δ = 0` the
energy is `½ m ṙ²`, so `ṙ` is constant, and inward motion reaches the centre
in the finite time `r/|ṙ|`; only `ṙ = 0` gives a circle.

*Status:* `modern_reconstruction`, the textbook effective-potential analysis
of the `1/r²` potential; algebra checked as listed, global motions derived.

### Examples for the proposed bound `|L| ≥ √(mk)`

- Positive: every circle (`circular_action`); a `Δ > 0` orbit, whose
  pericentre obeys `r² ≥ Δ/(2mE) > 0` (`supercritical_bound`).
- Negative: with `m k = c²` and any `ε > 0`, zero-energy infall data at `r = 1`
  with `0 < L < ε` and `ṙ < 0` (`small_action_infall`); at zero energy every
  orbit has `L² ≤ m k` (`zero_energy_upper`).

## 3. The Planck matching and its units

| Quantity | Expression | Units |
| --- | --- | --- |
| Swept area rate | `Ȧ = r v / 2` | `L² T⁻¹` |
| Specific angular momentum | `r v = 2 Ȧ` | `L² T⁻¹` |
| Angular momentum of the test body | `L = m r v` | `M L² T⁻¹` (an action) |
| Phase-space area of the circular orbit | `∮ p_θ dθ = 2π L` | `M L² T⁻¹` |

For a Kepler circle `(r v)² = G M r`, and `(ℓ_P²/t_P)² = ħ G/c`, with
`ℓ_P² = ħ G/c³` and `t_P = ℓ_P/c`. Write the matching as `r v = λ ℓ_P c`.
Then `M c r = λ² ħ`: Newton's constant cancels, `ħ` enters through `ℓ_P`, and
the clock through `t_P` (`planck_areal_radius`). The issue's matching
`Ȧ = ℓ_P²/(2 t_P)` is `λ = 1`, which gives `r = ħ/(M c)`. The dimensional
note's "one unit of Planck area in one unit of Planck time" is `Ȧ = ℓ_P²/t_P`,
`λ = 2`, which gives `r = 4ħ/(M c)`. The factor `λ` is a free normalization.

The matched quantity `r v` equals `λ ħ/m_P` and is an areal velocity. The test
body's angular momentum is `L = λ ħ m/m_P` (`test_body_action`), an action that
equals `ħ` at `λ = 1` exactly when `m = m_P` (`action_is_hbar_iff`). The
phase-space area is `2π L`. At the matched radius the orbital speed obeys
`(v/c)² = (M/m_P)²` (`matched_speed`, in the form `v² ħ = G M² c`).

### Examples for the proposed bound `r ≥ ħ/(M c)`

- Kepler circles: `r = 4ħ/(M c)` (`λ = 2`) satisfies it; `r = ħ/(4 M c)`
  (`λ = 1/2`) violates it, and nothing in the classical orbit forbids that
  radius.
- Bohr circles `L = n ħ` on a Kepler orbit: the bound holds exactly when
  `G m² ≤ n² ħ c` (`bohr_bound_iff`). The ground state `n = 1` satisfies it
  for `m ≤ m_P` and violates it for `m = 2 m_P`.

*Status:* the unit bookkeeping is checked as listed; the identification of the
matching with a physical bound is `editorial_interpretation`.

### Gauss-law scaling

In `D` spacetime dimensions the Gauss-law force is `κ/r^(D-2)`, and circles
obey `m (r v)² = κ r^(5-D)`, so `Ȧ ∝ r^((5-D)/2)`. At `D = 5` the areal
velocity is the same at every radius (`gauss_five`); at `D = 4`, `(r v)²` grows
as `r` (`gauss_four`). The general exponent is a derivation.

## Relation to Arg002 and Arg003

Arg002 step 3, the calibrated value `L² = m k` of the inverse-cube invariant, is
now checked (`circular_action`); its spiral addendum `L² = m k sin²α` is the
zero-energy relation `L² + (m r ṙ)² = m k`. Arg003 step 3 for `p = -3` is
refined: at `Δ = 0` inward motion also reaches the centre, so descent happens
exactly under the condition stated in §2, and the boundary `L² = m k` itself
belongs to the descending side for inward motion (`critical_radial`).

## GOALS.md tests

| Test | Result |
| --- | --- |
| Positivity | `√(mk) > 0` and `ħ/(Mc) > 0`, but each bound holds only under an orbit restriction or an imported constant. |
| Finiteness | Finite in every case. |
| Partition stability | Equal swept areas hold for every finite schedule and every central force (§1), so the area law alone selects nothing; the bounds of §2 are continuum statements. |
| System independence | Fails: `√(mk)` depends on the body and the force, `ħ/(Mc)` on the source mass, and the test body's action on its own mass. |
| Action-rescaling freedom | Retained classically: rescaling `m` and `k` rescales `√(mk)`. The Planck matching carries the free factor `λ`, and its value of `ħ` is imported. |

## Consequence

The equal-area law becomes a bound on an action only after a restriction on
the admissible orbits: collision avoidance in both time directions, or release
from an apsis, for the inverse cube. Its value `√(mk)` is fixed by the system.
The Planck matching supplies a scale only because `ħ` is put in through `ℓ_P`;
GOALS.md requires a further physical bridge before that value counts as derived.
