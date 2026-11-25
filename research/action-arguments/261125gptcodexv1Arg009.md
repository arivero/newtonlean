# Arg009 v1: reciprocal forces and one phase functional share an action unit

- Proposer: GPT (Codex), 22 November 2026, from a discussion with the user
  (issue 4). Written up on 25 November 2026 by Claude Opus 5.5 (Claude Code)
  from the issue, with the review and the Lean scope of Fable 5.2.
- Verdict: **supports a common unit across an interacting pair; its value is
  undetermined.** If two calibrated bodies with a non-constant reciprocal force
  are described by one stationary phase functional with a fixed diagonal
  kinetic form, the two action constants agree. Every common value reproduces
  the motion, so the classical construction fixes the kind of constant (one
  shared unit) and leaves its value free. Nothing here is identified with
  Planck's constant.
- Layer: action diagnostic (GOALS.md). It adds no historical proof edge and
  supplies no premise to an edition-local theorem. The Lean checks are in
  [ReciprocalPhase](../../ModernLib/Diagnostic/ReciprocalPhase.lean).

## Source

Rivero's late-1990s Kepler teaching note, recovered in September 2026, quoted
with its original spelling
([teaching note](https://lxbifi11.bifi.unizar.es/online/libretto/aceleraciones-hacia-un-punto.html)):

> Consideremos un muelle sujeto horizontalmente a dos masas. Tensamos el
> muelle y soltamos. Ambas masas se desplazan, acelerandose a distinta
> velocidad. Pero el muelle es totalmente simetrico, resulta absurdo suponer
> que la propiedad que causa la diferente aceleracion resida en el muelle;
> debe residir en los objetos acelerados. Llamamos masa inercial al
> coeficiente que relaciona el muelle, o mejor dicho la fuerza que este
> ejerce, y la aceleracion causada. Lo mas sencillo es suponer que este
> coeficiente es constante y, como hemos dicho, dependiente de cada cuerpo:
> F=m a.

> Si las fuerzas entre cuerpos cumplen la propiedad del muelle, y si F=m a,
> entonces hay un punto que permanece fijo, \sum xi mi \over \sum mi

> Dado que la dinamica de espacio tangente/cotangente es una generalizacion
> de la de origen de fuerzas, no es raro que la unidad que gobierna la
> dualidad entre ambos sea tambien la de h, la accion.

The first two passages supply the calibration step and the fixed centre. The
third asks the question tested here. The modern comparison is the spring
calculation and the algebraic mixed-force criterion (A10) of the
[navstokgap note](https://arivero.github.io/navstokgap/notes/rotation-composition-universality.html).

## Steps and status

1. **Calibration.** Reciprocal impulses `m_A Δv_A = -h V'` and
   `m_B Δv_B = +h V'` cancel, and the mass-weighted position advances
   uniformly, so it stays fixed when the total momentum vanishes. Any two
   calibrations that balance the same nonzero measured velocity changes have
   the same ratio `m_A/m_B = -Δv_B/Δv_A`. A common rescaling of both masses
   and the force law leaves every cell and every finite schedule unchanged.
   *Status:* `modern_reconstruction` of the note's calibration; checked:
   `cell_momentum`, `cell_centre`, `inertia_ratio`, `cell_rescale`,
   `schedule_rescale`.

2. **The lemma.** Premises: (P1) calibrated masses `m_A, m_B > 0`; (P2) a
   reciprocal force from `V ∈ C¹` on `x = q_A - q_B`, so `m_A q̈_A = -V'(x)`
   and `m_B q̈_B = +V'(x)`; (P3) one stationary phase functional
   `S = ∫ [T_A/s_A + T_B/s_B - W(q_A, q_B)] dt` with `T_i = m_i q̇_i²/2`,
   constants `s_i ≠ 0` and `W ∈ C¹`; (P4) its Euler–Lagrange equations have
   the same solutions as (P2). They read `m_i q̈_i = -s_i ∂_i W`. Solutions of
   (P2) pass through every configuration, so (P4) gives the identities
   `s_A ∂_A W = V'(x)` and `s_B ∂_B W = -V'(x)` everywhere. The first gives
   `W = V(x)/s_A + φ(q_B)` with `φ ∈ C¹`, and the second then gives
   `φ'(q_B) = V'(x)(1/s_A - 1/s_B)` for every `q_A`. The right side is
   therefore a constant `κ`. **For every non-constant force, `s_A = s_B`.**
   For `V' ≡ F` the general solution is `W = F q_A/s_A - F q_B/s_B + const`,
   which allows unequal constants. With `W ∈ C²` the same conclusion reads
   `V''(x)(1/s_A - 1/s_B) = 0`, the form of the issue.
   *Status:* `modern_reconstruction`; derivation here. Lean checks the
   polynomial case `V' = F + k x` with a quadratic `W`: `Reproduces`,
   `hooke_equates` (a Hooke term `k ≠ 0` equates the constants) and
   `common_value_free` (every common nonzero value is realized by `W = V/s`).

3. **Translations.** Strict invariance of `W` under `q_i ↦ q_i + c` means
   `∂_A W + ∂_B W = 0`, hence `V'(x)(1/s_A - 1/s_B) = 0`. In the boundary case
   `V' ≡ F` the phase rate shifts by the constant `κ c`, with
   `κ = F(1/s_A - 1/s_B)`, so `S` changes by `-κ c (t₁ - t₀)`, a term that
   depends only on the endpoint times and leaves the equations of motion
   unchanged. The corresponding conserved quantity is
   `m_A q̇_A/s_A + m_B q̇_B/s_B + κ t`. If the phase is required to depend on
   the separation alone, `W = w(q_A - q_B)`, a force that is nonzero at one
   separation already equates the constants.
   *Status:* `modern_reconstruction`; checked:
   `relative_iff_translation_invariant`, `linear_phase_translation` (the shift
   `F t (s_B - s_A)` after clearing denominators), `relative_phase_equates`,
   `linear_phase_relative_iff`.

4. **Impulse check.** The impulses generated by any reproducing phase are the
   calibrated impulses `-h V'` and `+h V'`, in both examples.
   *Status:* checked: `phase_impulses`, with `cell_momentum`.

5. **One counterexample per dropped premise.**

   | Premise dropped | Counterexample | Lean |
   | --- | --- | --- |
   | One phase functional (P3) | Two separate force covectors reproduce every Hooke force for arbitrary nonzero `s_A, s_B`; they close to one phase exactly when `k(s_A - s_B) = 0` | `separate_covectors` |
   | Non-constant force | `V' ≡ F` admits `W = F q_A/s_A - F q_B/s_B`, for example `s_A = 1`, `s_B = 2` | `constant_force_free`, `constant_force_unequal_example` |
   | Interaction | Free bodies leave the two constants unrelated | `free_bodies_unrelated` |

   *Status:* checked.

6. **Comparison with (A10).** The algebraic criterion
   `(h_i - h_j) ∂_{ia}∂_{jb} V = 0` admits the common zero branch
   `h_i = h_j = 0`. The phase functional divides by each `s_i`, and a
   vanishing constant reproduces only the free case: `s_A = 0` forces
   `F = k = 0`.
   *Status:* checked: `zero_excluded`; the comparison is
   `editorial_interpretation`.

## Literature, recalled

The mixed-derivative condition is the Helmholtz condition of the inverse
problem of the calculus of variations, for a constant diagonal multiplier.
Landau and Lifshitz, *Mechanics*, §2, state that a Lagrangian may be multiplied
by an arbitrary constant, and that for interacting parts the constant must be
common. Mach defines the mass ratio from mutual accelerations. All three are
recalled from memory and remain unverified until a passage is checked.

## GOALS.md tests

| Test | Result |
| --- | --- |
| Positivity | Not derived. A common negative value also reproduces the motion; positivity is a convention. A zero constant is excluded for an interacting pair (`zero_excluded`). |
| Finiteness | Every common nonzero rational value is admissible; nothing diverges. |
| Partition stability | The cell identities hold for every duration and every finite schedule of unequal durations. |
| System independence | Holds across one interacting pair with a non-constant force, for any masses. Extending it to many bodies needs a connected interaction graph, which this note does not treat. |
| Action-rescaling freedom | Retained. Every common value works (`common_value_free`), and a common rescaling of the masses and the force leaves the motion unchanged (`schedule_rescale`). |

## Consequence

The note's question receives a classical answer of limited scope. A single
stationary phase functional for two interacting bodies forces one shared action
unit, and the constant force is the exact boundary case. The value of the unit
stays free, as GOALS.md requires of a free normalization: identifying it with
`ħ` needs a further physical bridge, which this argument does not supply.
