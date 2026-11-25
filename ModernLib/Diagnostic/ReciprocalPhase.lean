/-!
Action diagnostic layer (research/action-arguments Arg009, newtonlean issue 4).
Two bodies on a line joined by a reciprocal force `V'(q_A - q_B)`, with the
drift/impulse cell of the finite construction and independently calibrated
masses. The question is whether one stationary phase functional
`∫ [T_A/s_A + T_B/s_B - W(q_A, q_B)] dt` that reproduces the calibrated motion
forces a common action constant `s_A = s_B`. The Lean scope is the polynomial
case: `V' = F + k x`, a quadratic phase `W` whose two partial derivatives share
one mixed coefficient, and its counterexamples. The general `C¹` lemma is
derived in the Arg009 note.

Checked here: reciprocity and uniform motion of the mass-weighted position in
every cell; the inertia ratio fixed by measured velocity changes; invariance of
every schedule under a common rescaling of both masses and the force; a Hooke
term equates the constants (`hooke_equates`), every common nonzero value is
realized (`common_value_free`), and a relative phase with a nonzero force also
equates them. One counterexample per dropped premise: two separate force
covectors (`separate_covectors`), a constant force (`constant_force_free`), no
interaction (`free_bodies_unrelated`). A vanishing constant is excluded for an
interacting pair (`zero_excluded`), in contrast with the algebraic criterion
(A10) of the navstokgap note. The intended case has positive constants; the
lemmas hold for nonzero rationals.

Original-language source of the calibration step (Rivero's late-1990s Kepler
teaching note, quoted with its original spelling,
https://lxbifi11.bifi.unizar.es/online/libretto/aceleraciones-hacia-un-punto.html):
"Consideremos un muelle sujeto horizontalmente a dos masas. [...] Llamamos masa
inercial al coeficiente que relaciona el muelle, o mejor dicho la fuerza que
este ejerce, y la aceleracion causada. Lo mas sencillo es suponer que este
coeficiente es constante y, como hemos dicho, dependiente de cada cuerpo:
F=m a."

The underlying facts are known: the mixed-derivative condition is the Helmholtz
condition of the inverse problem of the calculus of variations for a constant
diagonal multiplier, a common factor for interacting parts is in Landau and
Lifshitz's Mechanics, and the mass ratio from mutual accelerations is Mach's
definition. Exact passages for these remain to be supplied and verified. The
statements and proofs are project derivations with no priority claim. The
verdict is limited to a common unit of undetermined value: nothing is
identified with Planck's constant and no historical proof uses this module.
-/

namespace NewtonLimitDynamics.Diagnostic.ReciprocalPhase

/-- A one-dimensional two-body state `(qA, vA, qB, vB)`. -/
structure State where
  qA : Rat
  vA : Rat
  qB : Rat
  vB : Rat
deriving DecidableEq

/-- Spring force law on the relative coordinate: `V'(x) = F + k x`. -/
def slope (F k x : Rat) : Rat := F + k * x

/-- One drift/impulse cell: drift both bodies, then the reciprocal impulses `∓ h V'(x)`. -/
def cell (mA mB F k h : Rat) (z : State) : State :=
  let qA := z.qA + h * z.vA
  let qB := z.qB + h * z.vB
  ⟨qA, z.vA - h * slope F k (qA - qB) / mA, qB, z.vB + h * slope F k (qA - qB) / mB⟩

def schedule (mA mB F k : Rat) : List Rat → State → State
  | [], z => z
  | h :: hs, z => schedule mA mB F k hs (cell mA mB F k h z)

/-- Reciprocity: the calibrated impulses cancel. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem cell_momentum (mA mB F k h : Rat) (hA : mA ≠ 0) (hB : mB ≠ 0) (z : State) :
    mA * (cell mA mB F k h z).vA + mB * (cell mA mB F k h z).vB = mA * z.vA + mB * z.vB := by
  simp only [cell]
  grind

/-- The mass-weighted position advances uniformly: the centre of mass keeps its motion and
stays fixed when the total momentum vanishes. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem cell_centre (mA mB F k h : Rat) (z : State) :
    mA * (cell mA mB F k h z).qA + mB * (cell mA mB F k h z).qB
      = mA * z.qA + mB * z.qB + h * (mA * z.vA + mB * z.vB) := by
  simp only [cell]
  grind

/-- The measured velocity changes fix the inertia ratio: any two calibrations that both
balance the same nonzero changes have the same ratio. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem inertia_ratio (mA mB nA nB dA dB : Rat) (hd : dA ≠ 0)
    (h1 : mA * dA + mB * dB = 0) (h2 : nA * dA + nB * dB = 0) : mA * nB = nA * mB := by
  have h3 : dA * (mA * nB - nA * mB) = 0 := by grind
  rcases Rat.mul_eq_zero.mp h3 with h | h
  · exact absurd h hd
  · grind

/-- A common rescaling of both masses and the force law leaves every cell unchanged. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem cell_rescale (mA mB F k h c : Rat) (hc : c ≠ 0) (z : State) :
    cell (c * mA) (c * mB) (c * F) (c * k) h z = cell mA mB F k h z := by
  simp only [cell, slope, State.mk.injEq, true_and]
  refine ⟨?_, ?_⟩ <;> grind

/-- A common rescaling leaves every finite schedule unchanged. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem schedule_rescale (mA mB F k c : Rat) (hc : c ≠ 0) : (hs : List Rat) → (z : State) →
    schedule (c * mA) (c * mB) (c * F) (c * k) hs z = schedule mA mB F k hs z
  | [], _ => rfl
  | h :: hs, z => by
      simp only [schedule, cell_rescale mA mB F k h c hc]
      exact schedule_rescale mA mB F k c hc hs _

/-- A quadratic phase potential `W = b qA + c qB + d qA² + e qA qB + f qB²`. The single
coefficient `e` in both partial derivatives is the commutation of mixed derivatives. -/
structure Phase where
  b : Rat
  c : Rat
  d : Rat
  e : Rat
  f : Rat

def Phase.value (W : Phase) (qA qB : Rat) : Rat :=
  W.b * qA + W.c * qB + W.d * (qA * qA) + W.e * (qA * qB) + W.f * (qB * qB)
def Phase.dA (W : Phase) (qA qB : Rat) : Rat := W.b + 2 * W.d * qA + W.e * qB
def Phase.dB (W : Phase) (qA qB : Rat) : Rat := W.c + W.e * qA + 2 * W.f * qB

/-- The stationary phase functional with constants `sA`, `sB` reproduces the calibrated forces. -/
def Reproduces (sA sB : Rat) (W : Phase) (F k : Rat) : Prop :=
  ∀ qA qB, sA * W.dA qA qB = slope F k (qA - qB) ∧ sB * W.dB qA qB = -slope F k (qA - qB)

/-- A Hooke term equates the two constants. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem hooke_equates (sA sB : Rat) (W : Phase) (F k : Rat) (hk : k ≠ 0)
    (h : Reproduces sA sB W F k) : sA = sB := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  simp only [Phase.dA, Phase.dB, slope] at h00 h01 h10
  have he : sA * W.e = -k := by grind
  have he' : sB * W.e = -k := by grind
  have hz : (sA - sB) * W.e = 0 := by grind
  rcases Rat.mul_eq_zero.mp hz with h | h
  · grind
  · exfalso; apply hk; rw [h] at he; grind

/-- Every common nonzero value is realized: `W = V / s`. -/
def springPhase (s F k : Rat) : Phase := ⟨F / s, -(F / s), k / (2 * s), -(k / s), k / (2 * s)⟩

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem common_value_free (s F k : Rat) (hs : s ≠ 0) : Reproduces s s (springPhase s F k) F k := by
  intro qA qB
  simp only [Phase.dA, Phase.dB, springPhase, slope]
  constructor <;> grind

/-- Boundary case: a constant force admits unequal constants. -/
def linearPhase (sA sB F : Rat) : Phase := ⟨F / sA, -(F / sB), 0, 0, 0⟩

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem constant_force_free (sA sB F : Rat) (hA : sA ≠ 0) (hB : sB ≠ 0) :
    Reproduces sA sB (linearPhase sA sB F) F 0 := by
  intro qA qB
  simp only [Phase.dA, Phase.dB, linearPhase, slope]
  constructor <;> grind

-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem constant_force_unequal_example : Reproduces 1 2 (linearPhase 1 2 1) 1 0 ∧ (1 : Rat) ≠ 2 :=
  ⟨constant_force_free 1 2 1 (by grind) (by grind), by grind⟩

/-- The phase depends on the relative coordinate alone: `W = w(qA - qB)`. -/
def Relative (W : Phase) : Prop := W.c = -W.b ∧ W.f = W.d ∧ W.e = -(2 * W.d)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem relative_iff_translation_invariant (W : Phase) :
    Relative W ↔ ∀ qA qB t, W.value (qA + t) (qB + t) = W.value qA qB := by
  constructor
  · rintro ⟨hc, hf, he⟩ qA qB t
    simp only [Phase.value, hc, hf, he]
    grind
  · intro h
    have h1 := h 0 0 1
    have h2 := h 1 0 1
    have h3 := h 0 1 1
    simp only [Phase.value] at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩ <;> grind

/-- With a relative phase, a force that is nonzero at one separation equates the constants. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem relative_phase_equates (sA sB : Rat) (W : Phase) (F k x : Rat) (hrel : Relative W)
    (hF : slope F k x ≠ 0) (h : Reproduces sA sB W F k) : sA = sB := by
  obtain ⟨hc, hf, he⟩ := hrel
  have hx := h x 0
  simp only [Phase.dA, Phase.dB, hc, hf, he, slope] at hx hF
  have hz : (sA - sB) * (W.b + 2 * W.d * x) = 0 := by grind
  rcases Rat.mul_eq_zero.mp hz with h | h
  · grind
  · exfalso; apply hF; grind

/-- A translation shifts the linear phase by a constant, which vanishes exactly when the
constants agree (stated without division). -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem linear_phase_translation (sA sB F qA qB t : Rat) (hA : sA ≠ 0) (hB : sB ≠ 0) :
    sA * sB * ((linearPhase sA sB F).value (qA + t) (qB + t) - (linearPhase sA sB F).value qA qB)
      = F * t * (sB - sA) := by
  simp only [Phase.value, linearPhase]
  grind

/-- The impulses of the phase functional are the calibrated impulses. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem phase_impulses (sA sB mA mB : Rat) (W : Phase) (F k h qA qB : Rat) (hA : mA ≠ 0)
    (hB : mB ≠ 0) (hrep : Reproduces sA sB W F k) :
    mA * (-(h * (sA * W.dA qA qB) / mA)) = -(h * slope F k (qA - qB)) ∧
    mB * (-(h * (sB * W.dB qA qB) / mB)) = h * slope F k (qA - qB) := by
  obtain ⟨h1, h2⟩ := hrep qA qB
  rw [h1, h2]
  constructor <;> grind

/-- Without interaction the constants are unrelated. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem free_bodies_unrelated (sA sB : Rat) : Reproduces sA sB ⟨0, 0, 0, 0, 0⟩ 0 0 := by
  intro qA qB
  simp only [Phase.dA, Phase.dB, slope]
  constructor <;> grind

/-- Two affine force covectors with independent mixed coefficients `eA`, `eB`: the two
Euler–Lagrange right-hand sides when they are not required to come from one phase. -/
structure Covectors where
  b : Rat
  c : Rat
  d : Rat
  eA : Rat
  eB : Rat
  f : Rat

def Covectors.gA (G : Covectors) (qA qB : Rat) : Rat := G.b + 2 * G.d * qA + G.eA * qB
def Covectors.gB (G : Covectors) (qA qB : Rat) : Rat := G.c + G.eB * qA + 2 * G.f * qB

/-- The covectors are the two partial derivatives of one quadratic phase. -/
def Covectors.Closed (G : Covectors) : Prop := G.eA = G.eB

def hookeCovectors (sA sB F k : Rat) : Covectors :=
  ⟨F / sA, -(F / sB), k / (2 * sA), -(k / sA), -(k / sB), k / (2 * sB)⟩

/-- Dropping the single phase: separate covectors reproduce every Hooke force for arbitrary
nonzero constants, and they are closed exactly when `k (sA - sB) = 0`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem separate_covectors (sA sB F k : Rat) (hA : sA ≠ 0) (hB : sB ≠ 0) :
    (∀ qA qB, sA * (hookeCovectors sA sB F k).gA qA qB = slope F k (qA - qB) ∧
      sB * (hookeCovectors sA sB F k).gB qA qB = -slope F k (qA - qB)) ∧
    ((hookeCovectors sA sB F k).Closed ↔ k * (sA - sB) = 0) := by
  refine ⟨fun qA qB => ?_, ?_⟩
  · simp only [Covectors.gA, Covectors.gB, hookeCovectors, slope]
    constructor <;> grind
  · simp only [Covectors.Closed, hookeCovectors]
    constructor
    · intro h
      have h2 : sA * sB * (-(k / sA)) = sA * sB * (-(k / sB)) := by rw [h]
      grind
    · intro h
      rcases Rat.mul_eq_zero.mp h with h | h
      · rw [h]; grind
      · have : sA = sB := by grind
        rw [this]

/-- The constant-force phase is relative exactly when the constants agree or the force vanishes. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem linear_phase_relative_iff (sA sB F : Rat) (hA : sA ≠ 0) (hB : sB ≠ 0) :
    Relative (linearPhase sA sB F) ↔ F * (sA - sB) = 0 := by
  constructor
  · rintro ⟨h, _, _⟩
    simp only [linearPhase] at h
    have h2 : sA * sB * (-(F / sB)) = sA * sB * (-(F / sA)) := by rw [h]
    grind
  · intro h
    have hc : -(F / sB) = -(F / sA) := by
      rcases Rat.mul_eq_zero.mp h with h | h
      · rw [h]; grind
      · have : sA = sB := by grind
        rw [this]
    exact ⟨hc, rfl, by show (0 : Rat) = -(2 * 0); grind⟩

/-- The zero branch is excluded for an interacting pair: a vanishing constant reproduces only
the free case. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem zero_excluded (sB : Rat) (W : Phase) (F k : Rat) (h : Reproduces 0 sB W F k) :
    F = 0 ∧ k = 0 := by
  have h00 := (h 0 0).1
  have h10 := (h 1 0).1
  simp only [slope] at h00 h10
  constructor <;> grind

end NewtonLimitDynamics.Diagnostic.ReciprocalPhase
