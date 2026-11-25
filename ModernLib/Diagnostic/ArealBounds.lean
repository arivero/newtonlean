import BarrowLib.Polygon.CentralSchedule

/-!
Action diagnostic layer (research/action-arguments Arg010, newtonlean issue 5).
Which orbit restrictions turn Newton's equal-area law into a bound on an action?

Part 1, equal areas without a common force: from one initial state the zero
field and the Hooke field `-p` sweep equal signed areas over every finite
schedule (`equal_swept_areas`, through `CentralSchedule.swept_eq`), while their
polygons differ (`different_polygons`). Equal areas therefore compare no two
polygons unless the same force is supplied.

Part 2, the inverse-cube force `-k/r³`: its radial energy relation, cleared of
denominators as `2 m r² E = (m r ṙ)² + (L² - m k)`, and the orbit classes it
separates. Circles have `L² = m k` at every radius; `L² > m k` forces positive
energy and a pericentre; `L² < m k` with `E ≥ 0` has no apsis; `L² = m k` has
`ṙ = 0` exactly at zero energy; zero energy forces `L² ≤ m k`; and zero-energy
infall exists with arbitrarily small positive `L`.

Part 3, unit bookkeeping for a Planck matching of the Kepler areal velocity:
`G` cancels and `M c r = λ² ħ`, the test body's action depends on its own mass,
Gauss-law circles in five and four spacetime dimensions, the Bohr comparison
and the matched speed.

The Lean scope is the algebra of the energy relation and the unit bookkeeping;
finite-time collision and the trigonometric curves of the issue are derived in
the Arg010 note. The mathematics is the textbook effective-potential analysis
and dimensional bookkeeping; the statements and proofs are project derivations
with no priority claim. No historical proof uses this module, and nothing here
derives the value of `ħ`.
-/

namespace NewtonLimitDynamics.Diagnostic.ArealBounds
open NewtonLimitDynamics NewtonLimitDynamics.Polygon.TimeSubdivision
open NewtonLimitDynamics.Polygon.CentralSchedule

/-! Part 1: equal areas, different polygons. -/

def freeField : Field := fun _ => (Fraction.ofInt 0, Fraction.ofInt 0)
def hookeField : Field := fun p => pointNeg p

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem freeField_central : central freeField := by
  intro p
  simp only [freeField, det, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt]
  simp

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem hookeField_central : central hookeField := by
  intro p
  simp only [hookeField, pointNeg, det, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
    Int.add_mul, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Same initial state, two central forces: the swept areas agree for every schedule. -/
-- Modern dependency score: 2/20 (M=2, H=18; transitive project theorems/axioms).
theorem equal_swept_areas (ds : List Fraction) (s : Point × Point) :
    Fraction.equiv (swept freeField ds s) (swept hookeField ds s) :=
  Fraction.equiv_trans (swept_eq freeField freeField_central ds s)
    (Fraction.equiv_symm (swept_eq hookeField hookeField_central ds s))

def start : Point × Point :=
  ((Fraction.ofInt 1, Fraction.ofInt 0), (Fraction.ofInt 0, Fraction.ofInt 1))

/-- The two polygons differ at the second vertex. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem different_polygons :
    ¬ pointEquiv (schedule freeField [Fraction.ofInt 1, Fraction.ofInt 1] start).1
        (schedule hookeField [Fraction.ofInt 1, Fraction.ofInt 1] start).1 := by
  decide

/-! Part 2: the inverse-cube radial energy relation, cleared of denominators. -/

/-- `2 m r² E = (m r ṙ)² + (L² - m k)`: the energy `E = m ṙ²/2 + (L² - m k)/(2 m r²)` of the
force `-k/r³`, multiplied by `2 m r²`. -/
def EnergyRelation (m k L E r rdot : Rat) : Prop :=
  2 * m * (r * r) * E = (m * r * rdot) * (m * r * rdot) + (L * L - m * k)

/-- Circular balance `m v²/r = k/r³` gives `L² = m k` at every radius. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem circular_action (m k r v : Rat) (hr : r ≠ 0) (hbal : m * (v * v) / r = k / (r * r * r)) :
    (m * r * v) * (m * r * v) = m * k := by
  have h3 : r * r * r ≠ 0 := by
    intro h0
    rcases Rat.mul_eq_zero.mp h0 with h | h
    · rcases Rat.mul_eq_zero.mp h with h | h <;> exact hr h
    · exact hr h
  have e1 : m * (v * v) / r * r = m * (v * v) := Rat.div_mul_cancel hr
  have e2 : k / (r * r * r) * (r * r * r) = k := Rat.div_mul_cancel h3
  have e3 : m * (v * v) * (r * r) = k := by
    have : m * (v * v) / r * r * (r * r) = k / (r * r * r) * (r * r * r) := by rw [hbal]; grind
    rw [e1, e2] at this
    exact this
  grind

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem sq_nonneg (x : Rat) : 0 ≤ x * x := by
  rcases Rat.le_total (a := 0) (b := x) with h | h
  · exact Rat.mul_nonneg h h
  · have := Rat.mul_nonneg (show (0 : Rat) ≤ -x by grind) (show (0 : Rat) ≤ -x by grind)
    grind

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem sq_pos (x : Rat) (hx : x ≠ 0) : 0 < x * x := by
  rcases Rat.le_total (a := 0) (b := x) with h | h
  · exact Rat.mul_pos (by grind) (by grind)
  · have := Rat.mul_pos (show (0 : Rat) < -x by grind) (show (0 : Rat) < -x by grind)
    grind

/-- `L² > m k`: positive energy and a pericentre, `L² - m k ≤ 2 m r² E`. -/
-- Modern dependency score: 2/2 (M=2, H=0; transitive project theorems/axioms).
theorem supercritical_bound (m k L E r rdot : Rat) (hm : 0 < m) (hr : r ≠ 0)
    (hL : m * k < L * L) (h : EnergyRelation m k L E r rdot) :
    0 < E ∧ L * L - m * k ≤ 2 * m * (r * r) * E := by
  have hw := sq_nonneg (m * r * rdot)
  have hrr := sq_pos r hr
  have hc : 0 < 2 * m * (r * r) := Rat.mul_pos (by grind) hrr
  unfold EnergyRelation at h
  refine ⟨?_, by grind⟩
  rcases Rat.le_total (a := E) (b := 0) with hE | hE
  · have := Rat.mul_nonneg (Rat.le_of_lt hc) (show (0 : Rat) ≤ -E by grind)
    grind
  · have hne : E ≠ 0 := by
      intro h0; rw [h0] at h; grind
    grind

/-- `L² < m k` with `E ≥ 0`: the radial velocity never vanishes. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem subcritical_no_apsis (m k L E r rdot : Rat) (hm : 0 < m) (hr : r ≠ 0)
    (hL : L * L < m * k) (hE : 0 ≤ E) (h : EnergyRelation m k L E r rdot) : rdot ≠ 0 := by
  intro h0
  have hrr := sq_pos r hr
  have hc := Rat.mul_nonneg (Rat.mul_nonneg (show (0 : Rat) ≤ 2 * m by grind) (Rat.le_of_lt hrr)) hE
  unfold EnergyRelation at h
  rw [h0] at h
  grind

/-- `L² < m k` with `E < 0`: the orbit is bounded, `2 m r² (-E) ≤ m k - L²`. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem subcritical_bounded (m k L E r rdot : Rat)
    (h : EnergyRelation m k L E r rdot) : 2 * m * (r * r) * (-E) ≤ m * k - L * L := by
  have hw := sq_nonneg (m * r * rdot)
  unfold EnergyRelation at h
  grind

/-- `L² = m k`: the radial velocity vanishes exactly at zero energy. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem critical_radial (m k L E r rdot : Rat) (hm : 0 < m) (hr : r ≠ 0)
    (hL : L * L = m * k) (h : EnergyRelation m k L E r rdot) : rdot = 0 ↔ E = 0 := by
  have hrr := sq_pos r hr
  have hc : 2 * m * (r * r) ≠ 0 := by
    have : 0 < 2 * m * (r * r) := Rat.mul_pos (by grind) hrr
    grind
  have hmr : m * r ≠ 0 := by
    intro h0; rcases Rat.mul_eq_zero.mp h0 with h | h
    · grind
    · exact hr h
  unfold EnergyRelation at h
  constructor
  · intro h0
    rw [h0] at h
    have : 2 * m * (r * r) * E = 0 := by grind
    rcases Rat.mul_eq_zero.mp this with h | h
    · exact absurd h hc
    · exact h
  · intro h0
    rw [h0] at h
    have : (m * r * rdot) * (m * r * rdot) = 0 := by grind
    have h2 : m * r * rdot = 0 := by
      rcases Rat.mul_eq_zero.mp this with h | h <;> exact h
    rcases Rat.mul_eq_zero.mp h2 with h | h
    · exact absurd h hmr
    · exact h

/-- At zero energy `L² ≤ m k`: fixing this preparation turns the bound around. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem zero_energy_upper (m k L r rdot : Rat) (h : EnergyRelation m k L 0 r rdot) :
    L * L ≤ m * k := by
  have hw := sq_nonneg (m * r * rdot)
  unfold EnergyRelation at h
  grind

/-- At an apsis the sign of the energy is the sign of `L² - m k`. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem apsis_energy_sign (m k L E r : Rat) (hm : 0 < m) (hr : r ≠ 0)
    (h : EnergyRelation m k L E r 0) :
    (E < 0 ↔ L * L < m * k) ∧ (0 < E ↔ m * k < L * L) := by
  have hrr := sq_pos r hr
  have hc : 0 < 2 * m * (r * r) := Rat.mul_pos (by grind) hrr
  unfold EnergyRelation at h
  have key : 2 * m * (r * r) * E = L * L - m * k := by grind
  constructor
  · constructor
    · intro hE
      have := Rat.mul_pos hc (show (0 : Rat) < -E by grind)
      grind
    · intro hL
      rcases Rat.le_total (a := 0) (b := E) with h0 | h0
      · have := Rat.mul_nonneg (Rat.le_of_lt hc) h0
        grind
      · have hne : E ≠ 0 := by intro h1; rw [h1] at key; grind
        grind
  · constructor
    · intro hE
      have := Rat.mul_pos hc hE
      grind
    · intro hL
      rcases Rat.le_total (a := E) (b := 0) with h0 | h0
      · have := Rat.mul_nonneg (Rat.le_of_lt hc) (show (0 : Rat) ≤ -E by grind)
        grind
      · have hne : E ≠ 0 := by intro h1; rw [h1] at key; grind
        grind

/-- Zero-energy infall data with arbitrarily small positive `L`, for `m k = c²`, at `r = 1`. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem small_action_infall (m c eps : Rat) (hm : 0 < m) (hc : 0 < c) (heps : 0 < eps) :
    ∃ L rdot : Rat, 0 < L ∧ L < eps ∧ rdot < 0 ∧ L * L < c * c ∧
      EnergyRelation m (c * c / m) L 0 1 rdot := by
  -- t = min (1/2) (eps / (4 c)), L = 2 c t / (1 + t²), w = c (1 - t²) / (1 + t²)
  obtain ⟨t, ht0, ht1, htc⟩ : ∃ t : Rat, 0 < t ∧ t ≤ 1 / 2 ∧ 4 * c * t ≤ eps := by
    obtain ⟨q, hq, hmul⟩ : ∃ q : Rat, 0 < q ∧ q * (4 * c) = eps :=
      ⟨eps / (4 * c), by rw [Rat.div_def]; exact Rat.mul_pos heps (Rat.inv_pos.mpr (by grind)),
        Rat.div_mul_cancel (by grind)⟩
    rcases Rat.le_total (a := q) (b := 1 / 2) with h | h
    · exact ⟨q, hq, h, by grind⟩
    · have := Rat.mul_le_mul_of_nonneg_left h (show (0 : Rat) ≤ 4 * c by grind)
      exact ⟨1 / 2, by grind, by grind, by grind⟩
  have htt := sq_pos t (by grind)
  have hd : (0 : Rat) < 1 + t * t := by grind
  have hdz : 1 + t * t ≠ 0 := by grind
  obtain ⟨u, hu⟩ : ∃ u : Rat, u * (1 + t * t) = 1 := ⟨1 / (1 + t * t), Rat.div_mul_cancel hdz⟩
  have hu0 : 0 < u := by
    rcases Rat.le_total (a := u) (b := 0) with h | h
    · have := Rat.mul_nonneg (show (0 : Rat) ≤ -u by grind) (Rat.le_of_lt hd)
      grind
    · have : u ≠ 0 := by intro h0; rw [h0] at hu; grind
      grind
  have hu1 : u ≤ 1 := by
    have := Rat.mul_nonneg (Rat.le_of_lt hu0) (Rat.le_of_lt htt)
    grind
  have hmz : m ≠ 0 := by grind
  have hk : m * (c * c / m) = c * c := by
    have := Rat.div_mul_cancel (a := c * c) hmz
    grind
  obtain ⟨v, hv⟩ : ∃ v : Rat, v * m = 1 := ⟨1 / m, Rat.div_mul_cancel hmz⟩
  -- L = 2 c t u, w = c (1 - t²) u, rdot = -(w v)
  have htu := Rat.mul_pos ht0 hu0
  have hL0 : 0 < 2 * c * t * u := by
    have := Rat.mul_pos (Rat.mul_pos (show (0 : Rat) < 2 * c by grind) ht0) hu0
    grind
  have hLle : 2 * c * t * u ≤ 2 * c * t := by
    have := Rat.mul_le_mul_of_nonneg_left hu1 (show (0 : Rat) ≤ 2 * c * t by
      have := Rat.mul_pos (show (0 : Rat) < 2 * c by grind) ht0; grind)
    grind
  have ht2 : t * t ≤ 1 / 4 := by
    have := Rat.mul_le_mul_of_nonneg_left ht1 (Rat.le_of_lt ht0)
    grind
  have hw0 : 0 < c * (1 - t * t) * u := Rat.mul_pos (Rat.mul_pos hc (by grind)) hu0
  have hv0 : 0 < v := by
    rcases Rat.le_total (a := v) (b := 0) with h | h
    · have := Rat.mul_nonneg (show (0 : Rat) ≤ -v by grind) (Rat.le_of_lt hm)
      grind
    · have : v ≠ 0 := by intro h0; rw [h0] at hv; grind
      grind
  have hid : (2 * c * t * u) * (2 * c * t * u) + (c * (1 - t * t) * u) * (c * (1 - t * t) * u)
      = c * c * ((u * (1 + t * t)) * (u * (1 + t * t))) := by grind
  rw [hu] at hid
  refine ⟨2 * c * t * u, -(c * (1 - t * t) * u * v), hL0, by grind, ?_, ?_, ?_⟩
  · have := Rat.mul_pos hw0 hv0
    grind
  · have := sq_pos (c * (1 - t * t) * u) (by grind)
    grind
  · unfold EnergyRelation
    rw [hk]
    have hmv : m * 1 * (-(c * (1 - t * t) * u * v)) = -(c * (1 - t * t) * u) * (v * m) := by grind
    rw [hmv, hv]
    grind

/-! Part 3: where the Planck normalization enters. `twoA = r v` is twice the areal velocity,
`ħ G / c` is the square of `ℓ_P² / t_P`, and `lam` counts Planck units of `r v`. -/

/-- A Kepler circle `(r v)² = G M r` with `(r v)² = lam² ħ G / c` has `M c r = lam² ħ`:
Newton's constant cancels. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem planck_areal_radius (G M r hbar c lam twoA : Rat) (hG : G ≠ 0) (hc : c ≠ 0)
    (hK : twoA * twoA = G * M * r) (hP : twoA * twoA = lam * lam * (hbar * G / c)) :
    M * c * r = lam * lam * hbar := by
  have e : hbar * G / c * c = hbar * G := Rat.div_mul_cancel hc
  have h1 : G * (M * c * r - lam * lam * hbar) = 0 := by
    have : G * M * r * c = lam * lam * (hbar * G / c * c) := by rw [← hK, hP]; grind
    rw [e] at this
    grind
  rcases Rat.mul_eq_zero.mp h1 with h | h
  · exact absurd h hG
  · grind

/-- The test body's action `L = m r v` depends on its own mass: `L² c = lam² m² ħ G`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem test_body_action (m hbar G c lam twoA : Rat) (hc : c ≠ 0)
    (hP : twoA * twoA = lam * lam * (hbar * G / c)) :
    (m * twoA) * (m * twoA) * c = lam * lam * (m * m * hbar * G) := by
  have e : hbar * G / c * c = hbar * G := Rat.div_mul_cancel hc
  have : (m * twoA) * (m * twoA) * c = m * m * (lam * lam * (hbar * G / c * c)) := by
    have h2 : (m * twoA) * (m * twoA) = m * m * (twoA * twoA) := by grind
    rw [h2, hP]; grind
  rw [e] at this
  grind

/-- At one Planck unit the test body's action is `ħ` exactly when `m² G = ħ c`. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem action_is_hbar_iff (m hbar G c twoA : Rat) (hc : c ≠ 0) (hh : hbar ≠ 0)
    (hP : twoA * twoA = hbar * G / c) :
    (m * twoA) * (m * twoA) = hbar * hbar ↔ m * m * G = hbar * c := by
  have h1 := test_body_action m hbar G c 1 twoA hc (by rw [hP]; grind)
  constructor
  · intro h
    have : hbar * (m * m * G - hbar * c) = 0 := by rw [h] at h1; grind
    rcases Rat.mul_eq_zero.mp this with h | h
    · exact absurd h hh
    · grind
  · intro h
    have : c * ((m * twoA) * (m * twoA) - hbar * hbar) = 0 := by grind
    rcases Rat.mul_eq_zero.mp this with h | h
    · exact absurd h hc
    · grind

/-- Gauss-law circles in five spacetime dimensions, force `κ/r³`: `(r v)²` is the same at
every radius. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem gauss_five (m kappa r v : Rat) (hr : r ≠ 0)
    (h : m * (v * v) / r = kappa / (r * r * r)) : m * ((r * v) * (r * v)) = kappa := by
  have := circular_action m kappa r v hr h
  have hm2 : (m * r * v) * (m * r * v) = m * (m * ((r * v) * (r * v))) := by grind
  rw [hm2] at this
  by_cases hm : m = 0
  · rw [hm] at h
    have h3 : r * r * r ≠ 0 := by
      intro h0
      rcases Rat.mul_eq_zero.mp h0 with h | h
      · rcases Rat.mul_eq_zero.mp h with h | h <;> exact hr h
      · exact hr h
    have e2 : kappa / (r * r * r) * (r * r * r) = kappa := Rat.div_mul_cancel h3
    have : (0 : Rat) * (v * v) / r = 0 := by grind
    rw [hm]; grind
  · have h4 : m * (m * ((r * v) * (r * v)) - kappa) = 0 := by grind
    rcases Rat.mul_eq_zero.mp h4 with h | h
    · exact absurd h hm
    · grind

/-- Gauss-law circles in four spacetime dimensions, force `κ/r²`: `(r v)²` grows as `r`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem gauss_four (m kappa r v : Rat) (hr : r ≠ 0)
    (h : m * (v * v) / r = kappa / (r * r)) : m * ((r * v) * (r * v)) = kappa * r := by
  have h2 : r * r ≠ 0 := by
    intro h0; rcases Rat.mul_eq_zero.mp h0 with h | h <;> exact hr h
  have e1 : m * (v * v) / r * r = m * (v * v) := Rat.div_mul_cancel hr
  have e2 : kappa / (r * r) * (r * r) = kappa := Rat.div_mul_cancel h2
  have : m * (v * v) / r * r * r = kappa / (r * r) * (r * r) := by rw [h]; grind
  rw [e1, e2] at this
  grind

/-- Bohr comparison on a Kepler circle with `L = n ħ`: the radius is at least `ħ/(M c)`
exactly when `G m² ≤ n² ħ c`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem bohr_bound_iff (n m M G hbar c r : Rat) (hh : 0 < hbar) (hG : 0 < G) (hm : 0 < m)
    (hL : (n * hbar) * (n * hbar) = m * m * G * M * r) :
    hbar ≤ M * c * r ↔ G * (m * m) ≤ n * n * hbar * c := by
  have hGm : 0 < G * (m * m) := Rat.mul_pos hG (Rat.mul_pos hm hm)
  have key : G * (m * m) * (M * c * r) = hbar * (n * n * hbar * c) := by grind
  constructor
  · intro h
    have h1 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hGm)
    rw [key] at h1
    have h2 : (G * (m * m)) * hbar ≤ (n * n * hbar * c) * hbar := by grind
    exact Rat.le_of_mul_le_mul_right h2 hh
  · intro h
    have h1 := Rat.mul_le_mul_of_nonneg_left h (Rat.le_of_lt hh)
    have h2 : hbar * (G * (m * m)) ≤ (M * c * r) * (G * (m * m)) := by grind
    exact Rat.le_of_mul_le_mul_right h2 hGm

/-- At the matched radius the orbital speed obeys `v² ħ = G M² c`, that is `(v/c)² = G M²/(ħ c)`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem matched_speed (G M r v hbar c : Rat) (hK : v * v * r = G * M) (hr : M * c * r = hbar) :
    v * v * hbar = G * M * M * c := by
  rw [← hr]
  have : v * v * (M * c * r) = (v * v * r) * (M * c) := by grind
  rw [this, hK]
  grind

end NewtonLimitDynamics.Diagnostic.ArealBounds
