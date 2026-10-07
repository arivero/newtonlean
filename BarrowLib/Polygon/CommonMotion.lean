import BarrowLib.Polygon.ZeroForce

/-! Finite systems of bodies moving by impulse-then-drift cells, compared
through their relative positions and velocities. In every cell a supplied rule
changes each velocity, and a supplied motion map then moves each body for the
cell's duration. The superposition theorem shows that velocity changes shared
by all bodies, together with a shared initial displacement and velocity, add
one common motion to every body and leave the table of relative states fixed.

Source of these coordinate statements and derivations: the original English
statements and Lean proofs below, using the named finite library results.
This records project formalization authorship, not discovery or priority.
The uniform-motion map, the additive velocity change and impulses determined
by the relative table are explicit premises of each theorem. Compared systems
share one cell schedule, hence one time, and velocities compose by coordinate
vector addition. These are the finite coordinate forms used for Newton's Laws
Corollaries V and VI, whose statements and proofs are in their historical files
(1687 NATP00076 par20–23, 1713 NATP00081 par20–23). No post-Principia theorem
or completion is used.
-/
namespace NewtonLimitDynamics.Polygon.CommonMotion
open NewtonLimitDynamics TimeSubdivision

/-- A body's position and velocity at a cell boundary. -/
abbrev State := Point × Point

def stateEquiv (a b : State) : Prop := pointEquiv a.1 b.1 ∧ pointEquiv a.2 b.2
def stateAdd (a b : State) : State := (pointAdd a.1 b.1, pointAdd a.2 b.2)
def stateSub (a b : State) : State := (pointSub a.1 b.1, pointSub a.2 b.2)

/-- Entry `i j` is the state of body `i` relative to body `j`. -/
def relative {ι : Type} (S : ι → State) (i j : ι) : State := stateSub (S i) (S j)

/-- Impulses arise from the table of relative states alone: equivalent tables
give equivalent impulses. The cell index and the body stay available, so a
prescribed impulse history that ignores the table is included. -/
def RelativeKick {ι : Type} (kick : Nat → (ι → ι → State) → ι → Point) : Prop :=
  ∀ n (D D' : ι → ι → State), (∀ i j, stateEquiv (D i j) (D' i j)) →
    ∀ i, pointEquiv (kick n D i) (kick n D' i)

/-- Cell `n` changes body `i`'s velocity by `change`, which sees the current
relative table, then moves the body for `dt n` with the new velocity. -/
def run {ι : Type} (motion : Point → Point → Fraction → Point) (dt : Nat → Fraction)
    (change : Nat → (ι → ι → State) → ι → Point → Point) (S0 : ι → State) :
    Nat → ι → State
  | 0 => S0
  | n + 1 => fun i =>
      (motion (run motion dt change S0 n i).1
          (change n (relative (run motion dt change S0 n)) i (run motion dt change S0 n i).2)
          (dt n),
        change n (relative (run motion dt change S0 n)) i (run motion dt change S0 n i).2)

/-- A point starting from `g0` that receives only the common velocity changes
`h`, on the same cell schedule. -/
def commonRun (g0 : State) (dt : Nat → Fraction) (h : Nat → Point) : Nat → State
  | 0 => g0
  | n + 1 =>
      (pointAdd (commonRun g0 dt h n).1
          (pointScale (dt n) (pointAdd (commonRun g0 dt h n).2 (h n))),
        pointAdd (commonRun g0 dt h n).2 (h n))

/-- Elapsed time after `n` cells. -/
def elapsedTime (dt : Nat → Fraction) : Nat → Fraction
  | 0 => Fraction.ofInt 0
  | n + 1 => Fraction.add (elapsedTime dt n) (dt n)

/-- Every body of `S0` displaced by `c` and given the additional velocity `w`. -/
def boost {ι : Type} (S0 : ι → State) (c w : Point) : ι → State :=
  fun i => stateAdd (S0 i) (c, w)

theorem pointEquiv_refl (p : Point) : pointEquiv p p :=
  ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩

theorem stateEquiv_refl (a : State) : stateEquiv a a :=
  ⟨pointEquiv_refl _, pointEquiv_refl _⟩

theorem stateEquiv_symm {a b : State} (h : stateEquiv a b) : stateEquiv b a :=
  ⟨pointEquiv_symm h.1, pointEquiv_symm h.2⟩

theorem stateEquiv_trans {a b c : State} (h : stateEquiv a b) (k : stateEquiv b c) :
    stateEquiv a c :=
  ⟨pointEquiv_trans h.1 k.1, pointEquiv_trans h.2 k.2⟩

theorem stateSub_congr {a a' b b' : State} (ha : stateEquiv a a') (hb : stateEquiv b b') :
    stateEquiv (stateSub a b) (stateSub a' b') :=
  ⟨pointSub_congr ha.1 hb.1, pointSub_congr ha.2 hb.2⟩

theorem pointAdd_zero (p : Point) : pointEquiv (pointAdd p ZeroForce.zeroPoint) p := by
  constructor <;>
    simp only [pointAdd, ZeroForce.zeroPoint, Fraction.add, Fraction.equiv, Fraction.ofInt,
      Int.zero_mul, Int.mul_one, Int.add_zero]

theorem pointAdd_swap (a b c d : Point) :
    pointEquiv (pointAdd (pointAdd a b) (pointAdd c d))
      (pointAdd (pointAdd a c) (pointAdd b d)) := by
  constructor <;>
    simp only [pointAdd, Fraction.add, Fraction.equiv, Int.add_mul, Int.mul_add] <;>
    ac_nf <;> omega

/-- A shared displacement cancels from a difference. -/
theorem pointSub_add_common (a b g : Point) :
    pointEquiv (pointSub (pointAdd a g) (pointAdd b g)) (pointSub a b) := by
  constructor <;>
    simp only [pointSub, pointAdd, pointNeg, Fraction.add, Fraction.equiv,
      Int.add_mul, Int.mul_add, Int.neg_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem pointAdd_sub_cancel (a g : Point) :
    pointEquiv (pointSub (pointAdd a g) g) a := by
  constructor <;>
    simp only [pointSub, pointAdd, pointNeg, Fraction.add, Fraction.equiv,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem pointSub_add_add (a b x y : Point) :
    pointEquiv (pointSub (pointAdd a x) (pointAdd b y))
      (pointAdd (pointSub a b) (pointSub x y)) := by
  constructor <;>
    simp only [pointSub, pointAdd, pointNeg, Fraction.add, Fraction.equiv,
      Int.add_mul, Int.mul_add, Int.neg_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem pointScale_sub (d : Fraction) (x y : Point) :
    pointEquiv (pointSub (pointScale d x) (pointScale d y)) (pointScale d (pointSub x y)) := by
  constructor <;>
    simp only [pointSub, pointAdd, pointNeg, pointScale, Fraction.add, Fraction.mul,
      Fraction.equiv, Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg] <;>
    ac_nf <;> omega

theorem pointScale_add_left (a b : Fraction) (p : Point) :
    pointEquiv (pointScale (Fraction.add a b) p)
      (pointAdd (pointScale a p) (pointScale b p)) :=
  ⟨Fraction.add_mul a b p.1, Fraction.add_mul a b p.2⟩

theorem inertialAt_zero (c w : Point) :
    pointEquiv (ZeroForce.inertialAt c w (Fraction.ofInt 0)) c := by
  constructor <;>
    simp only [ZeroForce.inertialAt, pointAdd, pointScale, Fraction.add, Fraction.mul,
      Fraction.equiv, Fraction.ofInt, Int.zero_mul, Int.mul_one, Int.add_zero,
      Int.one_mul] <;> ac_rfl

theorem stateSub_add_common (a b g : State) :
    stateEquiv (stateSub (stateAdd a g) (stateAdd b g)) (stateSub a b) :=
  ⟨pointSub_add_common a.1 b.1 g.1, pointSub_add_common a.2 b.2 g.2⟩

/-- A common displacement and velocity leave the relative table unchanged. -/
theorem relative_boost {ι : Type} (S0 : ι → State) (c w : Point) (i j : ι) :
    stateEquiv (relative (boost S0 c w) i j) (relative S0 i j) :=
  stateSub_add_common _ _ _

/-- One velocity change of the form `(v + kick) + h`, compared between two bodies. -/
theorem change_difference {ι : Type} (change : Nat → (ι → ι → State) → ι → Point → Point)
    (kick : Nat → (ι → ι → State) → ι → Point) (h : Nat → Point)
    (hc : ∀ n D i v, pointEquiv (change n D i v) (pointAdd (pointAdd v (kick n D i)) (h n)))
    (n : Nat) (D : ι → ι → State) (i j : ι) (vi vj : Point) :
    pointEquiv (pointSub (change n D i vi) (change n D j vj))
      (pointAdd (pointSub vi vj) (pointSub (kick n D i) (kick n D j))) :=
  pointEquiv_trans (pointSub_congr (hc n D i vi) (hc n D j vj))
    (pointEquiv_trans (pointSub_add_common _ _ _) (pointSub_add_add _ _ _ _))

/-- Uniform motion of two bodies for one duration, compared. -/
theorem motion_difference (motion : Point → Point → Fraction → Point)
    (hI : ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t))
    (pi pj vi vj : Point) (t : Fraction) :
    pointEquiv (pointSub (motion pi vi t) (motion pj vj t))
      (pointAdd (pointSub pi pj) (pointScale t (pointSub vi vj))) :=
  pointEquiv_trans (pointSub_congr (hI pi vi t) (hI pj vj t))
    (pointEquiv_trans (pointSub_add_add _ _ _ _)
      (pointAdd_congr (pointEquiv_refl _) (pointScale_sub _ _ _)))

/-- The relative table evolves by itself. Two runs with the same impulse rule,
each adding its own common velocity changes, keep equal relative tables at
every cell boundary when they start with equal relative tables. -/
theorem relative_autonomous {ι : Type}
    (motion : Point → Point → Fraction → Point) (dt : Nat → Fraction)
    (kick : Nat → (ι → ι → State) → ι → Point)
    (cA cB : Nat → (ι → ι → State) → ι → Point → Point) (hA hB : Nat → Point)
    (A0 B0 : ι → State)
    (hI : ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t))
    (hK : RelativeKick kick)
    (hcA : ∀ n D i v, pointEquiv (cA n D i v) (pointAdd (pointAdd v (kick n D i)) (hA n)))
    (hcB : ∀ n D i v, pointEquiv (cB n D i v) (pointAdd (pointAdd v (kick n D i)) (hB n)))
    (h0 : ∀ i j, stateEquiv (relative A0 i j) (relative B0 i j)) :
    ∀ n i j, stateEquiv (relative (run motion dt cA A0 n) i j)
      (relative (run motion dt cB B0 n) i j) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro i j
    have hvel : pointEquiv
        (pointSub (cA n (relative (run motion dt cA A0 n)) i (run motion dt cA A0 n i).2)
          (cA n (relative (run motion dt cA A0 n)) j (run motion dt cA A0 n j).2))
        (pointSub (cB n (relative (run motion dt cB B0 n)) i (run motion dt cB B0 n i).2)
          (cB n (relative (run motion dt cB B0 n)) j (run motion dt cB B0 n j).2)) :=
      pointEquiv_trans (change_difference cA kick hA hcA n _ i j _ _)
        (pointEquiv_trans
          (pointAdd_congr (ih i j).2 (pointSub_congr (hK n _ _ ih i) (hK n _ _ ih j)))
          (pointEquiv_symm (change_difference cB kick hB hcB n _ i j _ _)))
    refine And.intro ?_ hvel
    exact pointEquiv_trans (motion_difference motion hI _ _ _ _ _)
      (pointEquiv_trans (pointAdd_congr (ih i j).1 (pointScale_congr _ hvel))
        (pointEquiv_symm (motion_difference motion hI _ _ _ _ _)))

theorem stateAdd_sub_cancel (a g : State) :
    stateEquiv (stateSub (stateAdd a g) g) a :=
  ⟨pointAdd_sub_cancel a.1 g.1, pointAdd_sub_cancel a.2 g.2⟩

/-- Superposition of a common motion. Run `urged` starts from `T0`, each body
displaced from `S0` by the common state `g0`, and changes every velocity by its
own impulse plus the common change `h n`. Run `free` starts from `S0` with
the same impulse rule and no common change. At every cell boundary each urged
body is the free body plus the common motion generated by `g0` and `h` alone. -/
theorem common_superposition {ι : Type}
    (motion : Point → Point → Fraction → Point) (dt : Nat → Fraction)
    (kick : Nat → (ι → ι → State) → ι → Point)
    (free urged : Nat → (ι → ι → State) → ι → Point → Point)
    (h : Nat → Point) (g0 : State) (S0 T0 : ι → State)
    (hI : ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t))
    (hK : RelativeKick kick)
    (hfree : ∀ n D i v, pointEquiv (free n D i v) (pointAdd v (kick n D i)))
    (hurged : ∀ n D i v,
      pointEquiv (urged n D i v) (pointAdd (pointAdd v (kick n D i)) (h n)))
    (h0 : ∀ i, stateEquiv (T0 i) (stateAdd (S0 i) g0)) :
    ∀ n i, stateEquiv (run motion dt urged T0 n i)
      (stateAdd (run motion dt free S0 n i) (commonRun g0 dt h n)) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro i
    have hrel : ∀ a b, stateEquiv (relative (run motion dt urged T0 n) a b)
        (relative (run motion dt free S0 n) a b) := fun a b =>
      stateEquiv_trans (stateSub_congr (ih a) (ih b)) (stateSub_add_common _ _ _)
    have hk := hK n _ _ hrel i
    have hv : pointEquiv
        (urged n (relative (run motion dt urged T0 n)) i (run motion dt urged T0 n i).2)
        (pointAdd (free n (relative (run motion dt free S0 n)) i (run motion dt free S0 n i).2)
          (pointAdd (commonRun g0 dt h n).2 (h n))) := by
      refine pointEquiv_trans (hurged _ _ _ _) ?_
      refine pointEquiv_trans
        (pointAdd_congr (pointAdd_congr (ih i).2 hk) (pointEquiv_refl _)) ?_
      refine pointEquiv_trans (pointAdd_assoc _ _ _) ?_
      refine pointEquiv_trans (pointAdd_swap _ _ _ _) ?_
      exact pointAdd_congr (pointEquiv_symm (hfree _ _ _ _)) (pointEquiv_refl _)
    refine And.intro ?_ hv
    refine pointEquiv_trans (hI _ _ _) ?_
    refine pointEquiv_trans (pointAdd_congr (ih i).1 (pointScale_congr (dt n) hv)) ?_
    refine pointEquiv_trans
      (pointAdd_congr (pointEquiv_refl _) (pointScale_add _ _ _)) ?_
    refine pointEquiv_trans (pointAdd_swap _ _ _ _) ?_
    exact pointAdd_congr (pointEquiv_symm (hI _ _ _)) (pointEquiv_refl _)

/-- Under the superposition premises the table of relative states of the two
runs agrees at every cell boundary. -/
theorem relative_unchanged {ι : Type}
    (motion : Point → Point → Fraction → Point) (dt : Nat → Fraction)
    (kick : Nat → (ι → ι → State) → ι → Point)
    (free urged : Nat → (ι → ι → State) → ι → Point → Point)
    (h : Nat → Point) (g0 : State) (S0 T0 : ι → State)
    (hI : ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t))
    (hK : RelativeKick kick)
    (hfree : ∀ n D i v, pointEquiv (free n D i v) (pointAdd v (kick n D i)))
    (hurged : ∀ n D i v,
      pointEquiv (urged n D i v) (pointAdd (pointAdd v (kick n D i)) (h n)))
    (h0 : ∀ i, stateEquiv (T0 i) (stateAdd (S0 i) g0)) (n : Nat) (i j : ι) :
    stateEquiv (relative (run motion dt urged T0 n) i j)
      (relative (run motion dt free S0 n) i j) :=
  have hs := common_superposition motion dt kick free urged h g0 S0 T0 hI hK hfree hurged h0 n
  stateEquiv_trans (stateSub_congr (hs i) (hs j)) (stateSub_add_common _ _ _)

/-- Under the superposition premises each urged body, taken relative to the
common motion, has the free body's state. -/
theorem relative_to_common {ι : Type}
    (motion : Point → Point → Fraction → Point) (dt : Nat → Fraction)
    (kick : Nat → (ι → ι → State) → ι → Point)
    (free urged : Nat → (ι → ι → State) → ι → Point → Point)
    (h : Nat → Point) (g0 : State) (S0 T0 : ι → State)
    (hI : ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t))
    (hK : RelativeKick kick)
    (hfree : ∀ n D i v, pointEquiv (free n D i v) (pointAdd v (kick n D i)))
    (hurged : ∀ n D i v,
      pointEquiv (urged n D i v) (pointAdd (pointAdd v (kick n D i)) (h n)))
    (h0 : ∀ i, stateEquiv (T0 i) (stateAdd (S0 i) g0)) (n : Nat) (i : ι) :
    stateEquiv (stateSub (run motion dt urged T0 n i) (commonRun g0 dt h n))
      (run motion dt free S0 n i) :=
  stateEquiv_trans
    (stateSub_congr
      (common_superposition motion dt kick free urged h g0 S0 T0 hI hK hfree hurged h0 n i)
      (stateEquiv_refl _))
    (stateAdd_sub_cancel _ _)

/-- With no common velocity change the common motion is uniform and
rectilinear: position `c + elapsed * w` and constant velocity `w`. -/
theorem commonRun_uniform (c w : Point) (dt : Nat → Fraction) (n : Nat) :
    stateEquiv (commonRun (c, w) dt (fun _ => ZeroForce.zeroPoint) n)
      (ZeroForce.inertialAt c w (elapsedTime dt n), w) := by
  induction n with
  | zero =>
    exact ⟨pointEquiv_symm (inertialAt_zero c w), (pointEquiv_refl _)⟩
  | succ n ih =>
    have hv : pointEquiv
        (pointAdd (commonRun (c, w) dt (fun _ => ZeroForce.zeroPoint) n).2 ZeroForce.zeroPoint)
        w :=
      pointEquiv_trans (pointAdd_zero _) ih.2
    refine And.intro ?_ hv
    refine pointEquiv_trans (pointAdd_congr ih.1 (pointScale_congr (dt n) hv)) ?_
    refine pointEquiv_trans (pointAdd_assoc _ _ _) ?_
    exact pointAdd_congr (pointEquiv_refl _)
      (pointEquiv_symm (pointScale_add_left _ _ _))

end NewtonLimitDynamics.Polygon.CommonMotion
