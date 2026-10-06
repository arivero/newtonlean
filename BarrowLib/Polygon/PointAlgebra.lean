import BarrowLib.Common.RationalMagnitudes

namespace NewtonLimitDynamics.Polygon.TimeSubdivision

open NewtonLimitDynamics

/-- A two-dimensional coordinate point whose components are signed rational
    representatives. -/
abbrev Point := Fraction × Fraction

def pointAdd (p q : Point) : Point := (Fraction.add p.1 q.1, Fraction.add p.2 q.2)
def pointScale (d : Fraction) (p : Point) : Point :=
  (Fraction.mul d p.1, Fraction.mul d p.2)
def pointNeg (p : Point) : Point :=
  (⟨-p.1.num, p.1.den, p.1.den_pos⟩, ⟨-p.2.num, p.2.den, p.2.den_pos⟩)
def pointSub (p q : Point) : Point := pointAdd p (pointNeg q)

def pointEquiv (p q : Point) : Prop :=
  Fraction.equiv p.1 q.1 ∧ Fraction.equiv p.2 q.2

instance (a b : Fraction) : Decidable (Fraction.equiv a b) :=
  if h : a.num * b.den = b.num * a.den then isTrue h else isFalse h
instance (p q : Point) : Decidable (pointEquiv p q) :=
  if h₁ : Fraction.equiv p.1 q.1 then
    if h₂ : Fraction.equiv p.2 q.2 then isTrue ⟨h₁, h₂⟩
    else isFalse (fun h => h₂ h.2)
  else isFalse (fun h => h₁ h.1)

-- Point equivalence lemmas shared by the Polygon modules.

theorem pointEquiv_symm {p q : Point} (h : pointEquiv p q) : pointEquiv q p :=
  ⟨Fraction.equiv_symm h.1, Fraction.equiv_symm h.2⟩

theorem pointEquiv_trans {p q r : Point} (h : pointEquiv p q) (k : pointEquiv q r) :
    pointEquiv p r :=
  ⟨Fraction.equiv_trans h.1 k.1, Fraction.equiv_trans h.2 k.2⟩

theorem pointAdd_congr {p p' q q' : Point}
    (hp : pointEquiv p p') (hq : pointEquiv q q') :
    pointEquiv (pointAdd p q) (pointAdd p' q') := by
  constructor
  · exact Fraction.equiv_trans (Fraction.add_equiv_right q.1 hp.1)
      (Fraction.equiv_trans (Fraction.add_comm p'.1 q.1)
        (Fraction.equiv_trans (Fraction.add_equiv_right p'.1 hq.1)
          (Fraction.add_comm q'.1 p'.1)))
  · exact Fraction.equiv_trans (Fraction.add_equiv_right q.2 hp.2)
      (Fraction.equiv_trans (Fraction.add_comm p'.2 q.2)
        (Fraction.equiv_trans (Fraction.add_equiv_right p'.2 hq.2)
          (Fraction.add_comm q'.2 p'.2)))

theorem pointScale_congr (d : Fraction) {p q : Point} (h : pointEquiv p q) :
    pointEquiv (pointScale d p) (pointScale d q) :=
  ⟨Fraction.mul_equiv_left d h.1, Fraction.mul_equiv_left d h.2⟩

/-- Scaling respects rational value equivalence in both arguments. -/
theorem pointScale_ratio_congr {d e : Fraction} {p q : Point}
    (hde : Fraction.equiv d e) (hpq : pointEquiv p q) :
    pointEquiv (pointScale d p) (pointScale e q) :=
  ⟨Fraction.mul_equiv hde hpq.1, Fraction.mul_equiv hde hpq.2⟩

theorem pointNeg_congr {p q : Point} (hpq : pointEquiv p q) :
    pointEquiv (pointNeg p) (pointNeg q) := by
  constructor
  · change -p.1.num * q.1.den = -q.1.num * p.1.den
    simpa only [Int.neg_mul] using congrArg Neg.neg hpq.1
  · change -p.2.num * q.2.den = -q.2.num * p.2.den
    simpa only [Int.neg_mul] using congrArg Neg.neg hpq.2

theorem pointSub_congr {p p' q q' : Point}
    (hpp' : pointEquiv p p') (hqq' : pointEquiv q q') :
    pointEquiv (pointSub p q) (pointSub p' q') :=
  pointAdd_congr hpp' (pointNeg_congr hqq')

theorem pointSub_zero (p : Point) :
    pointEquiv (pointSub p (Fraction.ofInt 0,Fraction.ofInt 0)) p := by
  constructor <;> simp only [pointSub,pointAdd,pointNeg,Fraction.equiv,Fraction.add,
    Fraction.ofInt,Int.neg_zero,Int.zero_mul,Int.mul_one,Int.add_zero]


def det (p q : Point) : Fraction :=
  Fraction.add (Fraction.mul p.1 q.2) (⟨-(Fraction.mul p.2 q.1).num,
    (Fraction.mul p.2 q.1).den, (Fraction.mul p.2 q.1).den_pos⟩)

theorem det_add_right (x v w : Point) :
    Fraction.equiv (det x (pointAdd v w)) (Fraction.add (det x v) (det x w)) := by
  unfold Fraction.equiv det pointAdd Fraction.add Fraction.mul
  dsimp
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

theorem pointAdd_comm (p q : Point) : pointEquiv (pointAdd p q) (pointAdd q p) :=
  ⟨Fraction.add_comm _ _, Fraction.add_comm _ _⟩

theorem pointAdd_assoc (p q r : Point) :
    pointEquiv (pointAdd (pointAdd p q) r) (pointAdd p (pointAdd q r)) :=
  ⟨Fraction.add_assoc _ _ _,Fraction.add_assoc _ _ _⟩

theorem pointScale_add (d : Fraction) (p q : Point) :
    pointEquiv (pointScale d (pointAdd p q))
      (pointAdd (pointScale d p) (pointScale d q)) :=
  ⟨Fraction.mul_add _ _ _,Fraction.mul_add _ _ _⟩

theorem pointSub_add_self_left_equiv (x y : Point) :
    pointEquiv (pointSub (pointAdd x y) x) y := by
  constructor <;>
    simp only [pointSub,pointAdd,pointNeg,Fraction.add,Fraction.equiv,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

theorem det_congr {p p' q q' : Point}
    (hp : pointEquiv p p') (hq : pointEquiv q q') :
    Fraction.equiv (det p q) (det p' q') := by
  have hn : Fraction.equiv
      (⟨-(Fraction.mul p.2 q.1).num,(Fraction.mul p.2 q.1).den,
        (Fraction.mul p.2 q.1).den_pos⟩ : Fraction)
      ⟨-(Fraction.mul p'.2 q'.1).num,(Fraction.mul p'.2 q'.1).den,
        (Fraction.mul p'.2 q'.1).den_pos⟩ := by
    simpa only [Fraction.equiv,Int.neg_mul] using
      congrArg Neg.neg (Fraction.mul_equiv hp.2 hq.1)
  exact Fraction.add_equiv (Fraction.mul_equiv hp.1 hq.2) hn

theorem det_add_left (q x y : Point) :
    Fraction.equiv (det (pointAdd x y) q) (Fraction.add (det x q) (det y q)) := by
  simp only [det,pointAdd,Fraction.add,Fraction.mul,Fraction.equiv,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

theorem det_scale_left (d : Fraction) (q x : Point) :
    Fraction.equiv (det (pointScale d x) q) (Fraction.mul d (det x q)) := by
  simp only [det,pointScale,Fraction.add,Fraction.mul,Fraction.equiv,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

theorem det_scale_right (d : Fraction) (p x : Point) :
    Fraction.equiv (det p (pointScale d x)) (Fraction.mul d (det p x)) := by
  simp only [det,pointScale,Fraction.add,Fraction.mul,Fraction.equiv,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

theorem det_self (x : Point) : Fraction.equiv (det x x) (Fraction.ofInt 0) := by
  simp only [det,Fraction.add,Fraction.mul,Fraction.ofInt,Fraction.equiv,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

/-- The two transverse coordinates recover a point after multiplication by
    the determinant of the directions. No division is used. -/
theorem det_coordinate_resolution (u v x : Point) :
    pointEquiv (pointScale (det u v) x)
      (pointSub (pointScale (det x v) u) (pointScale (det x u) v)) := by
  constructor <;>
    simp only [pointEquiv,pointScale,pointSub,pointNeg,pointAdd,det,Fraction.equiv,Fraction.add,
      Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;>
    ac_nf <;> omega

/-- Two independent transverse coordinates determine the point. -/
theorem det_coordinates_injective (u v : Point) (h : (det u v).num ≠ 0)
    {x y : Point} (hx : Fraction.equiv (det x v) (det y v))
    (hy : Fraction.equiv (det x u) (det y u)) : pointEquiv x y := by
  have he := pointEquiv_trans (det_coordinate_resolution u v x)
    (pointEquiv_trans
      (pointSub_congr
        (pointScale_ratio_congr hx ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
        (pointScale_ratio_congr hy ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))
      (pointEquiv_symm (det_coordinate_resolution u v y)))
  exact ⟨Fraction.mul_equiv_cancel_left (det u v) h he.1,
    Fraction.mul_equiv_cancel_left (det u v) h he.2⟩

/-- Signed doubled determinant sum for p -> B -> D -> C -> p. -/
def closedBoundaryTwice (p b d c : Point) : Fraction :=
  Fraction.add (Fraction.add (det p b) (det b d))
    (Fraction.add (det d c) (det c p))


end NewtonLimitDynamics.Polygon.TimeSubdivision

namespace NewtonLimitDynamics.Polygon.HarmonicStability
open NewtonLimitDynamics
open TimeSubdivision
def dot (p q : Point) : Fraction :=
  Fraction.add (Fraction.mul p.1 q.1) (Fraction.mul p.2 q.2)

end NewtonLimitDynamics.Polygon.HarmonicStability
