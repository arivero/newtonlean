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
