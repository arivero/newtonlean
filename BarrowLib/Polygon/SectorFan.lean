import BarrowLib.Polygon.RectangleContent
import BarrowLib.Polygon.CentralSchedule
import BarrowLib.Polygon.BoundedIteration
import BarrowLib.Polygon.RationalIntervals

/-! Actual finite sector unions, distinguished from fans with multiplicity.
All vertices lie in the positive horizontal half-plane and consecutive
determinants are nonnegative. These local geometric conditions derive the
radial cuts separating successive triangles; separation is not a premise.
Area itself remains a supplied partial geometric relation, extended from the
rectangle convention by triangle areas and additivity across nonzero radial
lines. No curved sector or limiting area is postulated or constructed here. -/
namespace NewtonLimitDynamics.Polygon.SectorFan
open NewtonLimitDynamics TimeSubdivision PolygonFanArea

/-- The filled triangle with vertices the fixed origin, `p` and `q`. -/
def Triangle (p q x : Point) : Prop :=
  ∃ u v : Fraction, 0 ≤ u.num ∧ 0 ≤ v.num ∧
    Fraction.le (Fraction.add u v) (Fraction.ofInt 1) ∧
    pointEquiv x (pointAdd (pointScale u p) (pointScale v q))

def Region (p : Nat → Point) (n : Nat) (x : Point) : Prop :=
  ∃ i, i < n ∧ Triangle (p i) (p (i+1)) x

def areaSum (p : Nat → Point) (n : Nat) : Fraction :=
  sum (fun i => (det (p i) (p (i+1))).half) n

/-- Additional elementary geometric area rules. The triangle normalization
and radial additivity are explicit premises, not consequences of the existing
rectangle-only convention. The nonzero cut is essential: the zero vector
would place every set on both sides and make additivity inconsistent. -/
structure AreaRules extends RectangleContent.AreaRules where
  triangle : ∀ p q, 0 ≤ (det p q).num → HasArea (Triangle p q) (det p q).half
  radial_union : ∀ U V A B r, (r.1.num ≠ 0 ∨ r.2.num ≠ 0) →
    (∀ x, U x → 0 ≤ (det x r).num) →
    (∀ x, V x → 0 ≤ (det r x).num) →
    HasArea U A → HasArea V B → HasArea (fun x => U x ∨ V x) (Fraction.add A B)

def slope (p : Point) (hp : 0 < p.1.num) : Fraction :=
  ⟨p.2.num * p.1.den, p.2.den * p.1.num, Int.mul_pos p.2.den_pos hp⟩

theorem slope_order (p q : Point) (hp : 0 < p.1.num) (hq : 0 < q.1.num) :
    Fraction.le (slope p hp) (slope q hq) ↔ 0 ≤ (det p q).num := by
  simp only [slope, Fraction.le, det, Fraction.add, Fraction.mul,
    Int.neg_mul, Int.mul_neg]
  ac_nf
  omega

/-- Local orientation propagates through every pair of rays in a common
positive half-plane. A polygon winding around the origin need not satisfy
this half-plane premise. -/
theorem pairwise_orientation (p : Nat → Point) (n : Nat)
    (hp : ∀ i, i ≤ n → 0 < (p i).1.num)
    (hc : ∀ i, i < n → 0 ≤ (det (p i) (p (i+1))).num) :
    ∀ i j, i ≤ j → j ≤ n → 0 ≤ (det (p i) (p j)).num := by
  intro i j
  induction j generalizing i with
  | zero =>
    intro hij _
    have hi : i = 0 := by omega
    subst i
    exact Fraction.nonnegative_equiv (det_self _) (by decide)
  | succ j ih =>
    intro hij hj
    by_cases he : i = j+1
    · subst i
      exact Fraction.nonnegative_equiv (det_self _) (by decide)
    · have hi : i ≤ j := by omega
      have hleft := (slope_order (p i) (p j) (hp i (by omega)) (hp j (by omega))).mpr
        (ih i hi (by omega))
      have hright := (slope_order (p j) (p (j+1)) (hp j (by omega)) (hp (j+1) hj)).mpr
        (hc j (by omega))
      exact (slope_order (p i) (p (j+1)) (hp i (by omega)) (hp (j+1) hj)).mp
        (Fraction.magnitudes.le_trans hleft hright)

theorem triangle_left (p q r x : Point) (hx : Triangle p q x)
    (hp : 0 ≤ (det p r).num) (hq : 0 ≤ (det q r).num) :
    0 ≤ (det x r).num := by
  obtain ⟨u,v,hu,hv,_,he⟩ := hx
  have hd := Fraction.equiv_trans
    (TimeSubdivision.det_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
    (Fraction.equiv_trans (det_add_left r _ _)
      (Fraction.add_equiv (det_scale_left u r p) (det_scale_left v r q)))
  exact Fraction.nonnegative_equiv hd
    (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hu hp)
      (Fraction.nonnegative_mul _ _ hv hq))

theorem triangle_right (p q r x : Point) (hx : Triangle p q x)
    (hp : 0 ≤ (det r p).num) (hq : 0 ≤ (det r q).num) :
    0 ≤ (det r x).num := by
  obtain ⟨u,v,hu,hv,_,he⟩ := hx
  have hd := Fraction.equiv_trans
    (TimeSubdivision.det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ he)
    (Fraction.equiv_trans (det_add_right r _ _)
      (Fraction.add_equiv (det_scale_right u r p) (det_scale_right v r q)))
  exact Fraction.nonnegative_equiv hd
    (Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hu hp)
      (Fraction.nonnegative_mul _ _ hv hq))

theorem region_succ (p : Nat → Point) (n : Nat) (x : Point) :
    Region p (n+1) x ↔ Region p n x ∨ Triangle (p n) (p (n+1)) x := by
  constructor
  · rintro ⟨i,hi,hx⟩
    by_cases h : i < n
    · exact Or.inl ⟨i,h,hx⟩
    · have he : i = n := by omega
      subst i
      exact Or.inr hx
  · rintro (⟨i,hi,hx⟩ | hx)
    · exact ⟨i,by omega,hx⟩
    · exact ⟨n,by omega,hx⟩

/-- The represented triangle union has the sum of its triangle areas.
Radial separation follows from the local half-plane and orientation data.
No multiplicity or nonoverlap assertion is assumed in the theorem. -/
theorem region_area (area : AreaRules) (p : Nat → Point) (n : Nat)
    (hp : ∀ i, i ≤ n → 0 < (p i).1.num)
    (hc : ∀ i, i < n → 0 ≤ (det (p i) (p (i+1))).num) :
    area.HasArea (Region p n) (areaSum p n) := by
  induction n with
  | zero =>
    apply area.congr_set (fun _ => False) _ _ _ area.empty
    intro x
    simp only [Region, Nat.not_lt_zero, false_and, exists_false]
  | succ n ih =>
    have hprev := ih (fun i hi => hp i (by omega)) (fun i hi => hc i (by omega))
    have hlast := area.triangle (p n) (p (n+1)) (hc n (by omega))
    have hordered := pairwise_orientation p (n+1) hp hc
    have hu := area.radial_union _ _ _ _ (p n) (Or.inl (Int.ne_of_gt (hp n (by omega))))
      ?_ ?_ hprev hlast
    · exact area.congr_set _ _ _ (fun x => (region_succ p n x).symm) hu
    · intro x hx
      obtain ⟨i,hi,hx⟩ := hx
      exact triangle_left _ _ _ x hx
        (hordered i n (by omega) (by omega)) (hordered (i+1) n (by omega) (by omega))
    · intro x hx
      exact triangle_right _ _ _ x hx
        (Fraction.nonnegative_equiv (det_self _) (by decide)) (hc n (by omega))

def vertices (a : CentralSchedule.Field) (h : Fraction) (s : Point × Point) (i : Nat) : Point :=
  (BoundedIteration.run a h s i).1

theorem run_momentum (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (h : Fraction) (s : Point × Point) (i : Nat) :
    Fraction.equiv (CentralSchedule.momentum (BoundedIteration.run a h s i))
      (CentralSchedule.momentum s) := by
  induction i with
  | zero => exact Fraction.equiv_refl _
  | succ i ih =>
    exact Fraction.equiv_trans
      (CentralSchedule.cell_momentum a ha h (BoundedIteration.run a h s i)) ih

theorem central_triangle (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (h : Fraction) (s : Point × Point) (i : Nat) :
    Fraction.equiv (det (vertices a h s i) (vertices a h s (i+1)))
      (Fraction.mul h (CentralSchedule.momentum s)) :=
  Fraction.equiv_trans
    (CentralSchedule.det_cell_area (BoundedIteration.run a h s i).1
      (BoundedIteration.run a h s i).2 h)
    (Fraction.mul_equiv_left h (run_momentum a ha h s i))

theorem central_area_sum (a : CentralSchedule.Field) (ha : CentralSchedule.central a)
    (h : Fraction) (s : Point × Point) (n : Nat) :
    Fraction.equiv (areaSum (vertices a h s) n)
      (Fraction.mul (BoundedIteration.time h n) (CentralSchedule.momentum s)).half := by
  have hs := sum_congr _ _ (fun i =>
    RationalIntervals.half_equiv (central_triangle a ha h s i)) n
  apply Fraction.equiv_trans hs
  apply Fraction.equiv_trans (sum_constant (Fraction.mul h (CentralSchedule.momentum s)).half n)
  simp only [BoundedIteration.time,Fraction.equiv,Fraction.half,Fraction.mul,Fraction.ofInt]
  ac_nf

/-- Newton's actual recursively constructed central-impulse polygon has an
ordinary union area proportional to its elapsed time on this local sector.
The half-plane clause is geometric; no triangle-area equality or union-area
conclusion is included in it. -/
theorem central_region_area (area : AreaRules) (a : CentralSchedule.Field)
    (ha : CentralSchedule.central a) (h : Fraction) (hh : 0 ≤ h.num)
    (s : Point × Point) (hs : 0 ≤ (CentralSchedule.momentum s).num) (n : Nat)
    (hp : ∀ i, i ≤ n → 0 < (vertices a h s i).1.num) :
    area.HasArea (Region (vertices a h s) n)
      (Fraction.mul (BoundedIteration.time h n) (CentralSchedule.momentum s)).half :=
  area.congr_value _ _ _ (central_area_sum a ha h s n)
    (region_area area _ n hp (fun i _ =>
      Fraction.nonnegative_equiv (central_triangle a ha h s i)
        (Fraction.nonnegative_mul _ _ hh hs)))

end NewtonLimitDynamics.Polygon.SectorFan
