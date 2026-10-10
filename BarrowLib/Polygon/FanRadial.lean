import BarrowLib.Polygon.TriangleExchange
import BarrowLib.Common.FiniteCrossing

/-! Rational ray crossings and radial caps for positive finite fans.
Source: the original English statements and finite coordinate proofs below.
This records a project derivation without historical textual attribution,
discovery or priority. Crossings concern finite rational edges, with no real
completion or continuous intermediate-value theorem. Area is not used.
-/

namespace NewtonLimitDynamics.Polygon.FanRadial
open NewtonLimitDynamics TimeSubdivision ConvexCover SupportingTangents RadialSector
open SectorFan TriangleExchange

def height (s : Fraction) (z : Point) : Fraction :=
  det (ray (Fraction.ofInt 1) s) z

theorem height_lerp (s ell : Fraction) (p q : Point) :
    Fraction.equiv (height s (lerp ell p q))
      (affine ell (height s p) (height s q)) := by
  apply Fraction.equiv_trans (det_add_right (ray (Fraction.ofInt 1) s) _ _)
  exact Fraction.add_equiv
    (det_scale_right (complement ell) (ray (Fraction.ofInt 1) s) p)
    (det_scale_right ell (ray (Fraction.ofInt 1) s) q)

theorem height_zero_ray (s : Fraction) (z : Point)
    (h : Fraction.equiv (height s z) (Fraction.ofInt 0)) :
    pointEquiv z (ray z.1 s) := by
  have hd : Fraction.equiv (det z (ray (Fraction.ofInt 1) s)) (Fraction.ofInt 0) := by
    apply Fraction.equiv_trans (det_swap_neg _ _)
    have hz : (height s z).num = 0 := by
      simpa only [Fraction.equiv,Fraction.ofInt,Int.mul_one,Int.zero_mul] using h
    simp only [HarmonicStability.negF,Fraction.equiv,Fraction.ofInt,Int.mul_one,Int.zero_mul]
    change -(height s z).num = 0
    omega
  have hr : 0 < (ray (Fraction.ofInt 1) s).1.num := by exact Int.zero_lt_one
  have he := collinear_scale z (ray (Fraction.ofInt 1) s) hr hd
  apply pointEquiv_trans he
  have hq : Fraction.equiv (Fraction.quotient z.1 (Fraction.ofInt 1) (by decide)) z.1 := by
    simp only [Fraction.quotient,Fraction.equiv,Fraction.ofInt,Int.mul_one,Int.one_mul]
  exact pointEquiv_trans (scale_ray _ _ _) (ray_congr_radius s
    (Fraction.equiv_trans (by
      change Fraction.equiv (Fraction.mul (Fraction.quotient z.1 (Fraction.ofInt 1) _) (Fraction.ofInt 1)) _
      simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.mul_one,Int.one_mul]) hq))

theorem ray_height_zero (s R : Fraction) :
    Fraction.equiv (height s (ray R s)) (Fraction.ofInt 0) := by
  simp only [height,ray,det,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,
    Int.one_mul,Int.mul_one,Int.zero_mul,Int.mul_zero]
  ac_nf
  omega

theorem lerp_first_positive (u : Fraction) (hu : UnitInterval u) (p q : Point)
    (hp : 0 < p.1.num) (hq : 0 < q.1.num) :
    0 < (lerp u p q).1.num := by
  by_cases h : Fraction.le p.1 q.1
  · exact positive_of_le _ _ hp (affine_between u p.1 q.1 hu h).1
  · have hr : Fraction.le q.1 p.1 := by unfold Fraction.le at *; omega
    have hb := (affine_between (complement u) q.1 p.1
      (complement_interval u hu) hr).1
    exact positive_of_le _ _ hq
      (Fraction.le_equiv_right hb (Fraction.equiv_symm (lerp_swap u p q).1))

theorem ray_lerp_radius (u R S s : Fraction) :
    pointEquiv (lerp u (ray R s) (ray S s)) (ray (affine u R S) s) := by
  constructor
  · exact Fraction.equiv_refl _
  · simp only [lerp,ray,affine,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
      Int.add_mul,Int.mul_add]
    ac_nf

/-- Every point on the same ray between two rational points is a convex
interpolation of them, including equal radii and reversed radial order. -/
theorem ray_between (s : Fraction) (a x b : Point)
    (ha : Fraction.equiv (height s a) (Fraction.ofInt 0))
    (hx : Fraction.equiv (height s x) (Fraction.ofInt 0))
    (hb : Fraction.equiv (height s b) (Fraction.ofInt 0))
    (h : FanIntervalChain.Between a.1.toRat x.1.toRat b.1.toRat) :
    ∃ u, UnitInterval u ∧ pointEquiv x (lerp u a b) := by
  have hc : (Fraction.le a.1 x.1 ∧ Fraction.le x.1 b.1) ∨
      (Fraction.le x.1 a.1 ∧ Fraction.le b.1 x.1) := by
    rcases h with h | h
    · exact Or.inl ⟨(Fraction.le_iff_toRat _ _).mpr h.1,
        (Fraction.le_iff_toRat _ _).mpr h.2⟩
    · exact Or.inr ⟨(Fraction.le_iff_toRat _ _).mpr h.2,
        (Fraction.le_iff_toRat _ _).mpr h.1⟩
  obtain ⟨u,hu,he⟩ := affine_crossing a.1 b.1 x.1 x.1 hc
  refine ⟨u,hu,pointEquiv_trans (height_zero_ray s x hx) (pointEquiv_symm ?_)⟩
  have hs := Fraction.equiv_trans he (affine_constant u x.1)
  have ht : pointEquiv (lerp u a b) (lerp u (ray a.1 s) (ray b.1 s)) :=
    pointAdd_congr (pointScale_congr _ (height_zero_ray s a ha))
      (pointScale_congr _ (height_zero_ray s b hb))
  exact pointEquiv_trans ht (pointEquiv_trans (ray_lerp_radius u a.1 b.1 s)
    (ray_congr_radius s hs))

/-- A paired connector whose endpoint heights straddle the ray meets it in
a positive rational point when both endpoints have positive first coordinate. -/
theorem positive_connector_crossing (s : Fraction) (p q : Point)
    (hp : 0 < p.1.num) (hq : 0 < q.1.num)
    (h : (Fraction.le (height s p) (Fraction.ofInt 0) ∧
        Fraction.le (Fraction.ofInt 0) (height s q)) ∨
      (Fraction.le (Fraction.ofInt 0) (height s p) ∧
        Fraction.le (height s q) (Fraction.ofInt 0))) :
    ∃ ell, UnitInterval ell ∧ 0 < (lerp ell p q).1.num ∧
      Fraction.equiv (height s (lerp ell p q)) (Fraction.ofInt 0) := by
  obtain ⟨ell,hell,he⟩ := affine_crossing (height s p) (height s q)
    (Fraction.ofInt 0) (Fraction.ofInt 0) h
  exact ⟨ell,hell,lerp_first_positive ell hell p q hp hq,
    Fraction.equiv_trans (height_lerp s ell p q)
      (Fraction.equiv_trans he (affine_constant ell (Fraction.ofInt 0)))⟩

theorem point_slope_ray (p : Point) (hp : 0 < p.1.num) :
    pointEquiv p (ray p.1 (slope p hp)) := by
  constructor
  · exact Fraction.equiv_refl _
  · simp only [ray,slope,Fraction.equiv,Fraction.mul]
    ac_nf

theorem height_at_slope (p : Point) (hp : 0 < p.1.num) :
    Fraction.equiv (height (slope p hp) p) (Fraction.ofInt 0) :=
  Fraction.equiv_trans (det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
    (point_slope_ray p hp)) (ray_height_zero _ _)

theorem slope_le_height (s : Fraction) (p : Point) (hp : 0 < p.1.num) :
    Fraction.le (slope p hp) s ↔ Fraction.le (height s p) (Fraction.ofInt 0) := by
  simp only [slope,height,ray,det,Fraction.le,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one,Int.zero_mul]
  ac_nf
  omega

theorem height_le_slope (s : Fraction) (p : Point) (hp : 0 < p.1.num) :
    Fraction.le s (slope p hp) ↔ Fraction.le (Fraction.ofInt 0) (height s p) := by
  simp only [slope,height,ray,det,Fraction.le,Fraction.add,Fraction.mul,Fraction.ofInt,
    Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.one_mul,Int.mul_one,Int.zero_mul]
  ac_nf
  omega

/-- A point below a positive cap on the same ray belongs to any origin
triangle containing the cap. -/
theorem below_cap (p q c x : Point) (s : Fraction)
    (hc : 0 < c.1.num) (hcx : Fraction.le x.1 c.1) (hx : 0 ≤ x.1.num)
    (hcRay : Fraction.equiv (height s c) (Fraction.ofInt 0))
    (hxRay : Fraction.equiv (height s x) (Fraction.ofInt 0))
    (hcTri : Triangle p q c) : Triangle p q x := by
  obtain ⟨r,hr,he⟩ := scale_to_cap (Fraction.ofInt 1) x.1 c.1
    ⟨by decide,by decide⟩ hx hc hcx
  have he' : Fraction.equiv (Fraction.mul r c.1) x.1 := Fraction.equiv_trans he
    (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one])
  have hpoint : pointEquiv x (pointScale r c) :=
    pointEquiv_trans (height_zero_ray s x hxRay)
      (pointEquiv_symm (pointEquiv_trans (pointScale_congr r (height_zero_ray s c hcRay))
        (pointEquiv_trans (scale_ray r c.1 s) (ray_congr_radius s he'))))
  obtain ⟨u,v,hu,hv,huv,hcv⟩ := hcTri
  refine ⟨Fraction.mul r u,Fraction.mul r v,
    Fraction.nonnegative_mul _ _ hr.1 hu,Fraction.nonnegative_mul _ _ hr.1 hv,?_,?_⟩
  · have hr1 : Fraction.le r (Fraction.ofInt 1) := by
      simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hr.2
    exact Fraction.le_equiv_left (Fraction.equiv_symm (Fraction.mul_add r u v))
      (Fraction.magnitudes.le_trans
        (Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative_left huv r hr.1)
          (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.mul_one,Int.one_mul])) hr1)
  · exact pointEquiv_trans hpoint (pointEquiv_trans (pointScale_congr r hcv)
      (pointEquiv_trans (pointScale_add _ _ _)
        (pointAdd_congr (scale_assoc _ _ _) (scale_assoc _ _ _))))

theorem edge_triangle (p q : Point) (u : Fraction) (hu : UnitInterval u) :
    Triangle p q (lerp u p q) := by
  refine ⟨complement u,u,complement_nonnegative u hu,hu.1,?_,
    ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩
  exact Fraction.le_of_equiv (weights_sum_one u)

def fanSlope (p : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num) (k : Nat) : Fraction :=
  slope (p (min k n)) (hp _ (Nat.min_le_right k n))

theorem fanSlope_vertex (p : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num) (k : Nat) (hk : k ≤ n) :
    fanSlope p n hp k = slope (p k) (hp k hk) := by
  simp only [fanSlope,Nat.min_eq_left hk]

theorem fanSlope_monotone (p : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num)
    (hc : ∀ k, k < n → 0 ≤ (det (p k) (p (k+1))).num) :
    ∀ i j, i ≤ j → Fraction.le (fanSlope p n hp i) (fanSlope p n hp j) := by
  intro i j hij
  exact (slope_order _ _ _ _).mpr (pairwise_orientation p n hp hc
    (min i n) (min j n) (by omega) (Nat.min_le_right _ _))

/-- An ordered positive fan whose endpoint slopes bracket a ray has an
actual rational boundary-edge crossing on that ray. -/
theorem fan_boundary_crossing (p : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num)
    (s : Fraction) (hn : 0 < n)
    (h0 : Fraction.le (fanSlope p n hp 0) s)
    (hN : Fraction.le s (fanSlope p n hp n)) :
    ∃ k u, k < n ∧ UnitInterval u ∧ 0 < (lerp u (p k) (p (k+1))).1.num ∧
      Fraction.equiv (height s (lerp u (p k) (p (k+1)))) (Fraction.ofInt 0) ∧
      Fraction.le (fanSlope p n hp k) s ∧
      Fraction.le s (fanSlope p n hp (k+1)) := by
  obtain ⟨k,hk,hleft,hright⟩ := FanIntervalChain.rising_crossing
    (fun k => (fanSlope p n hp k).toRat) s.toRat n hn
    ((Fraction.le_iff_toRat _ _).mp h0) ((Fraction.le_iff_toRat _ _).mp hN)
  have hleft := (Fraction.le_iff_toRat _ _).mpr hleft
  have hright := (Fraction.le_iff_toRat _ _).mpr hright
  have ha := (slope_le_height s (p k) (hp k (by omega))).mp
    (by simpa only [fanSlope_vertex p n hp k (by omega)] using hleft)
  have hb := (height_le_slope s (p (k+1)) (hp (k+1) (by omega))).mp
    (by simpa only [fanSlope_vertex p n hp (k+1) (by omega)] using hright)
  obtain ⟨u,hu,hpos,hzero⟩ := positive_connector_crossing s (p k) (p (k+1))
    (hp k (by omega)) (hp (k+1) (by omega)) (Or.inl ⟨ha,hb⟩)
  exact ⟨k,u,hk,hu,hpos,hzero,hleft,hright⟩

theorem edge_slope_bracket (p q : Point) (hp : 0 < p.1.num) (hq : 0 < q.1.num)
    (hd : 0 ≤ (det p q).num) (u : Fraction) (hu : UnitInterval u) :
    Fraction.le (slope p hp) (slope (lerp u p q) (lerp_first_positive u hu p q hp hq)) ∧
    Fraction.le (slope (lerp u p q) (lerp_first_positive u hu p q hp hq)) (slope q hq) := by
  have ht := edge_triangle p q u hu
  constructor
  · exact (slope_order _ _ _ _).mpr (triangle_right p q p _ ht
      (Fraction.nonnegative_equiv (det_self p) (by decide)) hd)
  · exact (slope_order _ _ _ _).mpr (triangle_left p q q _ ht hd
      (Fraction.nonnegative_equiv (det_self q) (by decide)))

end NewtonLimitDynamics.Polygon.FanRadial
