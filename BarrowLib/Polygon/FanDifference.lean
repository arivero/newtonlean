import BarrowLib.Polygon.FilledStrips
import BarrowLib.Polygon.FanRadial
import BarrowLib.Polygon.FanCorridor

/-! Geometric difference inclusion for finite ordered positive fans.
Source: the original English statements and checked rational-coordinate
proofs below. This records project derivation, without external historical
textual attribution, discovery or priority. Two fans must share their initial
vertex, have positive first coordinates and nonnegative consecutive
determinants. Under precisely these premises their symmetric difference is
covered by the filled paired-edge strips and the final radial connector
triangle. No sector inclusion or area is assumed; no curve, mechanical law,
real completion or modern topological result is used. This finite theorem
does not assign an area to the difference or the strip union.
-/

namespace NewtonLimitDynamics.Polygon.FanDifference
open NewtonLimitDynamics TimeSubdivision ConvexCover SupportingTangents RadialSector
open SectorFan FilledStrips FanRadial

theorem scaled_cap_data (s r : Fraction) (c x : Point) (hr : UnitInterval r)
    (hc : 0 < c.1.num) (he : pointEquiv x (pointScale r c))
    (hcRay : Fraction.equiv (height s c) (Fraction.ofInt 0)) :
    0 ≤ x.1.num ∧ Fraction.le x.1 c.1 ∧
      Fraction.equiv (height s x) (Fraction.ofInt 0) := by
  have hr1 : Fraction.le r (Fraction.ofInt 1) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hr.2
  refine ⟨Fraction.nonnegative_equiv he.1
    (Fraction.nonnegative_mul _ _ hr.1 (Int.le_of_lt hc)),?_,?_⟩
  · exact Fraction.le_equiv_left he.1
      (Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative hr1 c.1 (Int.le_of_lt hc))
        (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]))
  · exact Fraction.equiv_trans (det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ he)
      (Fraction.equiv_trans (det_scale_right r _ c)
        (Fraction.equiv_trans (Fraction.mul_equiv_left r hcRay) (Fraction.mul_zero r)))

theorem slope_congr (p q : Point) (hp : 0 < p.1.num) (hq : 0 < q.1.num)
    (h : pointEquiv p q) : Fraction.equiv (slope p hp) (slope q hq) := by
  have hd : Fraction.equiv (det p q) (Fraction.ofInt 0) :=
    Fraction.equiv_trans (det_congr h ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)
      (det_self q)
  have hd' : Fraction.equiv (det q p) (Fraction.ofInt 0) :=
    Fraction.equiv_trans (det_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ h)
      (det_self q)
  apply (Fraction.equiv_iff_mutual_le _ _).mpr
  exact ⟨(slope_order p q hp hq).mpr (Fraction.nonnegative_equiv hd (by decide)),
    (slope_order q p hq hp).mpr (Fraction.nonnegative_equiv hd' (by decide))⟩

/-- The interval of intermediate connector indices inherits opposite
height signs from the two ordered boundary crossings. -/
theorem connector_signs (p q : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num)
    (hq : ∀ k, k ≤ n → 0 < (q k).1.num)
    (hcp : ∀ k, k < n → 0 ≤ (det (p k) (p (k+1))).num)
    (hcq : ∀ k, k < n → 0 ≤ (det (q k) (q (k+1))).num)
    (s : Fraction) (ip iq k : Nat) (hiq : iq < n)
    (hleft : ip < k) (hright : k ≤ iq)
    (hsp : Fraction.le s (fanSlope p n hp (ip+1)))
    (hsq : Fraction.le (fanSlope q n hq iq) s) :
    Fraction.le (Fraction.ofInt 0) (height s (p k)) ∧
      Fraction.le (height s (q k)) (Fraction.ofInt 0) := by
  have h := FanIntervalChain.ordered_connector_bracket (fanSlope p n hp)
    (fanSlope q n hq) s ip iq k (fanSlope_monotone p n hp hcp)
    (fanSlope_monotone q n hq hcq) (by omega) hright hsp hsq
  exact ⟨(height_le_slope s (p k) (hp k (by omega))).mp
      (by simpa only [fanSlope_vertex p n hp k (by omega)] using h.1),
    (slope_le_height s (q k) (hq k (by omega))).mp
      (by simpa only [fanSlope_vertex q n hq k (by omega)] using h.2)⟩

theorem filled_region_swap (p q : Nat → Point) (n : Nat) (x : Point)
    (hx : FilledRegion p q n x) : FilledRegion q p n x := by
  obtain ⟨k,hk,theta,mu,lambda,ht,hm,hl,he⟩ := hx
  exact ⟨k,hk,mu,theta,complement lambda,hm,ht,complement_interval lambda hl,
    pointEquiv_trans he (lerp_swap lambda _ _)⟩

/-- Between two ordered positive fans, every point on a common ray between
their boundary-edge caps lies in a filled paired-edge strip. Internal radial
connectors are eliminated by the finite corridor, without area premises. -/
theorem between_boundaries (p q : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num)
    (hq : ∀ k, k ≤ n → 0 < (q k).1.num)
    (hcp : ∀ k, k < n → 0 ≤ (det (p k) (p (k+1))).num)
    (hcq : ∀ k, k < n → 0 ≤ (det (q k) (q (k+1))).num)
    (s : Fraction) (ip iq : Nat) (hip : ip < n) (hiq : iq < n)
    (up uq : Fraction) (hup : UnitInterval up) (huq : UnitInterval uq)
    (hsp0 : Fraction.le (fanSlope p n hp ip) s)
    (hsp1 : Fraction.le s (fanSlope p n hp (ip+1)))
    (hsq0 : Fraction.le (fanSlope q n hq iq) s)
    (hsq1 : Fraction.le s (fanSlope q n hq (iq+1)))
    (hrp : Fraction.equiv (height s (lerp up (p ip) (p (ip+1)))) (Fraction.ofInt 0))
    (hrq : Fraction.equiv (height s (lerp uq (q iq) (q (iq+1)))) (Fraction.ofInt 0))
    (x : Point) (hrx : Fraction.equiv (height s x) (Fraction.ofInt 0))
    (hbetween : FanIntervalChain.Between
      (lerp up (p ip) (p (ip+1))).1 x.1 (lerp uq (q iq) (q (iq+1))).1) :
    FilledRegion p q n x := by
  by_cases horder : ip ≤ iq
  · apply FanCorridor.corridor p q n ip iq horder hiq s _ _ x
      (p_edge _ _ _ _ up hup) (q_edge _ _ _ _ uq huq) hrp hrq hrx hbetween
    intro k hleft hright
    have hsign := connector_signs p q n hp hq hcp hcq s ip iq k hiq hleft hright hsp1 hsq0
    obtain ⟨ell,hell,_,he⟩ := positive_connector_crossing s (p k) (q k)
      (hp k (by omega)) (hq k (by omega)) (Or.inr hsign)
    exact ⟨ell,hell,he⟩
  · apply filled_region_swap q p n x
    have horder' : iq ≤ ip := by omega
    have hbetween' : FanIntervalChain.Between
        (lerp uq (q iq) (q (iq+1))).1 x.1 (lerp up (p ip) (p (ip+1))).1 := by
      rcases hbetween with h | h
      · exact Or.inr h
      · exact Or.inl h
    apply FanCorridor.corridor q p n iq ip horder' hip s _ _ x
      (p_edge _ _ _ _ uq huq) (q_edge _ _ _ _ up hup) hrq hrp hrx hbetween'
    intro k hleft hright
    have hsign := connector_signs q p n hq hp hcq hcp s iq ip k hip hleft hright hsq1 hsp0
    obtain ⟨ell,hell,_,he⟩ := positive_connector_crossing s (q k) (p k)
      (hq k (by omega)) (hp k (by omega)) (Or.inr hsign)
    exact ⟨ell,hell,he⟩

/-- Actual sector-union difference inclusion for two finite positive fans
with nonnegative consecutive orientations and a common initial vertex.
The only region outside their filled edge strips is the final radial
connector triangle. No area or mechanical comparison is assumed. -/
theorem difference_cover (p q : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num)
    (hq : ∀ k, k ≤ n → 0 < (q k).1.num)
    (hcp : ∀ k, k < n → 0 ≤ (det (p k) (p (k+1))).num)
    (hcq : ∀ k, k < n → 0 ≤ (det (q k) (q (k+1))).num)
    (hstart : pointEquiv (p 0) (q 0)) (x : Point)
    (hx : Region q n x) (hout : ¬ Region p n x) :
    FilledRegion p q n x ∨ Triangle (p n) (q n) x := by
  obtain ⟨iq,hiq,htri⟩ := hx
  have hn : 0 < n := by omega
  obtain ⟨r,uq,hr,huq,hscale⟩ := (triangle_radial _ _ _).mp htri
  let cq := lerp uq (q iq) (q (iq+1))
  have hcqpos : 0 < cq.1.num := lerp_first_positive uq huq _ _
    (hq iq (by omega)) (hq (iq+1) (by omega))
  let s := slope cq hcqpos
  have hcqRay : Fraction.equiv (height s cq) (Fraction.ofInt 0) := height_at_slope cq hcqpos
  obtain ⟨hx0,hxq,hxRay⟩ := scaled_cap_data s r cq x hr hcqpos hscale hcqRay
  have hbracket := edge_slope_bracket (q iq) (q (iq+1))
    (hq iq (by omega)) (hq (iq+1) (by omega)) (hcq iq hiq) uq huq
  have hqleft : Fraction.le (fanSlope q n hq iq) s := by
    simpa only [fanSlope_vertex q n hq iq (by omega)] using hbracket.1
  have hqright : Fraction.le s (fanSlope q n hq (iq+1)) := by
    simpa only [fanSlope_vertex q n hq (iq+1) (by omega)] using hbracket.2
  have hq0 : Fraction.le (fanSlope q n hq 0) s := Fraction.magnitudes.le_trans
    (fanSlope_monotone q n hq hcq 0 iq (by omega)) hqleft
  have hqN : Fraction.le s (fanSlope q n hq n) := Fraction.magnitudes.le_trans
    hqright (fanSlope_monotone q n hq hcq (iq+1) n (by omega))
  have hp0 : Fraction.le (fanSlope p n hp 0) s := by
    apply Fraction.le_equiv_left _ hq0
    simpa only [fanSlope_vertex p n hp 0 (by omega),fanSlope_vertex q n hq 0 (by omega)]
      using slope_congr (p 0) (q 0) (hp 0 (by omega)) (hq 0 (by omega)) hstart
  by_cases hpn : Fraction.le s (fanSlope p n hp n)
  · obtain ⟨ip,up,hip,hup,hcppos,hcpRay,hpleft,hpright⟩ :=
      fan_boundary_crossing p n hp s hn hp0 hpn
    let cp := lerp up (p ip) (p (ip+1))
    have hpx : Fraction.le cp.1 x.1 := by
      by_cases hxp : Fraction.le x.1 cp.1
      · exact False.elim (hout ⟨ip,hip,below_cap (p ip) (p (ip+1)) cp x s
          hcppos hxp hx0 hcpRay hxRay (edge_triangle _ _ up hup)⟩)
      · unfold Fraction.le at *
        omega
    exact Or.inl (between_boundaries p q n hp hq hcp hcq s ip iq hip hiq up uq hup huq
      hpleft hpright hqleft hqright hcpRay hcqRay x hxRay (Or.inl ⟨hpx,hxq⟩))
  · have hpn' : Fraction.le (fanSlope p n hp n) s := by unfold Fraction.le at *; omega
    have hpheight : Fraction.le (height s (p n)) (Fraction.ofInt 0) :=
      (slope_le_height s (p n) (hp n (by omega))).mp
        (by simpa only [fanSlope_vertex p n hp n (by omega)] using hpn')
    have hqheight : Fraction.le (Fraction.ofInt 0) (height s (q n)) :=
      (height_le_slope s (q n) (hq n (by omega))).mp
        (by simpa only [fanSlope_vertex q n hq n (by omega)] using hqN)
    obtain ⟨ell,hell,hendpos,hendRay⟩ := positive_connector_crossing s (p n) (q n)
      (hp n (by omega)) (hq n (by omega)) (Or.inl ⟨hpheight,hqheight⟩)
    let ce := lerp ell (p n) (q n)
    by_cases hxe : Fraction.le x.1 ce.1
    · exact Or.inr (below_cap (p n) (q n) ce x s hendpos hxe hx0 hendRay hxRay
        (edge_triangle _ _ ell hell))
    · have hex : Fraction.le ce.1 x.1 := by unfold Fraction.le at *; omega
      have hlast : n-1+1=n := by omega
      have hcend : FilledCell (p (n-1)) (p (n-1+1)) (q (n-1)) (q (n-1+1)) ce := by
        simpa only [hlast] using end_connector (p (n-1)) (p n) (q (n-1)) (q n) ell hell
      apply Or.inl
      apply FanCorridor.corridor p q n iq (n-1) (by omega) (by omega) s cq ce x
        (q_edge _ _ _ _ uq huq) hcend hcqRay hendRay hxRay (Or.inr ⟨hex,hxq⟩)
      intro k hleft hright
      have hpk : Fraction.le (fanSlope p n hp k) s := Fraction.magnitudes.le_trans
        (fanSlope_monotone p n hp hcp k n (by omega)) hpn'
      have hqk : Fraction.le s (fanSlope q n hq k) := Fraction.magnitudes.le_trans
        hqright (fanSlope_monotone q n hq hcq (iq+1) k (by omega))
      have hpkheight := (slope_le_height s (p k) (hp k (by omega))).mp
        (by simpa only [fanSlope_vertex p n hp k (by omega)] using hpk)
      have hqkheight := (height_le_slope s (q k) (hq k (by omega))).mp
        (by simpa only [fanSlope_vertex q n hq k (by omega)] using hqk)
      obtain ⟨ellk,hellk,_,hkRay⟩ := positive_connector_crossing s (p k) (q k)
        (hp k (by omega)) (hq k (by omega)) (Or.inl ⟨hpkheight,hqkheight⟩)
      exact ⟨ellk,hellk,hkRay⟩

/-- The preceding directional inclusion covers the actual symmetric
difference of the two finite sector unions. -/
theorem symmetric_difference_cover (p q : Nat → Point) (n : Nat)
    (hp : ∀ k, k ≤ n → 0 < (p k).1.num)
    (hq : ∀ k, k ≤ n → 0 < (q k).1.num)
    (hcp : ∀ k, k < n → 0 ≤ (det (p k) (p (k+1))).num)
    (hcq : ∀ k, k < n → 0 ≤ (det (q k) (q (k+1))).num)
    (hstart : pointEquiv (p 0) (q 0)) (x : Point)
    (hx : (Region p n x ∧ ¬ Region q n x) ∨ (Region q n x ∧ ¬ Region p n x)) :
    FilledRegion p q n x ∨ Triangle (p n) (q n) x := by
  rcases hx with ⟨hin,hout⟩ | ⟨hin,hout⟩
  · rcases difference_cover q p n hq hp hcq hcp (pointEquiv_symm hstart) x hin hout with h | h
    · exact Or.inl (filled_region_swap q p n x h)
    · exact Or.inr ((triangle_swap (q n) (p n) x).mp h)
  · exact difference_cover p q n hp hq hcp hcq hstart x hin hout

end NewtonLimitDynamics.Polygon.FanDifference
