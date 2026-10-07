import BarrowLib.Polygon.SectorFan
import BarrowLib.Polygon.SupportingTangents
import BarrowLib.Polygon.RationalIntervals

/-! Filled sectors of a given positive radial graph in a local half-plane.
The chart is `ray R t = (R, R*t)`: `t = y/x` is slope and `g(t)`
is the positive x-coordinate (ray scale), not Euclidean polar radius.
The graph is data. Its area, mechanical origin and agreement with Newton's
polygons are not built into its definition. Finite set inclusions below are
coordinate derivations using only Barrow support, not modern completion.

Source of the definitions and coordinate derivations: the original English
explanation and Lean statements/proofs in this file. This identifies project
formalization, not mathematical discovery or priority. The classical area
background is Euclid I.41, quoted in the original Greek in SectorFan.lean;
that passage is not claimed to state the exact coordinate helper lemmas.
https://physics.ntua.gr/mourmouras/euclid/book1/postulate41.html
Ἐὰν παραλληλόγραμμον τριγώνῳ βάσιν τε ἔχῃ τὴν αὐτὴν καὶ ἐν ταῖς
αὐταῖς παραλλήλοις ᾖ, διπλάσιόν ἐστι τὸ παραλληλόγραμμον τοῦ τριγώνου.
-/
namespace NewtonLimitDynamics.Polygon.RadialSector
open NewtonLimitDynamics TimeSubdivision ConvexCover SupportingTangents
open MonotoneRectangles HarmonicTimeComparison PolygonFanArea

def ray (R t : Fraction) : Point := (R, Fraction.mul R t)

def sector (g : Fraction → Fraction) (a b : Fraction) (x : Point) : Prop :=
  ∃ t, Fraction.le a t ∧ Fraction.le t b ∧ ∃ r, UnitInterval r ∧
    pointEquiv x (pointScale r (ray (g t) t))

theorem affine_constant (u t : Fraction) : Fraction.equiv (affine u t t) t :=
  Fraction.equiv_trans (Fraction.equiv_symm (Fraction.add_mul _ _ _))
    (Fraction.equiv_trans (Fraction.mul_equiv_right t (weights_sum_one u))
      (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]))

/-- Every point of an ordered scalar interval has a convex parameter,
including a collapsed interval. -/
theorem interval_parameter (a b t : Fraction) (ha : Fraction.le a t)
    (hb : Fraction.le t b) :
    ∃ u, UnitInterval u ∧ Fraction.equiv (affine u a b) t := by
  obtain ⟨u,hu,he⟩ := affine_crossing a b t t (Or.inl ⟨ha,hb⟩)
  exact ⟨u,hu,Fraction.equiv_trans he (affine_constant u t)⟩

theorem scale_assoc (r s : Fraction) (p : Point) :
    pointEquiv (pointScale r (pointScale s p)) (pointScale (Fraction.mul r s) p) :=
  ⟨Fraction.equiv_symm (Fraction.mul_assoc _ _ _),
    Fraction.equiv_symm (Fraction.mul_assoc _ _ _)⟩

theorem ray_lerp (u R a b : Fraction) :
    pointEquiv (lerp u (ray R a) (ray R b)) (ray R (affine u a b)) := by
  constructor
  · exact affine_constant u R
  · simp only [lerp,ray,affine,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
      Int.add_mul,Int.mul_add]
    ac_nf

/-- Shrinking a positive radial cap changes the radial parameter, rather
than assuming an inclusion of the represented filled figures. -/
theorem scale_to_cap (r R S : Fraction) (hr : UnitInterval r)
    (hR : 0 ≤ R.num) (hS : 0 < S.num) (hRS : Fraction.le R S) :
    ∃ u, UnitInterval u ∧ Fraction.equiv (Fraction.mul u S) (Fraction.mul r R) := by
  let z := Fraction.mul r R
  let u := Fraction.quotient z S hS
  have hz : 0 ≤ z.num := Fraction.nonnegative_mul _ _ hr.1 hR
  have hr1 : Fraction.le r (Fraction.ofInt 1) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hr.2
  have hzS : Fraction.le z S := Fraction.magnitudes.le_trans
    (Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative hr1 R hR)
      (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one])) hRS
  refine ⟨u,⟨Int.mul_nonneg hz (Int.le_of_lt S.den_pos),?_⟩,?_⟩
  · change z.num*S.den ≤ z.den*S.num
    simpa only [Fraction.le,Int.mul_comm] using hzS
  · simp only [u,z,Fraction.quotient,Fraction.mul,Fraction.equiv]
    ac_nf

/-- Barycentric triangle membership is equivalently a radial parameter
times a point on its opposite edge. Zero weights cause no division. -/
theorem triangle_radial (p q x : Point) :
    SectorFan.Triangle p q x ↔
      ∃ r u, UnitInterval r ∧ UnitInterval u ∧ pointEquiv x (pointScale r (lerp u p q)) := by
  constructor
  · rintro ⟨s,t,hs,ht,hst,he⟩
    obtain ⟨u,hu,hcross⟩ := affine_crossing t (Fraction.ofInt 0) (Fraction.ofInt 0) s
      (Or.inr ⟨by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using ht,
        by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hs⟩)
    have hbal : Fraction.equiv (Fraction.mul (complement u) t) (Fraction.mul u s) := by
      have hl : Fraction.equiv (affine u t (Fraction.ofInt 0)) (Fraction.mul (complement u) t) :=
        Fraction.equiv_trans (Fraction.add_equiv_left _ (Fraction.mul_zero u)) (Fraction.add_zero _)
      have hr : Fraction.equiv (affine u (Fraction.ofInt 0) s) (Fraction.mul u s) :=
        Fraction.equiv_trans (Fraction.add_equiv_right _ (Fraction.mul_zero (complement u)))
          (Fraction.equiv_trans (Fraction.add_comm _ _) (Fraction.add_zero _))
      exact Fraction.equiv_trans (Fraction.equiv_symm hl) (Fraction.equiv_trans hcross hr)
    have leftWeight : Fraction.equiv (Fraction.mul (Fraction.add s t) (complement u)) s := by
      have h := Fraction.equiv_trans (Fraction.add_mul s t (complement u))
        (Fraction.add_equiv (Fraction.mul_comm s (complement u))
          (Fraction.equiv_trans (Fraction.mul_comm t (complement u)) hbal))
      exact Fraction.equiv_trans h (affine_constant u s)
    have rightWeight : Fraction.equiv (Fraction.mul (Fraction.add s t) u) t := by
      have h := Fraction.equiv_trans (Fraction.add_mul s t u)
        (Fraction.add_equiv (Fraction.equiv_trans (Fraction.mul_comm s u) (Fraction.equiv_symm hbal))
          (Fraction.mul_comm t u))
      exact Fraction.equiv_trans h (affine_constant u t)
    refine ⟨Fraction.add s t,u,⟨Fraction.nonnegative_add _ _ hs ht,?_⟩,hu,?_⟩
    · simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hst
    · apply pointEquiv_trans he
      apply pointEquiv_symm
      exact pointEquiv_trans (pointScale_add _ _ _)
        (pointAdd_congr
          (pointEquiv_trans (scale_assoc _ _ _) (pointScale_ratio_congr leftWeight
            ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩))
          (pointEquiv_trans (scale_assoc _ _ _) (pointScale_ratio_congr rightWeight
            ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩)))
  · rintro ⟨r,u,hr,hu,he⟩
    let s := Fraction.mul r (complement u)
    let t := Fraction.mul r u
    have hsum : Fraction.equiv (Fraction.add s t) r :=
      Fraction.equiv_trans (Fraction.equiv_symm (Fraction.mul_add _ _ _))
        (Fraction.equiv_trans (Fraction.mul_equiv_left r (weights_sum_one u))
          (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]))
    refine ⟨s,t,Fraction.nonnegative_mul _ _ hr.1 (complement_nonnegative u hu),
      Fraction.nonnegative_mul _ _ hr.1 hu.1,?_,?_⟩
    · exact Fraction.le_equiv_left hsum
        (by simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hr.2)
    · exact pointEquiv_trans he (pointEquiv_trans (pointScale_add _ _ _)
        (pointAdd_congr (scale_assoc _ _ _) (scale_assoc _ _ _)))

theorem positive_of_le (R S : Fraction) (hR : 0 < R.num) (hRS : Fraction.le R S) :
    0 < S.num :=
  (Fraction.positive_iff_zero_lt S).mpr
    (Fraction.magnitudes.lt_of_lt_le ((Fraction.positive_iff_zero_lt R).mp hR) hRS)

theorem ray_congr_radius {R S : Fraction} (t : Fraction) (h : Fraction.equiv R S) :
    pointEquiv (ray R t) (ray S t) := ⟨h,Fraction.mul_equiv_right t h⟩

theorem ray_congr_slope (R : Fraction) {a b : Fraction} (h : Fraction.equiv a b) :
    pointEquiv (ray R a) (ray R b) := ⟨Fraction.equiv_refl _,Fraction.mul_equiv_left R h⟩

theorem scale_ray (r R t : Fraction) :
    pointEquiv (pointScale r (ray R t)) (ray (Fraction.mul r R) t) :=
  ⟨Fraction.equiv_refl _,Fraction.equiv_symm (Fraction.mul_assoc _ _ _)⟩

theorem scaled_ray_congr {r R s S : Fraction} (t : Fraction)
    (h : Fraction.equiv (Fraction.mul r R) (Fraction.mul s S)) :
    pointEquiv (pointScale r (ray R t)) (pointScale s (ray S t)) :=
  pointEquiv_trans (scale_ray _ _ _)
    (pointEquiv_trans (ray_congr_radius t h) (pointEquiv_symm (scale_ray _ _ _)))

/-- A triangle contains the triangle generated by any two of its points.
This is the coordinate barycentric inclusion, proved rather than supplied. -/
theorem triangle_inclusion {p q v w : Point}
    (hv : SectorFan.Triangle p q v) (hw : SectorFan.Triangle p q w) :
    ∀ x, SectorFan.Triangle v w x → SectorFan.Triangle p q x := by
  obtain ⟨a,b,ha,hb,hab,hv⟩ := hv
  obtain ⟨c,d,hc,hd,hcd,hw⟩ := hw
  rintro x ⟨s,t,hs,ht,hst,hx⟩
  let A := Fraction.add (Fraction.mul s a) (Fraction.mul t c)
  let B := Fraction.add (Fraction.mul s b) (Fraction.mul t d)
  have he : Fraction.equiv (Fraction.add A B)
      (Fraction.add (Fraction.mul s (Fraction.add a b)) (Fraction.mul t (Fraction.add c d))) := by
    simp only [A,B,Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add]
    ac_nf
  have hsum := Fraction.add_le_add
    (Fraction.mul_le_mul_nonnegative_left hab s hs)
    (Fraction.mul_le_mul_nonnegative_left hcd t ht)
  have hone (r : Fraction) : Fraction.equiv (Fraction.mul r (Fraction.ofInt 1)) r := by
    simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.mul_one,Int.one_mul]
  refine ⟨A,B,Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hs ha)
      (Fraction.nonnegative_mul _ _ ht hc),
    Fraction.nonnegative_add _ _ (Fraction.nonnegative_mul _ _ hs hb)
      (Fraction.nonnegative_mul _ _ ht hd),?_,?_⟩
  · exact Fraction.le_equiv_left he (Fraction.magnitudes.le_trans
      (Fraction.le_equiv_right hsum (Fraction.add_equiv (hone s) (hone t))) hst)
  · apply pointEquiv_trans hx
    apply pointEquiv_trans (pointAdd_congr (pointScale_congr s hv) (pointScale_congr t hw))
    constructor <;>
      simp only [A,B,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
        Int.add_mul,Int.mul_add] <;> ac_nf

theorem triangle_vertex_left (p q : Point) : SectorFan.Triangle p q p := by
  refine ⟨Fraction.ofInt 1,Fraction.ofInt 0,by decide,by decide,by simp [Fraction.le,Fraction.add,Fraction.ofInt],?_⟩
  constructor <;> simp only [pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
    Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.add_zero] <;> ac_nf

theorem triangle_vertex_right (p q : Point) : SectorFan.Triangle p q q := by
  refine ⟨Fraction.ofInt 0,Fraction.ofInt 1,by decide,by decide,by simp [Fraction.le,Fraction.add,Fraction.ofInt],?_⟩
  constructor <;> simp only [pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
    Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.zero_add] <;> ac_nf

theorem triangle_congr_point {p q x y : Point} (h : pointEquiv x y)
    (hy : SectorFan.Triangle p q y) : SectorFan.Triangle p q x := by
  obtain ⟨s,t,hs,ht,hst,he⟩ := hy
  exact ⟨s,t,hs,ht,hst,pointEquiv_trans h he⟩

theorem triangle_scale_left (p q : Point) (u : Fraction) (hu : UnitInterval u) :
    SectorFan.Triangle p q (pointScale u p) := by
  refine ⟨u,Fraction.ofInt 0,hu.1,by decide,?_,?_⟩
  · exact Fraction.le_equiv_left (Fraction.add_zero u)
      (by simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hu.2)
  · constructor <;> simp only [pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
      Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.add_zero] <;> ac_nf

theorem triangle_scale_right (p q : Point) (u : Fraction) (hu : UnitInterval u) :
    SectorFan.Triangle p q (pointScale u q) := by
  refine ⟨Fraction.ofInt 0,u,by decide,hu.1,?_,?_⟩
  · exact Fraction.le_equiv_left (Fraction.equiv_trans (Fraction.add_comm _ _) (Fraction.add_zero u))
      (by simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hu.2)
  · constructor <;> simp only [pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
      Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.one_mul,Int.mul_one,Int.zero_add] <;> ac_nf

/-- A smaller point on either radial side belongs to its larger cap. -/
theorem radial_vertex (R S t : Fraction) (hR : 0 ≤ R.num) (hS : 0 < S.num)
    (hRS : Fraction.le R S) :
    ∃ u, UnitInterval u ∧ pointEquiv (ray R t) (pointScale u (ray S t)) := by
  obtain ⟨u,hu,he⟩ := scale_to_cap (Fraction.ofInt 1) R S ⟨by decide,by decide⟩ hR hS hRS
  refine ⟨u,hu,pointEquiv_symm (pointEquiv_trans (scale_ray u S t) (ray_congr_radius t ?_))⟩
  exact Fraction.equiv_trans he (by simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,
    Int.one_mul,Int.mul_one])

/-- The actual lower triangle and upper triangle enclose the filled radial
graph sector. The inclusion is derived from radial monotonicity. -/
theorem caps_enclosure (g : Fraction → Fraction) (a b R S : Fraction)
    (hab : Fraction.le a b) (hg : MonotoneOn g a b) (hbase : 0 < (g a).num)
    (hR : 0 ≤ R.num) (hRa : Fraction.le R (g a)) (hbS : Fraction.le (g b) S) :
    (∀ x, SectorFan.Triangle (ray R a) (ray R b) x → sector g a b x) ∧
    (∀ x, sector g a b x → SectorFan.Triangle (ray S a) (ray S b) x) := by
  constructor
  · intro x hx
    obtain ⟨r,u,hr,hu,he⟩ := (triangle_radial _ _ _).mp hx
    let t := affine u a b
    have ht := affine_between u a b hu hab
    have hga := hg a t (Fraction.magnitudes.le_refl _) ht.1 ht.2
    obtain ⟨w,hw,heq⟩ := scale_to_cap r R (g t) hr hR (positive_of_le _ _ hbase hga)
      (Fraction.magnitudes.le_trans hRa hga)
    refine ⟨t,ht.1,ht.2,w,hw,?_⟩
    exact pointEquiv_trans he (pointEquiv_trans (pointScale_congr r (ray_lerp u R a b))
      (scaled_ray_congr t (Fraction.equiv_symm heq)))
  · rintro x ⟨t,hat,htb,r,hr,he⟩
    have hga := hg a t (Fraction.magnitudes.le_refl _) hat htb
    have hgb := hg t b hat htb (Fraction.magnitudes.le_refl _)
    have hS := positive_of_le _ _ hbase (Fraction.magnitudes.le_trans hga
      (Fraction.magnitudes.le_trans hgb hbS))
    obtain ⟨w,hw,heq⟩ := scale_to_cap r (g t) S hr
      (Int.le_of_lt (positive_of_le _ _ hbase hga)) hS (Fraction.magnitudes.le_trans hgb hbS)
    obtain ⟨u,hu,heu⟩ := interval_parameter a b t hat htb
    apply (triangle_radial _ _ _).mpr
    refine ⟨w,u,hw,hu,?_⟩
    have hline := pointEquiv_trans (ray_lerp u S a b) (ray_congr_slope S heu)
    exact pointEquiv_trans he (pointEquiv_trans (scaled_ray_congr t (Fraction.equiv_symm heq))
      (pointEquiv_symm (pointScale_congr w hline)))

def strips {a b : Fraction} (p : Partition a b) (radii : Nat → Fraction)
    (n : Nat) (x : Point) : Prop :=
  ∃ i, i < n ∧ SectorFan.Triangle
    (ray (radii i) (p.nodes i)) (ray (radii i) (p.nodes (i+1))) x

def lowerFigure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) : Point → Prop :=
  strips p (fun i => g (p.nodes i)) p.count

def upperFigure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) : Point → Prop :=
  strips p (fun i => g (p.nodes (i+1))) p.count

def chordFigure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) : Point → Prop :=
  SectorFan.Region (fun i => ray (g (p.nodes i)) (p.nodes i)) p.count

theorem cap_chord_enclosure (R S a b : Fraction) (hR : 0 < R.num) (hRS : Fraction.le R S) :
    (∀ x, SectorFan.Triangle (ray R a) (ray R b) x →
      SectorFan.Triangle (ray R a) (ray S b) x) ∧
    (∀ x, SectorFan.Triangle (ray R a) (ray S b) x →
      SectorFan.Triangle (ray S a) (ray S b) x) := by
  have hS := positive_of_le R S hR hRS
  obtain ⟨u,hu,he⟩ := radial_vertex R S b (Int.le_of_lt hR) hS hRS
  obtain ⟨v,hv,hf⟩ := radial_vertex R S a (Int.le_of_lt hR) hS hRS
  exact ⟨triangle_inclusion (triangle_vertex_left _ _)
      (triangle_congr_point he (triangle_scale_right _ _ u hu)),
    triangle_inclusion (triangle_congr_point hf (triangle_scale_left _ _ v hv))
      (triangle_vertex_right _ _)⟩

theorem cell_monotone {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (i : Nat) (hi : i < p.count) :
    MonotoneOn g (p.nodes i) (p.nodes (i+1)) := by
  intro s t hls hst htr
  exact hg s t (Fraction.magnitudes.le_trans (node_bounds p i (by omega)).1 hls)
    hst (Fraction.magnitudes.le_trans htr (node_bounds p (i+1) (by omega)).2)

theorem node_positive {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0 < (g a).num) (i : Nat) (hi : i ≤ p.count) :
    0 < (g (p.nodes i)).num :=
  positive_of_le _ _ hbase (hg a _ (Fraction.magnitudes.le_refl _)
    (node_bounds p i hi).1 (node_bounds p i hi).2)

/-- Finite slope cells enclose the actual given sector, including their
shared radial boundaries and the final ray. No area or convergence premise
is used in these point-set inclusions. -/
theorem sector_enclosure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0 < (g a).num) :
    (∀ x, lowerFigure g p x → sector g a b x) ∧
    (∀ x, sector g a b x → upperFigure g p x) := by
  have hcaps (i : Nat) (hi : i < p.count) := caps_enclosure g (p.nodes i) (p.nodes (i+1))
    (g (p.nodes i)) (g (p.nodes (i+1))) (p.ordered i hi) (cell_monotone g p hg i hi)
    (node_positive g p hg hbase i (by omega))
    (Int.le_of_lt (node_positive g p hg hbase i (by omega)))
    (Fraction.magnitudes.le_refl _) (Fraction.magnitudes.le_refl _)
  constructor
  · rintro x ⟨i,hi,hx⟩
    obtain ⟨t,hat,htb,r,hr,he⟩ := (hcaps i hi).1 x hx
    exact ⟨t,Fraction.magnitudes.le_trans (node_bounds p i (by omega)).1 hat,
      Fraction.magnitudes.le_trans htb (node_bounds p (i+1) (by omega)).2,r,hr,he⟩
  · rintro x ⟨t,hat,htb,r,hr,he⟩
    obtain ⟨i,hi,hl,hu⟩ := partition_cover p t hat htb
    exact ⟨i,hi,(hcaps i hi).2 x ⟨t,hl,hu,r,hr,he⟩⟩

/-- Both the given sector and its actual chord polygon have the same finite
inner/outer enclosures. The chord polygon need not lie on one side of the curve. -/
theorem chord_enclosure {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0 < (g a).num) :
    (∀ x, lowerFigure g p x → chordFigure g p x) ∧
    (∀ x, chordFigure g p x → upperFigure g p x) := by
  have hc (i : Nat) (hi : i < p.count) := cap_chord_enclosure (g (p.nodes i))
    (g (p.nodes (i+1))) (p.nodes i) (p.nodes (i+1))
    (node_positive g p hg hbase i (by omega))
    (hg _ _ (node_bounds p i (by omega)).1 (p.ordered i hi)
      (node_bounds p (i+1) (by omega)).2)
  constructor
  · rintro x ⟨i,hi,hx⟩
    exact ⟨i,hi,(hc i hi).1 x hx⟩
  · rintro x ⟨i,hi,hx⟩
    exact ⟨i,hi,(hc i hi).2 x hx⟩

theorem ray_det (R S a b : Fraction) :
    Fraction.equiv (TimeSubdivision.det (ray R a) (ray S b))
      (Fraction.mul (Fraction.mul R S) (durationDifference a b)) := by
  simp only [ray,TimeSubdivision.det,durationDifference,HarmonicStability.negF,
    Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
  ac_nf

theorem ray_orientation (R S a b : Fraction) (hR : 0 ≤ R.num) (hS : 0 ≤ S.num)
    (hab : Fraction.le a b) :
    0 ≤ (TimeSubdivision.det (ray R a) (ray S b)).num :=
  Fraction.nonnegative_equiv (ray_det R S a b)
    (Fraction.nonnegative_mul _ _ (Fraction.nonnegative_mul _ _ hR hS)
      ((difference_nonnegative_iff _ _).mpr hab))

def density (g : Fraction → Fraction) (t : Fraction) : Fraction :=
  (Fraction.mul (g t) (g t)).half

theorem density_monotone (g : Fraction → Fraction) (a b : Fraction)
    (hg : MonotoneOn g a b) (hbase : 0 ≤ (g a).num) : MonotoneOn (density g) a b := by
  intro s t has hst htb
  have hgs := Fraction.nonnegative_of_le hbase
    (hg a s (Fraction.magnitudes.le_refl _) has (Fraction.magnitudes.le_trans hst htb))
  have h := hg s t has hst htb
  have hgt := Fraction.nonnegative_of_le hgs h
  exact RationalIntervals.half_le (Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative h (g s) hgs)
    (Fraction.mul_le_mul_nonnegative_left h (g t) hgt))

def stripSum {a b : Fraction} (p : Partition a b) (radii : Nat → Fraction) (n : Nat) : Fraction :=
  sum (fun i => Fraction.mul (width p i) (Fraction.mul (radii i) (radii i)).half) n

theorem cap_area_formula (R a b : Fraction) :
    Fraction.equiv (TimeSubdivision.det (ray R a) (ray R b)).half
      (Fraction.mul (durationDifference a b) (Fraction.mul R R).half) := by
  apply Fraction.equiv_trans (RationalIntervals.half_equiv (ray_det R R a b))
  simp only [Fraction.equiv,Fraction.half,Fraction.mul]
  ac_nf

theorem strips_succ {a b : Fraction} (p : Partition a b) (radii : Nat → Fraction)
    (n : Nat) (x : Point) : strips p radii (n+1) x ↔ strips p radii n x ∨
      SectorFan.Triangle (ray (radii n) (p.nodes n)) (ray (radii n) (p.nodes (n+1))) x := by
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

/-- Actual radial triangle unions have their finite side-product sums as
areas. Different ray scales in adjacent cells cause no overlap error: the slope
partition derives radial separation even when the radial edges differ. -/
theorem strips_area (area : SectorFan.AreaRules) {a b : Fraction} (p : Partition a b)
    (radii : Nat → Fraction) (hr : ∀ i, i < p.count → 0 ≤ (radii i).num)
    (n : Nat) (hn : n ≤ p.count) : area.HasArea (strips p radii n) (stripSum p radii n) := by
  induction n with
  | zero =>
    apply area.congr_set (fun _ => False) _ _ _ area.empty
    intro x
    simp only [strips,Nat.not_lt_zero,false_and,exists_false]
  | succ n ih =>
    have hprev := ih (by omega)
    have hlast := area.congr_value _ _ _ (cap_area_formula (radii n) (p.nodes n) (p.nodes (n+1)))
      (area.triangle (ray (radii n) (p.nodes n)) (ray (radii n) (p.nodes (n+1)))
        (ray_orientation _ _ _ _ (hr n (by omega)) (hr n (by omega)) (p.ordered n (by omega))))
    have hu := area.radial_union _ _ _ _ (ray (Fraction.ofInt 1) (p.nodes n))
      (Or.inl (by change (1 : Int) ≠ 0; decide)) ?_ ?_ hprev hlast
    · exact area.congr_set _ _ _ (fun x => (strips_succ p radii n x).symm) hu
    · rintro x ⟨i,hi,hx⟩
      apply SectorFan.triangle_left _ _ _ x hx
      · exact ray_orientation _ _ _ _ (hr i (by omega)) (by decide)
          (node_order p n i (by omega) (by omega))
      · exact ray_orientation _ _ _ _ (hr i (by omega)) (by decide)
          (node_order p n (i+1) (by omega) (by omega))
    · intro x hx
      apply SectorFan.triangle_right _ _ _ x hx
      · exact ray_orientation _ _ _ _ (by decide) (hr n (by omega)) (Fraction.magnitudes.le_refl _)
      · exact ray_orientation _ _ _ _ (by decide) (hr n (by omega)) (p.ordered n (by omega))

theorem lower_upper_areas (area : SectorFan.AreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0 < (g a).num) :
    area.HasArea (lowerFigure g p) (lowerSum (density g) p) ∧
    area.HasArea (upperFigure g p) (upperSum (density g) p) :=
  ⟨strips_area area p (fun i => g (p.nodes i))
      (fun i hi => Int.le_of_lt (node_positive g p hg hbase i (by omega))) p.count (Nat.le_refl _),
    strips_area area p (fun i => g (p.nodes (i+1)))
      (fun i hi => Int.le_of_lt (node_positive g p hg hbase (i+1) (by omega))) p.count (Nat.le_refl _)⟩

theorem area_enclosure (area : SectorFan.AreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0 < (g a).num) (A : Fraction) (hA : area.HasArea (sector g a b) A) :
    Fraction.le (lowerSum (density g) p) A ∧ Fraction.le A (upperSum (density g) p) := by
  have hs := sector_enclosure g p hg hbase
  have ha := lower_upper_areas area g p hg hbase
  exact ⟨area.monotone _ _ _ _ hs.1 ha.1 hA,area.monotone _ _ _ _ hs.2 hA ha.2⟩

def chordArea {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) : Fraction :=
  SectorFan.areaSum (fun i => ray (g (p.nodes i)) (p.nodes i)) p.count

theorem chord_area (area : SectorFan.AreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0 < (g a).num) : area.HasArea (chordFigure g p) (chordArea g p) :=
  SectorFan.region_area area _ _ (fun i hi => node_positive g p hg hbase i hi)
    (fun i hi => ray_orientation _ _ _ _
      (Int.le_of_lt (node_positive g p hg hbase i (by omega)))
      (Int.le_of_lt (node_positive g p hg hbase (i+1) (by omega))) (p.ordered i hi))

theorem chord_area_enclosure (area : SectorFan.AreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0 < (g a).num) :
    Fraction.le (lowerSum (density g) p) (chordArea g p) ∧
    Fraction.le (chordArea g p) (upperSum (density g) p) := by
  have hs := chord_enclosure g p hg hbase
  have ha := lower_upper_areas area g p hg hbase
  have hc := chord_area area g p hg hbase
  exact ⟨area.monotone _ _ _ _ hs.1 ha.1 hc,area.monotone _ _ _ _ hs.2 hc ha.2⟩

/-- Two magnitudes in one interval differ by at most its width. -/
theorem interval_difference_bound (L U A C : Fraction)
    (hLA : Fraction.le L A) (hAU : Fraction.le A U)
    (hLC : Fraction.le L C) (hCU : Fraction.le C U) :
    Fraction.le (durationDifference A C).abs (durationDifference L U) := by
  have hLU := Fraction.magnitudes.le_trans hLA hAU
  have hnon := Fraction.abs_of_nonnegative _ ((difference_nonnegative_iff L U).mpr hLU)
  apply Fraction.le_equiv_right (b := (durationDifference L U).abs) ?_ hnon
  classical
  by_cases hAC : Fraction.le A C
  ·
    exact Fraction.magnitudes.le_trans (difference_interval_gaps L A C hLA hAC).2
      (difference_interval_gaps L C U hLC hCU).1
  · have hCA : Fraction.le C A := by
      simp only [Fraction.le] at *
      omega
    exact Fraction.le_equiv_left (HarmonicTimeRealization.durationDifference_abs_symm A C)
      (Fraction.magnitudes.le_trans (difference_interval_gaps L C A hLC hCA).2
        (difference_interval_gaps L A U hLA hAU).1)

theorem chord_error_bound (area : SectorFan.AreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0 < (g a).num) (A : Fraction) (hA : area.HasArea (sector g a b) A) :
    Fraction.le (durationDifference A (chordArea g p)).abs (gap (density g) p) := by
  have ha := area_enclosure area g p hg hbase A hA
  have hc := chord_area_enclosure area g p hg hbase
  exact interval_difference_bound _ _ _ _ ha.1 ha.2 hc.1 hc.2

/-- Subtraction of nested assigned areas is a further geometric convention.
It does not assume any bound, agreement or limiting behavior for a curve.
Background: Euclid's Common Notion 3, original Greek (NTUA transcription):
Καὶ ἐὰν ἀπὸ ἴσων ἴσα ἀφαιρεθῇ, τὰ καταλειπόμενά ἐστιν ἴσα.
https://physics.ntua.gr/mourmouras/euclid/book1/elements1.html
The coordinate closure rule is our stated premise; the quoted equality rule
is not claimed to state this exact partial-area interface. -/
structure DifferenceAreaRules extends toSectorAreaRules : SectorFan.AreaRules where
  subtract : ∀ U V A B, (∀ x, U x → V x) → HasArea U A → HasArea V B →
    HasArea (fun x => V x ∧ ¬ U x) (durationDifference A B)

def between {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (x : Point) : Prop :=
  (sector g a b x ∧ ¬ chordFigure g p x) ∨ (chordFigure g p x ∧ ¬ sector g a b x)

def collar {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b) (x : Point) : Prop :=
  upperFigure g p x ∧ ¬ lowerFigure g p x

theorem between_subset_collar {a b : Fraction} (g : Fraction → Fraction) (p : Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0 < (g a).num) :
    ∀ x, between g p x → collar g p x := by
  have hs := sector_enclosure g p hg hbase
  have hc := chord_enclosure g p hg hbase
  rintro x (⟨hx,hn⟩ | ⟨hx,hn⟩)
  · exact ⟨hs.2 x hx,fun hl => hn (hc.1 x hl)⟩
  · exact ⟨hc.2 x hx,fun hl => hn (hs.1 x hl)⟩

theorem collar_area (area : DifferenceAreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0 < (g a).num) :
    area.HasArea (collar g p) (gap (density g) p) := by
  have hs := sector_enclosure g p hg hbase
  have ha := lower_upper_areas area.toSectorAreaRules g p hg hbase
  exact area.subtract _ _ _ _ (fun x hx => hs.2 x (hs.1 x hx)) ha.1 ha.2

theorem assigned_area_nonnegative (area : SectorFan.AreaRules) (U : Point → Prop)
    (A : Fraction) (hA : area.HasArea U A) : 0 ≤ A.num := by
  have h := area.monotone (fun _ => False) U (Fraction.ofInt 0) A
    (fun _ h => False.elim h) area.empty hA
  simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.one_mul,Int.mul_one] using h

/-- The actual region between curve and chord polygon is covered by a
finite figure with the derived gap as area. If that region itself has an
assigned rational area, its nonnegativity and bound follow; its area is
never assumed to vanish. -/
theorem between_area_bound (area : DifferenceAreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (p : Partition a b) (hg : MonotoneOn g a b)
    (hbase : 0 < (g a).num) (B : Fraction) (hB : area.HasArea (between g p) B) :
    0 ≤ B.num ∧ Fraction.le B (gap (density g) p) :=
  ⟨assigned_area_nonnegative area.toSectorAreaRules _ B hB,
    area.monotone _ _ _ _ (between_subset_collar g p hg hbase) hB
      (collar_area area g p hg hbase)⟩

/-- The caller supplies exhaustion of the radial strip gap. The chord
error follows from actual set inclusions and area rules; this generic
interface does not depend on a particular historical limiting lemma. -/
theorem chord_errors_vanish (area : SectorFan.AreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (parts : Nat → Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0 < (g a).num)
    (A : Fraction) (hA : area.HasArea (sector g a b) A)
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => gap (density g) (parts m))) :
    Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => (durationDifference A (chordArea g (parts m))).abs) := by
  intro eps heps
  obtain ⟨N,hN⟩ := hgap eps heps
  exact ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt
    (chord_error_bound area g (parts m) hg hbase A hA) (hN m hm)⟩

theorem between_areas_vanish (area : DifferenceAreaRules) {a b : Fraction}
    (g : Fraction → Fraction) (parts : Nat → Partition a b)
    (hg : MonotoneOn g a b) (hbase : 0 < (g a).num)
    (B : Nat → Fraction) (hB : ∀ m, area.HasArea (between g (parts m)) (B m))
    (hgap : Exhaustion.VanishingDifference Fraction.magnitudes (fun m => gap (density g) (parts m))) :
    (∀ m, 0 ≤ (B m).num) ∧ Exhaustion.VanishingDifference Fraction.magnitudes B := by
  refine ⟨fun m => (between_area_bound area g (parts m) hg hbase (B m) (hB m)).1,?_⟩
  intro eps heps
  obtain ⟨N,hN⟩ := hgap eps heps
  exact ⟨N,fun m hm => Fraction.magnitudes.lt_of_le_lt
    (between_area_bound area g (parts m) hg hbase (B m) (hB m)).2 (hN m hm)⟩

end NewtonLimitDynamics.Polygon.RadialSector
