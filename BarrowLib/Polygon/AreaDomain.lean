import BarrowLib.Polygon.TriangleContent

/-! Domain of the supplied elementary partial-area convention.
Source: the original English statements and rational proofs here; project
derivation without historical textual support or a priority claim.

Target: from any supplied TriangleContent.AreaRules, construct another
convention satisfying exactly those rules but assigning no area to the
symmetric difference of Triangle((1,0),(1,1)) and Triangle((1,0),(1,2)).
Permitted: elementary rational order, barycentric triangles and the supplied
convention. Not permitted: subtraction closure or an area for the difference.
The test regions themselves must retain their triangle areas 1/2 and 1.
This is a relative countermodel, not a construction of an initial area model
or a claim that every convention fails to assign every Newton between-region.

The restriction keeps representative-invariant predicates with an attained
minimum first coordinate, together with empty predicates. Representative
invariance is necessary: Fraction stores noncanonical displays, and raw
translation need not preserve minimum attainment for arbitrary predicates.
No topology, infinite union, completion or post-Newtonian theorem is used.
-/

namespace NewtonLimitDynamics.Polygon.AreaDomain
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open TriangleContent ConvexCover SupportingTangents RadialSector

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))

def Minimum (U : Point → Prop) : Prop :=
  (∀ x, ¬ U x) ∨ ∃ p, U p ∧ ∀ x, U x → Fraction.le p.1 x.1

def Admissible (U : Point → Prop) : Prop := RespectsPoints U ∧ Minimum U

theorem minimum_congr {U V : Point → Prop} (h : ∀ x, U x ↔ V x)
    (hm : Minimum U) : Minimum V := by
  rcases hm with he | ⟨p,hp,hmin⟩
  · exact Or.inl (fun x hx => he x ((h x).mpr hx))
  · exact Or.inr ⟨p,(h p).mp hp,fun x hx => hmin x ((h x).mpr hx)⟩

theorem minimum_union {U V : Point → Prop} (hU : Minimum U) (hV : Minimum V) :
    Minimum (fun x => U x ∨ V x) := by
  rcases hU with heU | ⟨p,hp,hminp⟩
  · exact minimum_congr (fun x => ⟨Or.inr,fun h => h.elim
      (fun hu => False.elim (heU x hu)) id⟩) hV
  · rcases hV with heV | ⟨q,hq,hminq⟩
    · exact Or.inr ⟨p,Or.inl hp,fun x h => h.elim (hminp x)
        (fun hv => False.elim (heV x hv))⟩
    · by_cases h : Fraction.le p.1 q.1
      · exact Or.inr ⟨p,Or.inl hp,fun x hx => hx.elim (hminp x)
          (fun hv => Fraction.magnitudes.le_trans h (hminq x hv))⟩
      · have hqp : Fraction.le q.1 p.1 := by unfold Fraction.le at *; omega
        exact Or.inr ⟨q,Or.inr hq,fun x hx => hx.elim
          (fun hu => Fraction.magnitudes.le_trans hqp (hminp x hu)) (hminq x)⟩

theorem admissible_congr {U V : Point → Prop} (h : ∀ x, U x ↔ V x)
    (hU : Admissible U) : Admissible V :=
  ⟨fun x y he hx => (h y).mp (hU.1 x y he ((h x).mpr hx)), minimum_congr h hU.2⟩

theorem admissible_union {U V : Point → Prop} (hU : Admissible U) (hV : Admissible V) :
    Admissible (fun x => U x ∨ V x) :=
  ⟨fun x y he hx => hx.elim (fun hu => Or.inl (hU.1 x y he hu))
    (fun hv => Or.inr (hV.1 x y he hv)), minimum_union hU.2 hV.2⟩

theorem admissible_empty : Admissible (fun _ => False) :=
  ⟨fun _ _ _ h => False.elim h, Or.inl (fun _ h => h)⟩

private theorem translate_inverse (p c : Point) : pointEquiv (pointSub (pointAdd p c) c) p := by
  constructor <;>
    simp only [pointSub,pointAdd,pointNeg,Fraction.equiv,Fraction.add,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

theorem admissible_translation {U : Point → Prop} (hU : Admissible U) (c : Point) :
    Admissible (translate c U) := by
  refine ⟨fun x y he hx => hU.1 _ _
    (pointSub_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) hx,?_⟩
  rcases hU.2 with he | ⟨p,hp,hmin⟩
  · exact Or.inl (fun x hx => he _ hx)
  · refine Or.inr ⟨pointAdd p c,hU.1 _ _ (pointEquiv_symm (translate_inverse p c)) hp,?_⟩
    intro x hx
    have h := Fraction.add_le_add_right (hmin _ hx) c.1
    have he : Fraction.equiv (Fraction.add (pointSub x c).1 c.1) x.1 := by
      simp only [pointSub,pointAdd,pointNeg,Fraction.equiv,Fraction.add,
        Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg]
      ac_nf
      omega
    exact Fraction.le_equiv_right h he

theorem admissible_rectangle (l r H : Fraction) (hlr : Fraction.le l r) (hH : 0 ≤ H.num) :
    Admissible (MonotoneRectangles.rectangle l r H) := by
  constructor
  · intro x y he hx
    exact ⟨Fraction.le_equiv_right hx.1 he.1,
      Fraction.le_equiv_left (Fraction.equiv_symm he.1) hx.2.1,
      Fraction.nonnegative_equiv (Fraction.equiv_symm he.2) hx.2.2.1,
      Fraction.le_equiv_left (Fraction.equiv_symm he.2) hx.2.2.2⟩
  · refine Or.inr ⟨(l,Fraction.ofInt 0),?_,fun _ hx => hx.1⟩
    exact ⟨Fraction.magnitudes.le_refl _,hlr,by change (0 : Int) ≤ 0; decide,
      by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hH⟩

private theorem affine_lower (t m a b : Fraction) (ht : UnitInterval t)
    (ha : Fraction.le m a) (hb : Fraction.le m b) : Fraction.le m (affine t a b) :=
  Fraction.le_equiv_left (Fraction.equiv_symm (affine_constant t m))
    (Fraction.add_le_add
      (Fraction.mul_le_mul_nonnegative_left ha (complement t) (complement_nonnegative t ht))
      (Fraction.mul_le_mul_nonnegative_left hb t ht.1))

private theorem triangle_lower (p q : Point) (m : Fraction)
    (hm : Fraction.le m (Fraction.ofInt 0)) (hp : Fraction.le m p.1) (hq : Fraction.le m q.1)
    (x : Point) (hx : SectorFan.Triangle p q x) : Fraction.le m x.1 := by
  obtain ⟨r,t,hr,ht,he⟩ := (triangle_radial p q x).mp hx
  have he' : Fraction.equiv (affine r (Fraction.ofInt 0) (affine t p.1 q.1))
      (pointScale r (lerp t p q)).1 := by
    simp only [affine,pointScale,lerp,pointAdd,Fraction.equiv,Fraction.add,Fraction.mul,
      Fraction.ofInt,Int.zero_mul,Int.mul_zero,Int.zero_add,Int.mul_one,Int.one_mul]
    ac_nf
  exact Fraction.le_equiv_right
    (Fraction.le_equiv_right (affine_lower r m _ _ hr hm (affine_lower t m _ _ ht hp hq)) he')
    (Fraction.equiv_symm he.1)

private theorem triangle_origin (p q : Point) :
    SectorFan.Triangle p q (Fraction.ofInt 0,Fraction.ofInt 0) := by
  refine ⟨Fraction.ofInt 0,Fraction.ofInt 0,by decide,by decide,by decide,?_⟩
  constructor <;> simp [pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt]

theorem admissible_triangle (p q : Point) : Admissible (SectorFan.Triangle p q) := by
  constructor
  · intro x y he hx
    exact triangle_congr_point (pointEquiv_symm he) hx
  · by_cases hp0 : Fraction.le p.1 (Fraction.ofInt 0)
    · by_cases hpq : Fraction.le p.1 q.1
      · exact Or.inr ⟨p,triangle_vertex_left p q,triangle_lower p q p.1 hp0
          (Fraction.magnitudes.le_refl _) hpq⟩
      · have hqp : Fraction.le q.1 p.1 := by unfold Fraction.le at *; omega
        exact Or.inr ⟨q,triangle_vertex_right p q,triangle_lower p q q.1
          (Fraction.magnitudes.le_trans hqp hp0) hqp (Fraction.magnitudes.le_refl _)⟩
    · have h0p : Fraction.le (Fraction.ofInt 0) p.1 := by unfold Fraction.le at *; omega
      by_cases hq0 : Fraction.le q.1 (Fraction.ofInt 0)
      · exact Or.inr ⟨q,triangle_vertex_right p q,triangle_lower p q q.1 hq0
          (Fraction.magnitudes.le_trans hq0 h0p) (Fraction.magnitudes.le_refl _)⟩
      · have h0q : Fraction.le (Fraction.ofInt 0) q.1 := by unfold Fraction.le at *; omega
        exact Or.inr ⟨(Fraction.ofInt 0,Fraction.ofInt 0),triangle_origin p q,
          triangle_lower p q _ (Fraction.magnitudes.le_refl _) h0p h0q⟩

/-- Restrict only the domain of the supplied relation. Every geometric rule
of the original interface is retained; no subtraction rule is added. -/
def restrict (area : TriangleContent.AreaRules) : TriangleContent.AreaRules where
  HasArea U A := area.HasArea U A ∧ Admissible U
  empty := ⟨area.empty,admissible_empty⟩
  congr_set := fun U V A h hA => ⟨area.congr_set U V A h hA.1,admissible_congr h hA.2⟩
  congr_value := fun U A B he hA => ⟨area.congr_value U A B he hA.1,hA.2⟩
  rectangle := fun l r H hlr hH => ⟨area.rectangle l r H hlr hH,admissible_rectangle l r H hlr hH⟩
  separated_union := fun U V A B c hU hV hA hB =>
    ⟨area.separated_union U V A B c hU hV hA.1 hB.1,admissible_union hA.2 hB.2⟩
  monotone := fun U V A B hUV hA hB => area.monotone U V A B hUV hA.1 hB.1
  triangle := fun p q hpq => ⟨area.triangle p q hpq,admissible_triangle p q⟩
  radial_union := fun U V A B r hr hU hV hA hB =>
    ⟨area.radial_union U V A B r hr hU hV hA.1 hB.1,admissible_union hA.2 hB.2⟩
  translation := fun U A c hA => ⟨area.translation U A c hA.1,admissible_translation hA.2 c⟩

/-- The restriction retains every already assigned positive-half-plane
radial sector. The origin attains its minimum first coordinate, and its
definition respects equivalent points. Thus the countermodel need not
discard the curved-sector input used by the local area-law proof. -/
theorem admissible_sector (g : Fraction → Fraction) (a b : Fraction)
    (hab : Fraction.le a b)
    (hg : ∀ t, Fraction.le a t → Fraction.le t b → 0 ≤ (g t).num) :
    Admissible (sector g a b) := by
  constructor
  · rintro x y he ⟨t,hat,htb,r,hr,hx⟩
    exact ⟨t,hat,htb,r,hr,pointEquiv_trans (pointEquiv_symm he) hx⟩
  · refine Or.inr ⟨(Fraction.ofInt 0,Fraction.ofInt 0),?_,?_⟩
    · refine ⟨a,Fraction.magnitudes.le_refl _,hab,Fraction.ofInt 0,⟨by decide,by decide⟩,?_⟩
      constructor <;> simp [pointScale,Fraction.equiv,Fraction.mul,Fraction.ofInt]
    · rintro x ⟨t,hat,htb,r,hr,hx⟩
      have hn := Fraction.nonnegative_equiv hx.1 (Fraction.nonnegative_mul r (g t) hr.1 (hg t hat htb))
      simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hn

theorem retain_sector (area : TriangleContent.AreaRules) (g : Fraction → Fraction)
    (a b A : Fraction) (hab : Fraction.le a b)
    (hg : ∀ t, Fraction.le a t → Fraction.le t b → 0 ≤ (g t).num)
    (hA : area.HasArea (sector g a b) A) :
    (restrict area).HasArea (sector g a b) A := ⟨hA,admissible_sector g a b hab hg⟩

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def two : Fraction := Fraction.ofInt 2

def lowerTriangle : Point → Prop := SectorFan.Triangle (ray one z) (ray one one)
def upperTriangle : Point → Prop := SectorFan.Triangle (ray one z) (ray one two)
def difference (x : Point) : Prop :=
  (lowerTriangle x ∧ ¬ upperTriangle x) ∨ (upperTriangle x ∧ ¬ lowerTriangle x)

theorem triangle_nested : ∀ x, lowerTriangle x → upperTriangle x := by
  apply triangle_inclusion (triangle_vertex_left _ _)
  exact ⟨one.half,one.half,by decide,by decide,by decide,by decide⟩

theorem difference_iff (x : Point) : difference x ↔ upperTriangle x ∧ ¬ lowerTriangle x :=
  ⟨fun h => h.elim (fun h => False.elim (h.2 (triangle_nested x h.1))) id,Or.inr⟩

theorem difference_positive (x : Point) (hx : difference x) : 0 < x.1.num := by
  obtain ⟨hu,hn⟩ := (difference_iff x).mp hx
  obtain ⟨r,t,hr,ht,he⟩ := (triangle_radial _ _ _).mp hu
  have hxr : Fraction.equiv x.1 r := by
    apply Fraction.equiv_trans he.1
    apply Fraction.equiv_trans (Fraction.mul_equiv_left r (affine_constant t one))
    simp [one,Fraction.equiv,Fraction.mul,Fraction.ofInt]
  by_cases hp : 0 < x.1.num
  · exact hp
  · have hr0 : r.num = 0 := by
      have hnon : 0 ≤ r.num := hr.1
      have hd := x.1.den_pos
      have he0 : x.1.num * r.den = r.num * x.1.den := hxr
      have hleft : x.1.num * r.den ≤ 0 :=
        Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (Int.le_of_lt r.den_pos)
      have hright : 0 ≤ r.num * x.1.den := Int.mul_nonneg hnon (Int.le_of_lt hd)
      have hz : r.num * x.1.den = 0 := by omega
      exact (Int.mul_eq_zero.mp hz).resolve_right (Int.ne_of_gt hd)
    have hx0 : pointEquiv x (z,z) := pointEquiv_trans he (by
      constructor <;> simp [pointScale,Fraction.equiv,Fraction.mul,z,Fraction.ofInt,hr0])
    exact False.elim (hn (triangle_congr_point hx0 (triangle_origin _ _)))

theorem difference_ray (r : Fraction) (hr : UnitInterval r) (hp : 0 < r.num) :
    difference (ray r two) := by
  apply (difference_iff _).mpr
  constructor
  · refine ⟨z,r,by decide,hr.1,?_,?_⟩
    · exact Fraction.le_equiv_left
        (Fraction.equiv_trans (Fraction.add_comm z r) (Fraction.add_zero r))
        (by simpa only [Fraction.le,Fraction.ofInt,Int.mul_one,Int.one_mul] using hr.2)
    · constructor <;> simp [ray,pointAdd,pointScale,Fraction.equiv,Fraction.add,Fraction.mul,
        z,one,two,Fraction.ofInt]
  · intro h
    have hd := SectorFan.triangle_left (ray one z) (ray one one) (ray one one)
      (ray r two) h (by decide) (by decide)
    simp only [TimeSubdivision.det,ray,one,two,Fraction.ofInt,Fraction.add,Fraction.mul,
      Int.mul_one,Int.one_mul,Int.mul_neg,Int.neg_mul] at hd
    have hpden : 0 < r.num * r.den := Int.mul_pos hp r.den_pos
    have hdouble : r.num * 2 * r.den = 2 * (r.num * r.den) := by ac_nf
    rw [hdouble] at hd
    omega

private theorem smaller_parameter (x : Fraction) (hx : 0 < x.num) :
    ∃ r, UnitInterval r ∧ 0 < r.num ∧ Fraction.lt r x := by
  by_cases h : Fraction.le x one
  · have hh := Fraction.magnitudes.le_trans
      (Fraction.magnitudes.lt_implies_le (Fraction.half_lt x hx)) h
    change Fraction.le x.half one at hh
    exact ⟨x.half,⟨by change 0 ≤ x.num; omega,
      by simpa only [Fraction.le,one,Fraction.ofInt,Int.mul_one,Int.one_mul]
      using hh⟩,hx,Fraction.half_lt x hx⟩
  · have h1x : Fraction.le one x := by unfold Fraction.le at *; omega
    exact ⟨one.half,⟨by decide,by decide⟩,by decide,
      Fraction.magnitudes.lt_of_lt_le (Fraction.half_lt one (by decide)) h1x⟩

/-- Every proposed leftmost point has a strictly more leftward point of
the same difference. This is a finite rational construction, not a limit
or topological nonclosure argument. -/
theorem difference_no_minimum : ¬ Minimum difference := by
  rintro (he | ⟨p,hp,hmin⟩)
  · exact he _ (difference_ray one ⟨by decide,by decide⟩ (by decide))
  · obtain ⟨r,hr,hrp,hrlt⟩ := smaller_parameter p.1 (difference_positive p hp)
    exact Fraction.magnitudes.lt_irrefl p.1
      (Fraction.magnitudes.lt_of_le_lt (hmin _ (difference_ray r hr hrp)) hrlt)

theorem difference_unassigned (area : TriangleContent.AreaRules) :
    ¬ ∃ A, (restrict area).HasArea difference A := by
  rintro ⟨A,hA⟩
  exact difference_no_minimum hA.2.2

/-- Both nested sectors retain their normalized areas. Their nonempty
symmetric difference has no assigned area in this same restricted
convention. Thus the displayed elementary rules alone do not imply even
finite sector-difference area existence, relative to any supplied model. -/
theorem relative_countermodel (area : TriangleContent.AreaRules) :
    ∃ bad : TriangleContent.AreaRules,
      bad.HasArea lowerTriangle one.half ∧ bad.HasArea upperTriangle one ∧
      ¬ ∃ A, bad.HasArea difference A := by
  refine ⟨restrict area,?_,?_,difference_unassigned area⟩
  · exact (restrict area).congr_value _ _ _ (by decide)
      ((restrict area).triangle (ray one z) (ray one one) (by decide))
  · exact (restrict area).congr_value _ _ _ (by decide)
      ((restrict area).triangle (ray one z) (ray one two) (by decide))

/-- The separately stated, already existing nested-subtraction convention
does assign this same difference its expected area. This is a successful
elementary repair for the displayed nested example, without adding that
rule to TriangleContent.AreaRules or claiming it suffices for arbitrary B. -/
theorem difference_area_of_subtraction (area : DifferenceAreaRules) :
    area.HasArea difference one.half := by
  have h := area.subtract lowerTriangle upperTriangle one.half one triangle_nested
    (area.congr_value _ _ _ (by decide) (area.triangle (ray one z) (ray one one) (by decide)))
    (area.congr_value _ _ _ (by decide) (area.triangle (ray one z) (ray one two) (by decide)))
  exact area.congr_value _ _ _ (by decide)
    (area.congr_set _ _ _ (fun x => (difference_iff x).symm) h)

end NewtonLimitDynamics.Polygon.AreaDomain
