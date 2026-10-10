import BarrowLib.Polygon.RadialSector

/-!
Finite affine subgraph area by rectangle and triangle dissection.

Source of the precise coordinate statements and derivations: the original
English statements and Lean proofs in this file. This records project
reconstruction, not historical textual support, discovery or priority.

The supplied area convention extends SectorFan.AreaRules by translation
invariance. Triangle normalization and dissection additivity remain explicit
geometric premises. Their classical background is Euclid I.41 and the Common
Notions, quoted in Greek in SectorFan.lean. Translation is the coordinate
interpretation of congruent figures, not a new quotation attributed to Euclid.
https://physics.ntua.gr/mourmouras/euclid/book1/postulate41.html
Ἐὰν παραλληλόγραμμον τριγώνῳ βάσιν τε ἔχῃ τὴν αὐτὴν καὶ ἐν ταῖς
αὐταῖς παραλλήλοις ᾖ, διπλάσιόν ἐστι τὸ παραλληλόγραμμον τοῦ τριγώνου.

The affine subgraph's area is derived, not a field of the convention.
Zero slopes and zero widths are allowed. The horizontal dissection always
uses the nonzero direction (1,0). No area on arbitrary curved sets is supplied.
-/
namespace NewtonLimitDynamics.Polygon.TriangleContent
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open SupportingTangents ConvexCover

def translate (c : Point) (U : Point → Prop) (z : Point) : Prop := U (pointSub z c)

structure AreaRules extends toSectorRules : SectorFan.AreaRules where
  translation : ∀ U A c, HasArea U A → HasArea (translate c U) A

def RespectsPoints (U : Point → Prop) : Prop :=
  ∀ x y, pointEquiv x y → U x → U y

private theorem undo_translation (x c : Point) :
    pointEquiv (pointSub (pointSub x c) (pointNeg c)) x := by
  constructor <;>
    simp only [pointSub, pointAdd, pointNeg, Fraction.equiv, Fraction.add,
      Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_neg] <;>
    ac_nf <;> omega

private theorem translated_y (x : Point) (H : Fraction) :
    Fraction.equiv (pointSub x (pointNeg (Fraction.ofInt 0,H))).2
      (Fraction.add H x.2) := by
  simp only [pointSub, pointAdd, pointNeg, Fraction.equiv, Fraction.add,
    Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  ac_nf

private theorem horizontal_right (x : Point) :
    Fraction.equiv (det x (Fraction.ofInt 1,Fraction.ofInt 0)) (negF x.2) := by
  simp only [det, negF, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
    Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one, Int.zero_add, Int.add_zero]
  ac_nf

private theorem horizontal_left (x : Point) :
    Fraction.equiv (det (Fraction.ofInt 1,Fraction.ofInt 0) x) x.2 := by
  simp only [det, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
    Int.zero_mul, Int.mul_zero, Int.one_mul, Int.mul_one, Int.zero_add, Int.add_zero,
    Int.neg_zero]
  ac_nf

/-- Additivity at any horizontal cut follows from translation and the
existing radial-cut convention. Representative invariance is proved for
each consuming figure; it is not an additional area axiom. -/
theorem horizontal_union (area : AreaRules) (U V : Point → Prop) (A B H : Fraction)
    (hU : RespectsPoints U) (hV : RespectsPoints V)
    (hbelow : ∀ x, U x → Fraction.le x.2 H)
    (habove : ∀ x, V x → Fraction.le H x.2)
    (hA : area.HasArea U A) (hB : area.HasArea V B) :
    area.HasArea (fun x => U x ∨ V x) (Fraction.add A B) := by
  let c : Point := (Fraction.ofInt 0,H)
  have hU0 := area.translation U A (pointNeg c) hA
  have hV0 := area.translation V B (pointNeg c) hB
  have h0 := area.radial_union (translate (pointNeg c) U) (translate (pointNeg c) V)
    A B (Fraction.ofInt 1,Fraction.ofInt 0) (Or.inl (by decide)) ?_ ?_ hU0 hV0
  · have h1 := area.translation _ _ c h0
    apply area.congr_set _ _ _ _ h1
    intro x
    have he := undo_translation x c
    change (U (pointSub (pointSub x c) (pointNeg c)) ∨
      V (pointSub (pointSub x c) (pointNeg c))) ↔ U x ∨ V x
    exact ⟨fun h => h.elim (fun h => Or.inl (hU _ _ he h))
      (fun h => Or.inr (hV _ _ he h)),
      fun h => h.elim (fun h => Or.inl (hU _ _ (pointEquiv_symm he) h))
        (fun h => Or.inr (hV _ _ (pointEquiv_symm he) h))⟩
  · intro x hx
    have hb := Fraction.le_equiv_left (Fraction.equiv_symm (translated_y x H)) (hbelow _ hx)
    have hn := Fraction.le_add_cancel_left H x.2 (Fraction.ofInt 0)
      (Fraction.le_equiv_right hb (Fraction.equiv_symm (Fraction.add_zero H)))
    have hn' : 0 ≤ (negF x.2).num := by
      simp only [Fraction.le, Fraction.ofInt, Int.mul_one, Int.zero_mul] at hn
      change 0 ≤ -x.2.num
      omega
    exact Fraction.nonnegative_equiv (horizontal_right x) hn'
  · intro x hx
    have hb := Fraction.le_equiv_right (habove _ hx) (translated_y x H)
    have hn := Fraction.le_add_cancel_left H (Fraction.ofInt 0) x.2
      (Fraction.le_equiv_left (Fraction.add_zero H) hb)
    have hn' : 0 ≤ x.2.num := by
      simpa only [Fraction.le, Fraction.ofInt, Int.mul_one, Int.zero_mul] using hn
    exact Fraction.nonnegative_equiv (horizontal_left x) hn'

def Ramp (s W : Fraction) (z : Point) : Prop :=
  0 ≤ z.1.num ∧ Fraction.le z.1 W ∧ 0 ≤ z.2.num ∧ Fraction.le z.2 (Fraction.mul s z.1)

private theorem zero_affine (u x : Fraction) :
    Fraction.equiv (affine u (Fraction.ofInt 0) x) (Fraction.mul u x) := by
  simp only [affine, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
    Int.mul_zero, Int.zero_mul, Int.zero_add, Int.mul_one]
  ac_nf

private theorem ramp_parameters (r t s W : Fraction) :
    pointEquiv (pointScale r (lerp t (W,Fraction.ofInt 0) (W,Fraction.mul s W)))
      (Fraction.mul r W, Fraction.mul t (Fraction.mul s (Fraction.mul r W))) := by
  constructor
  · exact Fraction.mul_equiv_left r (RadialSector.affine_constant t W)
  · simp only [pointScale, lerp, pointAdd, Fraction.equiv, Fraction.add, Fraction.mul,
      Fraction.ofInt, Int.mul_zero, Int.zero_mul, Int.zero_add, Int.mul_one, Int.one_mul]
    ac_nf

/-- A right triangle is exactly the subgraph of a nonnegative linear ramp.
The inverse uses interval interpolation rather than division by width or
slope, so collapsed triangles require no exception or new premise. -/
theorem ramp_triangle (s W : Fraction) (hs : 0 ≤ s.num) (hW : 0 ≤ W.num) (z : Point) :
    SectorFan.Triangle (W,Fraction.ofInt 0) (W,Fraction.mul s W) z ↔ Ramp s W z := by
  constructor
  · intro hz
    obtain ⟨r,t,hr,ht,he⟩ := (RadialSector.triangle_radial _ _ z).mp hz
    have he' := pointEquiv_trans he (ramp_parameters r t s W)
    have hX := Fraction.nonnegative_mul r W hr.1 hW
    have hSX := Fraction.nonnegative_mul s (Fraction.mul r W) hs hX
    have hr1 : Fraction.le r (Fraction.ofInt 1) := by
      simpa only [Fraction.le, Fraction.ofInt, Int.mul_one, Int.one_mul] using hr.2
    have ht1 : Fraction.le t (Fraction.ofInt 1) := by
      simpa only [Fraction.le, Fraction.ofInt, Int.mul_one, Int.one_mul] using ht.2
    have one_mul (v : Fraction) : Fraction.equiv (Fraction.mul (Fraction.ofInt 1) v) v := by
      simp only [Fraction.equiv, Fraction.mul, Fraction.ofInt, Int.one_mul, Int.mul_one]
    exact ⟨Fraction.nonnegative_equiv he'.1 hX,
      Fraction.le_equiv_left he'.1 (Fraction.le_equiv_right
        (Fraction.mul_le_mul_nonnegative hr1 W hW) (one_mul W)),
      Fraction.nonnegative_equiv he'.2 (Fraction.nonnegative_mul _ _ ht.1 hSX),
      Fraction.le_equiv_left he'.2 (Fraction.le_equiv_right
        (Fraction.le_equiv_right (Fraction.mul_le_mul_nonnegative ht1 _ hSX) (one_mul _))
        (Fraction.mul_equiv_left s (Fraction.equiv_symm he'.1)))⟩
  · rintro ⟨hX,hXW,hY,hYX⟩
    have hx0 : Fraction.le (Fraction.ofInt 0) z.1 := by
      simpa only [Fraction.le, Fraction.ofInt, Int.mul_one, Int.zero_mul] using hX
    have hy0 : Fraction.le (Fraction.ofInt 0) z.2 := by
      simpa only [Fraction.le, Fraction.ofInt, Int.mul_one, Int.zero_mul] using hY
    obtain ⟨r,hr,heX⟩ := RadialSector.interval_parameter (Fraction.ofInt 0) W z.1 hx0 hXW
    obtain ⟨t,ht,heY⟩ := RadialSector.interval_parameter (Fraction.ofInt 0)
      (Fraction.mul s z.1) z.2 hy0 hYX
    have hXr := Fraction.equiv_trans (Fraction.equiv_symm (zero_affine r W)) heX
    have hYt := Fraction.equiv_trans (Fraction.equiv_symm (zero_affine t _)) heY
    apply (RadialSector.triangle_radial _ _ z).mpr
    refine ⟨r,t,hr,ht,pointEquiv_trans ?_ (pointEquiv_symm (ramp_parameters r t s W))⟩
    exact ⟨Fraction.equiv_symm hXr, Fraction.equiv_trans (Fraction.equiv_symm hYt)
      (Fraction.mul_equiv_left t (Fraction.mul_equiv_left s (Fraction.equiv_symm hXr)))⟩

/-- The ramp area follows from triangle normalization and the proved set
identity. No ramp-area assignment is supplied. -/
theorem ramp_area (area : AreaRules) (s W : Fraction) (hs : 0 ≤ s.num) (hW : 0 ≤ W.num) :
    area.HasArea (Ramp s W) (Fraction.mul W (Fraction.mul s W)).half := by
  have he : Fraction.equiv (det (W,Fraction.ofInt 0) (W,Fraction.mul s W))
      (Fraction.mul W (Fraction.mul s W)) := by
    simp only [det, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
      Int.mul_zero, Int.zero_mul, Int.neg_zero, Int.add_zero, Int.mul_one, Int.one_mul]
    ac_nf
  have ht := area.triangle (W,Fraction.ofInt 0) (W,Fraction.mul s W)
    (Fraction.nonnegative_equiv he (Fraction.nonnegative_mul _ _ hW
      (Fraction.nonnegative_mul _ _ hs hW)))
  exact area.congr_value _ _ _ ((show Fraction.equiv (Fraction.half _) (Fraction.half _) from by
      apply (Fraction.equiv_iff_toRat _ _).mpr
      simp only [Fraction.toRat_half]
      exact congrArg (fun q : Rat => q / 2) ((Fraction.equiv_iff_toRat _ _).mp he)))
    (area.congr_set _ _ _ (ramp_triangle s W hs hW) ht)

def height (l H s x : Fraction) : Fraction :=
  Fraction.add H (Fraction.mul s (durationDifference l x))

def UnderLine (l r H s : Fraction) (z : Point) : Prop :=
  Fraction.le l z.1 ∧ Fraction.le z.1 r ∧ 0 ≤ z.2.num ∧ Fraction.le z.2 (height l H s z.1)

theorem difference_le_iff (a b c : Fraction) :
    Fraction.le (durationDifference a b) c ↔ Fraction.le b (Fraction.add a c) := by
  constructor
  · exact difference_add_bound a b c
  · intro h
    exact Fraction.le_add_cancel_left a _ _
      (Fraction.le_equiv_left (add_difference_cancel a b) h)

private theorem rectangle_respects (l r H : Fraction) :
    RespectsPoints (MonotoneRectangles.rectangle l r H) := by
  intro x y he hx
  exact ⟨Fraction.le_equiv_right hx.1 he.1,
    Fraction.le_equiv_left (Fraction.equiv_symm he.1) hx.2.1,
    Fraction.nonnegative_equiv (Fraction.equiv_symm he.2) hx.2.2.1,
    Fraction.le_equiv_left (Fraction.equiv_symm he.2) hx.2.2.2⟩

private theorem ramp_respects (s W : Fraction) : RespectsPoints (Ramp s W) := by
  intro x y he hx
  exact ⟨Fraction.nonnegative_equiv (Fraction.equiv_symm he.1) hx.1,
    Fraction.le_equiv_left (Fraction.equiv_symm he.1) hx.2.1,
    Fraction.nonnegative_equiv (Fraction.equiv_symm he.2) hx.2.2.1,
    Fraction.le_equiv_left (Fraction.equiv_symm he.2)
      (Fraction.le_equiv_right hx.2.2.2 (Fraction.mul_equiv_left s he.1))⟩

private theorem translate_respects (c : Point) (U : Point → Prop)
    (hU : RespectsPoints U) : RespectsPoints (translate c U) := by
  intro x y he hx
  exact hU _ _ (pointSub_congr he ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩) hx

/-- The actual affine subgraph is a rectangle and a translated ramp
triangle. Their common horizontal boundary is allowed by dissection. -/
theorem underLine_dissection (l r H s : Fraction) (hH : 0 ≤ H.num) (hs : 0 ≤ s.num)
    (z : Point) :
    UnderLine l r H s z ↔ MonotoneRectangles.rectangle l r H z ∨
      translate (l,H) (Ramp s (durationDifference l r)) z := by
  constructor
  · rintro ⟨hl,hr,hy,hheight⟩
    by_cases hh : Fraction.le z.2 H
    · exact Or.inl ⟨hl,hr,hy,hh⟩
    · have hHy : Fraction.le H z.2 := by unfold Fraction.le at *; omega
      right
      change Ramp s (durationDifference l r) (durationDifference l z.1,durationDifference H z.2)
      exact ⟨(difference_nonnegative_iff _ _).mpr hl,
        Fraction.add_le_add_right hr (negF l),
        (difference_nonnegative_iff _ _).mpr hHy,
        (difference_le_iff _ _ _).mpr hheight⟩
  · intro hz
    rcases hz with hz | hz
    · exact ⟨hz.1,hz.2.1,hz.2.2.1,
        Fraction.magnitudes.le_trans hz.2.2.2
          (Fraction.le_add_nonnegative H _ (Fraction.nonnegative_mul _ _ hs
            ((difference_nonnegative_iff _ _).mpr hz.1)))⟩
    · change Ramp s (durationDifference l r)
        (durationDifference l z.1,durationDifference H z.2) at hz
      have hl := (difference_nonnegative_iff _ _).mp hz.1
      have hr := Fraction.le_equiv_right (difference_add_bound _ _ _ hz.2.1)
        (add_difference_cancel l r)
      have hHy := (difference_nonnegative_iff _ _).mp hz.2.2.1
      exact ⟨hl,hr,Fraction.nonnegative_of_le hH hHy,
        (difference_le_iff _ _ _).mp hz.2.2.2⟩

theorem trapezoid_identity (W H s : Fraction) :
    Fraction.equiv
      (Fraction.add (Fraction.mul W H) (Fraction.mul W (Fraction.mul s W)).half)
      (Fraction.mul W (Fraction.add H (Fraction.add H (Fraction.mul s W))).half) := by
  simp only [Fraction.equiv, Fraction.add, Fraction.mul, Fraction.half,
    show (2 : Int) = 1+1 by rfl, Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one]
  ac_nf

/-- The trapezoid area is width times the mean of its endpoint heights,
derived from the dissection. No trapezoid normalization is assumed. -/
theorem underLine_area (area : AreaRules) (l r H s : Fraction)
    (hlr : Fraction.le l r) (hH : 0 ≤ H.num) (hs : 0 ≤ s.num) :
    area.HasArea (UnderLine l r H s)
      (Fraction.mul (durationDifference l r) (Fraction.add H (height l H s r)).half) := by
  have hW := (difference_nonnegative_iff l r).mpr hlr
  have hrectangle := area.rectangle l r H hlr hH
  have hramp := area.translation (Ramp s (durationDifference l r))
    (Fraction.mul (durationDifference l r) (Fraction.mul s (durationDifference l r))).half
    (l,H) (ramp_area area s (durationDifference l r) hs hW)
  have hu := horizontal_union area (MonotoneRectangles.rectangle l r H)
    (translate (l,H) (Ramp s (durationDifference l r))) _ _ H
    (rectangle_respects l r H) (translate_respects _ _ (ramp_respects _ _))
    (fun _ hx => hx.2.2.2) (fun x hx => ?_) hrectangle hramp
  · exact area.congr_value _ _ _ (trapezoid_identity (durationDifference l r) H s)
      (area.congr_set _ _ _ (fun z => (underLine_dissection l r H s hH hs z).symm) hu)
  · change Ramp s (durationDifference l r)
      (durationDifference l x.1,durationDifference H x.2) at hx
    exact (difference_nonnegative_iff H x.2).mp hx.2.2.1

end NewtonLimitDynamics.Polygon.TriangleContent
