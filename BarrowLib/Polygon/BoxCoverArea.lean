import BarrowLib.Polygon.TriangleContent

/-! Actual finite unions of rational axis-parallel boxes.
Source: the original English statements and checked coordinate derivations
below. This records project derivation, without historical textual support,
discovery or priority claims. The supplied area convention is the existing
TriangleContent.AreaRules, including translation invariance and separated
cuts. Neither an arbitrary-union rule nor the cover's area is supplied.
Reversed boxes are empty; collapsed boxes and shared boundaries are allowed.
This does not establish the weaker subtraction-only area convention's
sufficiency, existence of a global area convention, or the curve's B.
-/

namespace NewtonLimitDynamics.Polygon.BoxCoverArea
open NewtonLimitDynamics TimeSubdivision HarmonicTimeComparison HarmonicStability
open TriangleContent PolygonFanArea

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den ≤ b.num*a.den))

structure Box where
  left : Fraction
  right : Fraction
  bottom : Fraction
  top : Fraction

def region (B : Box) (x : Point) : Prop :=
  Fraction.le B.left x.1 ∧ Fraction.le x.1 B.right ∧
    Fraction.le B.bottom x.2 ∧ Fraction.le x.2 B.top

def ordered (B : Box) : Prop := Fraction.le B.left B.right ∧ Fraction.le B.bottom B.top

local instance (B : Box) : Decidable (ordered B) :=
  inferInstanceAs (Decidable (Fraction.le B.left B.right ∧ Fraction.le B.bottom B.top))

def value (B : Box) : Fraction :=
  if ordered B then Fraction.mul (durationDifference B.left B.right)
    (durationDifference B.bottom B.top) else Fraction.ofInt 0

def cover (boxes : Nat → Box) (n : Nat) (x : Point) : Prop :=
  ∃ k, k < n ∧ region (boxes k) x

theorem region_respects (B : Box) : RespectsPoints (region B) := by
  intro x y he hx
  exact ⟨Fraction.le_equiv_right hx.1 he.1,
    Fraction.le_equiv_left (Fraction.equiv_symm he.1) hx.2.1,
    Fraction.le_equiv_right hx.2.2.1 he.2,
    Fraction.le_equiv_left (Fraction.equiv_symm he.2) hx.2.2.2⟩

theorem cover_respects (boxes : Nat → Box) (n : Nat) : RespectsPoints (cover boxes n) := by
  rintro x y he ⟨k,hk,hx⟩
  exact ⟨k,hk,region_respects (boxes k) x y he hx⟩

theorem region_empty (B : Box) (h : ¬ ordered B) : ∀ x, ¬ region B x := by
  intro x hx
  exact h ⟨Fraction.magnitudes.le_trans hx.1 hx.2.1,
    Fraction.magnitudes.le_trans hx.2.2.1 hx.2.2.2⟩

/-- A closed translated box has its side-product area, including zero
width or height. Translation is an explicit premise of the existing
convention, not a consequence of nested subtraction. -/
theorem box_area (area : TriangleContent.AreaRules) (B : Box) :
    area.HasArea (region B) (value B) := by
  by_cases h : ordered B
  · have hH : 0 ≤ (durationDifference B.bottom B.top).num :=
      (difference_nonnegative_iff _ _).mpr h.2
    have ha := area.translation
      (MonotoneRectangles.rectangle B.left B.right (durationDifference B.bottom B.top))
      (Fraction.mul (durationDifference B.left B.right) (durationDifference B.bottom B.top))
      (Fraction.ofInt 0,B.bottom)
      (area.rectangle B.left B.right (durationDifference B.bottom B.top) h.1 hH)
    unfold value
    rw [ite_eq_left h]
    apply area.congr_set _ _ _ _ ha
    intro x
    have hx : Fraction.equiv (pointSub x (Fraction.ofInt 0,B.bottom)).1 x.1 := by
      simp only [pointSub,pointAdd,pointNeg,Fraction.equiv,Fraction.add,Fraction.ofInt,
        Int.neg_zero,Int.mul_zero,Int.zero_mul,Int.mul_one,Int.one_mul,Int.add_zero]
    have hy : Fraction.equiv (pointSub x (Fraction.ofInt 0,B.bottom)).2
        (durationDifference B.bottom x.2) := Fraction.equiv_refl _
    change (Fraction.le B.left (pointSub x (Fraction.ofInt 0,B.bottom)).1 ∧
      Fraction.le (pointSub x (Fraction.ofInt 0,B.bottom)).1 B.right ∧
      0 ≤ (pointSub x (Fraction.ofInt 0,B.bottom)).2.num ∧
      Fraction.le (pointSub x (Fraction.ofInt 0,B.bottom)).2
        (durationDifference B.bottom B.top)) ↔ region B x
    constructor
    · rintro ⟨hl,hr,hb,ht⟩
      refine ⟨Fraction.le_equiv_right hl hx,
        Fraction.le_equiv_left (Fraction.equiv_symm hx) hr,
        (difference_nonnegative_iff _ _).mp (Fraction.nonnegative_equiv (Fraction.equiv_symm hy) hb),?_⟩
      have ht' := Fraction.le_equiv_left (Fraction.equiv_symm hy) ht
      have hadd := Fraction.add_le_add_left ht' B.bottom
      exact Fraction.le_equiv_left (Fraction.equiv_symm (add_difference_cancel B.bottom x.2))
        (Fraction.le_equiv_right hadd (add_difference_cancel B.bottom B.top))
    · rintro ⟨hl,hr,hb,ht⟩
      refine ⟨Fraction.le_equiv_right hl (Fraction.equiv_symm hx),
        Fraction.le_equiv_left hx hr,
        Fraction.nonnegative_equiv hy ((difference_nonnegative_iff _ _).mpr hb),?_⟩
      apply Fraction.le_equiv_left hy
      apply Fraction.le_add_cancel_left B.bottom
      exact Fraction.le_equiv_left (add_difference_cancel B.bottom x.2)
        (Fraction.le_equiv_right ht (Fraction.equiv_symm (add_difference_cancel B.bottom B.top)))
  · apply area.congr_set (fun _ => False) _ _ _
      (area.congr_value _ _ _ (by simp only [value,ite_eq_right h]; exact Fraction.equiv_refl _) area.empty)
    intro x
    exact ⟨False.elim,fun hx => False.elim (region_empty B h x hx)⟩

private def minF (a b : Fraction) : Fraction := if Fraction.le a b then a else b
private def maxF (a b : Fraction) : Fraction := if Fraction.le a b then b else a

private theorem le_minF (x a b : Fraction) :
    Fraction.le x (minF a b) ↔ Fraction.le x a ∧ Fraction.le x b := by
  by_cases h : Fraction.le a b
  · simp only [minF,ite_eq_left h]
    exact ⟨fun hx => ⟨hx,Fraction.magnitudes.le_trans hx h⟩,fun hx => hx.1⟩
  · have h' : Fraction.le b a := by unfold Fraction.le at *; omega
    simp only [minF,ite_eq_right h]
    exact ⟨fun hx => ⟨Fraction.magnitudes.le_trans hx h',hx⟩,fun hx => hx.2⟩

private theorem maxF_le (a b x : Fraction) :
    Fraction.le (maxF a b) x ↔ Fraction.le a x ∧ Fraction.le b x := by
  by_cases h : Fraction.le a b
  · simp only [maxF,ite_eq_left h]
    exact ⟨fun hx => ⟨Fraction.magnitudes.le_trans h hx,hx⟩,fun hx => hx.2⟩
  · have h' : Fraction.le b a := by unfold Fraction.le at *; omega
    simp only [maxF,ite_eq_right h]
    exact ⟨fun hx => ⟨hx,Fraction.magnitudes.le_trans h' hx⟩,fun hx => hx.1⟩

def clipLeft (c : Fraction) (B : Box) : Box := {B with right := minF B.right c}
def clipRight (c : Fraction) (B : Box) : Box := {B with left := maxF B.left c}
def clipBelow (c : Fraction) (B : Box) : Box := {B with top := minF B.top c}
def clipAbove (c : Fraction) (B : Box) : Box := {B with bottom := maxF B.bottom c}

theorem clip_left (B : Box) (c : Fraction) (x : Point) :
    region (clipLeft c B) x ↔ region B x ∧ Fraction.le x.1 c := by
  simp only [region,clipLeft,le_minF]
  exact ⟨fun h => ⟨⟨h.1,h.2.1.1,h.2.2⟩,h.2.1.2⟩,
    fun h => ⟨h.1.1,⟨h.1.2.1,h.2⟩,h.1.2.2⟩⟩

theorem clip_right (B : Box) (c : Fraction) (x : Point) :
    region (clipRight c B) x ↔ region B x ∧ Fraction.le c x.1 := by
  simp only [region,clipRight,maxF_le]
  exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,
    fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩

theorem clip_below (B : Box) (c : Fraction) (x : Point) :
    region (clipBelow c B) x ↔ region B x ∧ Fraction.le x.2 c := by
  simp only [region,clipBelow,le_minF]
  exact ⟨fun h => ⟨⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩,h.2.2.2.2⟩,
    fun h => ⟨h.1.1,h.1.2.1,h.1.2.2.1,⟨h.1.2.2.2,h.2⟩⟩⟩

theorem clip_above (B : Box) (c : Fraction) (x : Point) :
    region (clipAbove c B) x ↔ region B x ∧ Fraction.le c x.2 := by
  simp only [region,clipAbove,maxF_le]
  exact ⟨fun h => ⟨⟨h.1,h.2.1,h.2.2.1.1,h.2.2.2⟩,h.2.2.1.2⟩,
    fun h => ⟨h.1.1,h.1.2.1,⟨h.1.2.2.1,h.2⟩,h.1.2.2.2⟩⟩

private theorem cover_clip (boxes : Nat → Box) (n : Nat) (f : Box → Box) (P : Point → Prop)
    (h : ∀ B x, region (f B) x ↔ region B x ∧ P x) (x : Point) :
    cover (fun k => f (boxes k)) n x ↔ cover boxes n x ∧ P x := by
  constructor
  · rintro ⟨k,hk,hx⟩
    obtain ⟨hb,hp⟩ := (h (boxes k) x).mp hx
    exact ⟨⟨k,hk,hb⟩,hp⟩
  · rintro ⟨⟨k,hk,hb⟩,hp⟩
    exact ⟨k,hk,(h (boxes k) x).mpr ⟨hb,hp⟩⟩

theorem cover_left (boxes : Nat → Box) (n : Nat) (c : Fraction) (x : Point) :
    cover (fun k => clipLeft c (boxes k)) n x ↔ cover boxes n x ∧ Fraction.le x.1 c :=
  cover_clip boxes n (clipLeft c) _ (fun B x => clip_left B c x) x

theorem cover_right (boxes : Nat → Box) (n : Nat) (c : Fraction) (x : Point) :
    cover (fun k => clipRight c (boxes k)) n x ↔ cover boxes n x ∧ Fraction.le c x.1 :=
  cover_clip boxes n (clipRight c) _ (fun B x => clip_right B c x) x

theorem cover_below (boxes : Nat → Box) (n : Nat) (c : Fraction) (x : Point) :
    cover (fun k => clipBelow c (boxes k)) n x ↔ cover boxes n x ∧ Fraction.le x.2 c :=
  cover_clip boxes n (clipBelow c) _ (fun B x => clip_below B c x) x

theorem cover_above (boxes : Nat → Box) (n : Nat) (c : Fraction) (x : Point) :
    cover (fun k => clipAbove c (boxes k)) n x ↔ cover boxes n x ∧ Fraction.le c x.2 :=
  cover_clip boxes n (clipAbove c) _ (fun B x => clip_above B c x) x

def middle (B C : Box) : Box := clipLeft B.right (clipRight B.left C)
def below (B C : Box) : Box := clipBelow B.bottom (middle B C)
def above (B C : Box) : Box := clipAbove B.top (middle B C)
def inside (B C : Box) : Box := clipBelow B.top (clipAbove B.bottom (middle B C))

theorem cover_middle (boxes : Nat → Box) (n : Nat) (B : Box) (x : Point) :
    cover (fun k => middle B (boxes k)) n x ↔
      cover boxes n x ∧ Fraction.le B.left x.1 ∧ Fraction.le x.1 B.right := by
  simp only [middle,cover_left,cover_right]
  exact ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩⟩

theorem cover_below_middle (boxes : Nat → Box) (n : Nat) (B : Box) (x : Point) :
    cover (fun k => below B (boxes k)) n x ↔
      cover boxes n x ∧ Fraction.le B.left x.1 ∧ Fraction.le x.1 B.right ∧
        Fraction.le x.2 B.bottom := by
  simp only [below,cover_below,cover_middle]
  exact ⟨fun h => ⟨h.1.1,h.1.2.1,h.1.2.2,h.2⟩,
    fun h => ⟨⟨h.1,h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩

theorem cover_above_middle (boxes : Nat → Box) (n : Nat) (B : Box) (x : Point) :
    cover (fun k => above B (boxes k)) n x ↔
      cover boxes n x ∧ Fraction.le B.left x.1 ∧ Fraction.le x.1 B.right ∧
        Fraction.le B.top x.2 := by
  simp only [above,cover_above,cover_middle]
  exact ⟨fun h => ⟨h.1.1,h.1.2.1,h.1.2.2,h.2⟩,
    fun h => ⟨⟨h.1,h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩

theorem cover_inside (boxes : Nat → Box) (n : Nat) (B : Box) (x : Point) :
    cover (fun k => inside B (boxes k)) n x ↔ cover boxes n x ∧ region B x := by
  simp only [inside,cover_below,cover_above,cover_middle,region]
  exact ⟨fun h => ⟨h.1.1.1,h.1.1.2.1,h.1.1.2.2,h.1.2,h.2⟩,
    fun h => ⟨⟨⟨h.1,h.2.1,h.2.2.1⟩,h.2.2.2.1⟩,h.2.2.2.2⟩⟩

def frame (boxes : Nat → Box) (n : Nat) (B : Box) (I : Point → Prop) (x : Point) : Prop :=
  cover (fun k => clipLeft B.left (boxes k)) n x ∨
    ((cover (fun k => below B (boxes k)) n x ∨
      (I x ∨ cover (fun k => above B (boxes k)) n x)) ∨
      cover (fun k => clipRight B.right (boxes k)) n x)

/-- Four exterior pieces and the old intersection dissect the old cover.
Every piece is still a finite union of boxes, including collapsed pieces. -/
theorem frame_old (boxes : Nat → Box) (n : Nat) (B : Box) (x : Point) :
    cover boxes n x ↔ frame boxes n B (cover (fun k => inside B (boxes k)) n) x := by
  simp only [frame,cover_left,cover_right,cover_below_middle,cover_above_middle,cover_inside]
  constructor
  · intro hx
    by_cases hl : Fraction.le x.1 B.left
    · exact Or.inl ⟨hx,hl⟩
    by_cases hr : Fraction.le B.right x.1
    · exact Or.inr (Or.inr ⟨hx,hr⟩)
    have hl' : Fraction.le B.left x.1 := by unfold Fraction.le at *; omega
    have hr' : Fraction.le x.1 B.right := by unfold Fraction.le at *; omega
    by_cases hb : Fraction.le x.2 B.bottom
    · exact Or.inr (Or.inl (Or.inl ⟨hx,hl',hr',hb⟩))
    by_cases ht : Fraction.le B.top x.2
    · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨hx,hl',hr',ht⟩)))
    have hb' : Fraction.le B.bottom x.2 := by unfold Fraction.le at *; omega
    have ht' : Fraction.le x.2 B.top := by unfold Fraction.le at *; omega
    exact Or.inr (Or.inl (Or.inr (Or.inl ⟨hx,hl',hr',hb',ht'⟩)))
  · intro hx
    rcases hx with h | (h | (h | h)) | h <;> exact h.1

/-- Replacing only the middle intersection by the added box gives the new
union. This is a set identity proved before any area calculation. -/
theorem frame_new (boxes : Nat → Box) (n : Nat) (B : Box) (x : Point) :
    (cover boxes n x ∨ region B x) ↔ frame boxes n B (region B) x := by
  constructor
  · intro hx
    rcases hx with hx | hx
    · have h := (frame_old boxes n B x).mp hx
      rcases h with h | (h | (h | h)) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ((cover_inside boxes n B x).mp h).2)))
      · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl (Or.inr (Or.inl hx)))
  · intro hx
    rcases hx with h | (h | (h | h)) | h
    · exact Or.inl ((cover_left boxes n B.left x).mp h).1
    · exact Or.inl ((cover_below_middle boxes n B x).mp h).1
    · exact Or.inr h
    · exact Or.inl ((cover_above_middle boxes n B x).mp h).1
    · exact Or.inl ((cover_right boxes n B.right x).mp h).1

private theorem respects_or {P Q : Point → Prop}
    (hP : RespectsPoints P) (hQ : RespectsPoints Q) :
    RespectsPoints (fun x => P x ∨ Q x) := by
  intro x y hxy h
  exact h.elim (fun hp => Or.inl (hP x y hxy hp))
    (fun hq => Or.inr (hQ x y hxy hq))

def frameValue (AL AD AI AU AR : Fraction) : Fraction :=
  Fraction.add (Fraction.add AL (Fraction.add AD (Fraction.add AI AU))) AR

/-- Five closed pieces are joined only across their separating horizontal
or vertical cuts. Their shared boundaries are permitted by the convention. -/
theorem frame_area (area : TriangleContent.AreaRules)
    (L D I U R : Point → Prop) (AL AD AI AU AR l r b t : Fraction)
    (hlr : Fraction.le l r) (hbt : Fraction.le b t)
    (hD : RespectsPoints D) (hI : RespectsPoints I) (hU : RespectsPoints U)
    (hLx : ∀ x, L x → Fraction.le x.1 l)
    (hRx : ∀ x, R x → Fraction.le r x.1)
    (hDx : ∀ x, D x → Fraction.le l x.1 ∧ Fraction.le x.1 r)
    (hIx : ∀ x, I x → Fraction.le l x.1 ∧ Fraction.le x.1 r)
    (hUx : ∀ x, U x → Fraction.le l x.1 ∧ Fraction.le x.1 r)
    (hDy : ∀ x, D x → Fraction.le x.2 b)
    (hIy : ∀ x, I x → Fraction.le b x.2 ∧ Fraction.le x.2 t)
    (hUy : ∀ x, U x → Fraction.le t x.2)
    (hAL : area.HasArea L AL) (hAD : area.HasArea D AD)
    (hAI : area.HasArea I AI) (hAU : area.HasArea U AU)
    (hAR : area.HasArea R AR) :
    area.HasArea (fun x => L x ∨ ((D x ∨ (I x ∨ U x)) ∨ R x))
      (frameValue AL AD AI AU AR) := by
  have hIU := horizontal_union area I U AI AU t hI hU
    (fun x hx => (hIy x hx).2) hUy hAI hAU
  have hDIU := horizontal_union area D (fun x => I x ∨ U x) AD (Fraction.add AI AU) b
    hD (respects_or hI hU) hDy
    (by
      intro x hx
      exact hx.elim (fun hi => (hIy x hi).1)
        (fun hu => Fraction.magnitudes.le_trans hbt (hUy x hu)))
    hAD hIU
  have hLDIU := area.separated_union L (fun x => D x ∨ (I x ∨ U x))
    AL (Fraction.add AD (Fraction.add AI AU)) l hLx
    (by
      intro x hx
      rcases hx with hd | hi | hu
      · exact (hDx x hd).1
      · exact (hIx x hi).1
      · exact (hUx x hu).1)
    hAL hDIU
  have hfinal := area.separated_union
    (fun x => L x ∨ (D x ∨ (I x ∨ U x))) R
    (Fraction.add AL (Fraction.add AD (Fraction.add AI AU))) AR r
    (by
      intro x hx
      rcases hx with hleft | hd | hi | hu
      · exact Fraction.magnitudes.le_trans (hLx x hleft) hlr
      · exact (hDx x hd).2
      · exact (hIx x hi).2
      · exact (hUx x hu).2)
    hRx hLDIU hAR
  apply area.congr_set _ _ _ ?_ hfinal
  intro x
  exact ⟨fun h => h.elim
    (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))
    (fun h => Or.inr (Or.inr h)),
    fun h => h.elim (fun h => Or.inl (Or.inl h))
      (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)⟩

private theorem frame_replacement_le
    (AL AD AI AU AR AB : Fraction) (hAI : 0 ≤ AI.num) :
    Fraction.le (frameValue AL AD AB AU AR)
      (Fraction.add (frameValue AL AD AI AU AR) AB) := by
  have hbase := Fraction.le_add_nonnegative (frameValue AL AD AB AU AR) AI hAI
  apply Fraction.le_equiv_right hbase
  simp only [frameValue,Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add]
  ac_nf

private theorem frame_box_area (area : TriangleContent.AreaRules)
    (boxes : Nat → Box) (n : Nat) (B : Box) (hB : ordered B)
    (I : Point → Prop) (hI : RespectsPoints I) (hIB : ∀ x, I x → region B x)
    (AL AD AI AU AR : Fraction)
    (hAL : area.HasArea (cover (fun k => clipLeft B.left (boxes k)) n) AL)
    (hAD : area.HasArea (cover (fun k => below B (boxes k)) n) AD)
    (hAI : area.HasArea I AI)
    (hAU : area.HasArea (cover (fun k => above B (boxes k)) n) AU)
    (hAR : area.HasArea (cover (fun k => clipRight B.right (boxes k)) n) AR) :
    area.HasArea (frame boxes n B I) (frameValue AL AD AI AU AR) := by
  apply frame_area area _ _ I _ _ AL AD AI AU AR B.left B.right B.bottom B.top hB.1 hB.2
    (cover_respects _ _) hI (cover_respects _ _) _ _ _ _ _ _ _ _ hAL hAD hAI hAU hAR
  · intro x hx; exact ((cover_left boxes n B.left x).mp hx).2
  · intro x hx; exact ((cover_right boxes n B.right x).mp hx).2
  · intro x hx
    have h := (cover_below_middle boxes n B x).mp hx
    exact ⟨h.2.1,h.2.2.1⟩
  · intro x hx; exact ⟨(hIB x hx).1,(hIB x hx).2.1⟩
  · intro x hx
    have h := (cover_above_middle boxes n B x).mp hx
    exact ⟨h.2.1,h.2.2.1⟩
  · intro x hx; exact ((cover_below_middle boxes n B x).mp hx).2.2.2
  · intro x hx; exact (hIB x hx).2.2
  · intro x hx; exact ((cover_above_middle boxes n B x).mp hx).2.2.2

theorem cover_succ (boxes : Nat → Box) (n : Nat) (x : Point) :
    cover boxes (n+1) x ↔ cover boxes n x ∨ region (boxes n) x := by
  constructor
  · rintro ⟨k,hk,hx⟩
    by_cases h : k<n
    · exact Or.inl ⟨k,h,hx⟩
    · have he : k=n := by omega
      subst k
      exact Or.inr hx
  · rintro (⟨k,hk,hx⟩ | hx)
    · exact ⟨k,by omega,hx⟩
    · exact ⟨n,by omega,hx⟩

/-- A finite union of arbitrary closed rational boxes has an assigned
nonnegative area at most the sum of their side products. Overlap is handled
by finite dissection, rather than by an assumed subadditivity rule.
The existing translation-and-cut convention remains an explicit premise. -/
theorem cover_area (area : TriangleContent.AreaRules) :
    ∀ n, ∀ boxes : Nat → Box, ∃ A, area.HasArea (cover boxes n) A ∧
      0 ≤ A.num ∧ Fraction.le A (sum (fun k => value (boxes k)) n) := by
  intro n
  induction n with
  | zero =>
    intro boxes
    refine ⟨Fraction.ofInt 0,?_,by decide,Fraction.magnitudes.le_refl _⟩
    apply area.congr_set (fun _ => False) _ _ _ area.empty
    intro x
    exact ⟨False.elim,fun ⟨_,hk,_⟩ => by omega⟩
  | succ n ih =>
    intro boxes
    obtain ⟨A,hA,hA0,hAbound⟩ := ih boxes
    by_cases hB : ordered (boxes n)
    · let B := boxes n
      obtain ⟨AL,hAL,_,_⟩ := ih (fun k => clipLeft B.left (boxes k))
      obtain ⟨AD,hAD,_,_⟩ := ih (fun k => below B (boxes k))
      obtain ⟨AI,hAI,hAI0,_⟩ := ih (fun k => inside B (boxes k))
      obtain ⟨AU,hAU,_,_⟩ := ih (fun k => above B (boxes k))
      obtain ⟨AR,hAR,_,_⟩ := ih (fun k => clipRight B.right (boxes k))
      have holdframe := frame_box_area area boxes n B hB _ (cover_respects _ _)
        (fun x hx => ((cover_inside boxes n B x).mp hx).2) AL AD AI AU AR hAL hAD hAI hAU hAR
      have hold := area.congr_set _ _ _ (fun x => (frame_old boxes n B x).symm) holdframe
      have hEq : Fraction.equiv (frameValue AL AD AI AU AR) A :=
        (Fraction.equiv_iff_mutual_le _ _).mpr
          ⟨area.monotone _ _ _ _ (fun _ h => h) hold hA,
            area.monotone _ _ _ _ (fun _ h => h) hA hold⟩
      have hnewframe := frame_box_area area boxes n B hB _ (region_respects B)
        (fun _ h => h) AL AD (value B) AU AR hAL hAD (box_area area B) hAU hAR
      have hnew := area.congr_set _ _ _
        (fun x => (frame_new boxes n B x).symm.trans (cover_succ boxes n x).symm) hnewframe
      refine ⟨frameValue AL AD (value B) AU AR,hnew,
        RadialSector.assigned_area_nonnegative area.toSectorRules _ _ hnew,?_⟩
      exact Fraction.magnitudes.le_trans
        (Fraction.le_equiv_right (frame_replacement_le AL AD AI AU AR (value B) hAI0)
          (Fraction.add_equiv_right (value B) hEq))
        (Fraction.add_le_add_right hAbound (value B))
    · have he : ∀ x, cover boxes n x ↔ cover boxes (n+1) x := by
        intro x
        rw [cover_succ]
        exact ⟨Or.inl,fun h => h.elim id (fun hx => False.elim (region_empty _ hB x hx))⟩
      refine ⟨A,area.congr_set _ _ _ he hA,hA0,?_⟩
      exact Fraction.le_equiv_right hAbound (Fraction.equiv_symm (by
        simp only [sum,value,ite_eq_right hB]
        exact Fraction.add_zero _))

private theorem abs_le_iff (a R : Fraction) :
    Fraction.le a.abs R ↔ Fraction.le (negF R) a ∧ Fraction.le a R := by
  constructor
  · intro h
    have hn := Fraction.magnitudes.le_trans
      (Fraction.le_equiv_right (Fraction.le_abs (negF a)) (Fraction.abs_neg a)) h
    refine ⟨?_,Fraction.magnitudes.le_trans (Fraction.le_abs a) h⟩
    change (-a.num) * R.den ≤ R.num * a.den at hn
    change (-R.num) * a.den ≤ a.num * R.den
    simp only [Fraction.le,negF,Int.neg_mul,Int.mul_neg] at hn ⊢
    omega
  · intro h
    by_cases ha : 0 ≤ a.num
    · exact Fraction.le_equiv_left (Fraction.abs_of_nonnegative a ha) h.2
    · have hn : 0 ≤ (negF a).num := by change 0 ≤ -a.num; omega
      have he : Fraction.equiv a.abs (negF a) := Fraction.equiv_trans
        (Fraction.equiv_symm (Fraction.abs_neg a)) (Fraction.abs_of_nonnegative (negF a) hn)
      apply Fraction.le_equiv_left he
      have hl := h.1
      simp only [Fraction.le,negF,Int.neg_mul,Int.mul_neg] at hl ⊢
      omega

theorem coordinate_interval (a R x : Fraction) :
    Fraction.le (durationDifference a x).abs R ↔
      Fraction.le (durationDifference R a) x ∧ Fraction.le x (Fraction.add a R) := by
  rw [abs_le_iff]
  constructor
  · intro h
    have hl := Fraction.add_le_add_left h.1 a
    exact ⟨Fraction.le_equiv_right hl (add_difference_cancel a x),
      (difference_le_iff a x R).mp h.2⟩
  · intro h
    exact ⟨Fraction.le_add_cancel_left a _ _
      (Fraction.le_equiv_right h.1 (Fraction.equiv_symm (add_difference_cancel a x))),
      (difference_le_iff a x R).mpr h.2⟩

def square (q : Point) (R : Fraction) : Box :=
  ⟨durationDifference R q.1,Fraction.add q.1 R,
    durationDifference R q.2,Fraction.add q.2 R⟩

theorem square_region (q x : Point) (R : Fraction) :
    region (square q R) x ↔ ConvexCover.SquareContains q R x := by
  exact ⟨fun h => ⟨(coordinate_interval q.1 R x.1).mpr ⟨h.1,h.2.1⟩,
      (coordinate_interval q.2 R x.2).mpr h.2.2⟩,
    fun h => ⟨((coordinate_interval q.1 R x.1).mp h.1).1,
      ((coordinate_interval q.1 R x.1).mp h.1).2,
      (coordinate_interval q.2 R x.2).mp h.2⟩⟩

theorem square_ordered (q : Point) (R : Fraction) (hR : 0 ≤ R.num) : ordered (square q R) := by
  have hcoord (a : Fraction) : Fraction.le (durationDifference a a).abs R := by
    have hz : Fraction.equiv (durationDifference a a).abs (Fraction.ofInt 0) := by
      have he : (durationDifference a a).num = 0 := by
        simp only [durationDifference,negF,Fraction.add,Int.neg_mul]
        omega
      simp only [Fraction.equiv,Fraction.abs,Fraction.ofInt,he,Int.natAbs_zero,
        Int.natCast_zero,Int.zero_mul,Int.mul_zero]
    exact Fraction.le_equiv_left hz
      (by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.mul_one] using hR)
  have hx := (coordinate_interval q.1 R q.1).mp (hcoord q.1)
  have hy := (coordinate_interval q.2 R q.2).mp (hcoord q.2)
  exact ⟨Fraction.magnitudes.le_trans hx.1 hx.2,Fraction.magnitudes.le_trans hy.1 hy.2⟩

theorem square_value (q : Point) (R : Fraction) (hR : 0 ≤ R.num) :
    Fraction.equiv (value (square q R)) (Fraction.mul (Fraction.ofInt 4) (Fraction.mul R R)) := by
  unfold value
  rw [ite_eq_left (square_ordered q R hR)]
  simp only [square]
  have hwidth (a : Fraction) : Fraction.equiv
      (durationDifference (durationDifference R a) (Fraction.add a R))
      (Fraction.mul (Fraction.ofInt 2) R) := by
    simp only [durationDifference,negF,Fraction.equiv,Fraction.add,Fraction.mul,Fraction.ofInt,
      Int.add_mul,Int.mul_add,Int.neg_mul,Int.mul_neg,Int.neg_add,Int.neg_neg,
      Int.one_mul,Int.mul_one]
    ac_nf
    simp only [← Int.mul_assoc]
    omega
  apply Fraction.equiv_trans (Fraction.mul_equiv (hwidth q.1) (hwidth q.2))
  simp only [Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
  ac_nf

theorem square_cover (q : Nat → Point) (R : Fraction) (n : Nat) (x : Point) :
    cover (fun k => square (q k) R) n x ↔ ConvexCover.SquareCover q R n x := by
  constructor
  · rintro ⟨k,hk,hx⟩
    exact ⟨k,hk,(square_region (q k) x R).mp hx⟩
  · rintro ⟨k,hk,hx⟩
    exact ⟨k,hk,(square_region (q k) x R).mpr hx⟩

/-- The actual finite square-cover union has a constructed nonnegative area
bounded by the sum of its square side products. Arbitrary overlap, translated
centres and zero radius are allowed. No difference-area assignment is used. -/
theorem square_cover_area (area : TriangleContent.AreaRules) (q : Nat → Point)
    (R : Fraction) (hR : 0 ≤ R.num) (n : Nat) :
    ∃ A, area.HasArea (ConvexCover.SquareCover q R n) A ∧ 0 ≤ A.num ∧
      Fraction.le A (sum (fun _ => Fraction.mul (Fraction.ofInt 4) (Fraction.mul R R)) n) := by
  obtain ⟨A,hA,hA0,hbound⟩ := cover_area area n (fun k => square (q k) R)
  exact ⟨A,area.congr_set _ _ _ (square_cover q R n) hA,hA0,
    Fraction.le_equiv_right hbound (sum_congr _ _ (fun k => square_value (q k) R hR) n)⟩

end NewtonLimitDynamics.Polygon.BoxCoverArea
