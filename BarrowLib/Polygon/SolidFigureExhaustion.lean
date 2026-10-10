import BarrowLib.Polygon.CurvilinearCoincidence

/-! Filled-figure exhaustion by finite rectangular dissections.

Provenance: the exact English statements and elementary proofs below are
project derivations, without an external exact-result or priority claim.
The partial finite-content convention is explicit: rectangle normalization,
finite addition across shared straight edges, and monotonicity. It assigns
no content to the supplied curved figure. Core field/order laws encode the
coordinates; no completeness, compactness or curve-existence theorem is used.

`Solid` is the editorial domain of a filled figure: every neighborhood of
every figure point contains a positive rectangle wholly in the figure.
`Separated` excludes outside limit points. Neither condition asserts that
the approximating figures converge. Isolated hairs are excluded explicitly.
Newton's exact Latin and edition-local clients remain in Historical/. -/

namespace NewtonLimitDynamics.Polygon.SolidFigureExhaustion
open Lean.Grind Std CurvilinearCoincidence

variable {K : Type} [Field K] [LE K] [LT K]
  [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K]

structure Box (K : Type) where
  left : K
  right : K
  bottom : K
  top : K

def Box.region (B : Box K) (x : K × K) : Prop :=
  B.left≤x.1 ∧ x.1≤B.right ∧ B.bottom≤x.2 ∧ x.2≤B.top

def Box.ordered (B : Box K) : Prop := B.left≤B.right ∧ B.bottom≤B.top
def Box.positive (B : Box K) : Prop := B.left<B.right ∧ B.bottom<B.top
def Box.value (B : Box K) : K := (B.right-B.left)*(B.top-B.bottom)

/-- A finite union of coordinate lines; only shared straight edges are
ignored in finite addition. This is not a rule for arbitrary null sets. -/
def Thin (U : (K × K) → Prop) : Prop :=
  ∃ vertical horizontal : List K, ∀ x, U x → x.1∈vertical ∨ x.2∈horizontal

/-- A partial finite-content convention, not area existence for curved
sets. All uses below start from rectangles or supplied finite inner sums. -/
structure ContentRules (K : Type) [Field K] [LE K] where
  HasContent : ((K × K) → Prop) → K → Prop
  empty : HasContent (fun _ => False) 0
  congr_set : ∀ U V A, (∀ x, U x ↔ V x) → HasContent U A → HasContent V A
  rectangle : ∀ B : Box K, B.ordered → HasContent B.region B.value
  union : ∀ U V A B, Thin (fun x => U x ∧ V x) →
    HasContent U A → HasContent V B → HasContent (fun x => U x ∨ V x) (A+B)
  monotone : ∀ U V A B, (∀ x, U x → V x) →
    HasContent U A → HasContent V B → A≤B

def cover (boxes : List (Box K)) (x : K × K) : Prop :=
  ∃ B, B∈boxes ∧ B.region x

/-- Each new rectangle meets the preceding finite union only on finitely
many coordinate lines. This is a finite geometric dissection certificate. -/
def Dissects (inner : (K × K) → Prop) : List (Box K) → Prop
  | [] => True
  | B::rest => Thin (fun x => inner x ∧ B.region x) ∧
      Dissects (fun x => inner x ∨ B.region x) rest

omit [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K] in
/-- The finite union's content is derived by repeated addition. Its value
and the eventual vanishing of a gap are not fields of the certificate. -/
theorem dissection_content (area : ContentRules K) (inner : (K × K) → Prop)
    (A : K) (boxes : List (Box K)) (hA : area.HasContent inner A)
    (hboxes : ∀ B, B∈boxes → B.ordered) (hdissect : Dissects inner boxes) :
    area.HasContent (fun x => inner x ∨ cover boxes x)
      (A+(boxes.map Box.value).sum) := by
  induction boxes generalizing inner A with
  | nil =>
    simp only [List.map_nil,List.sum_nil,Semiring.add_zero]
    apply area.congr_set inner _ _ ?_ hA
    intro x
    constructor
    · exact Or.inl
    · rintro (hx | ⟨B,hB,_⟩)
      · exact hx
      · nomatch hB
  | cons B rest ih =>
    have hB := area.rectangle B (hboxes B (by simp only [List.mem_cons, true_or]))
    have hAB := area.union inner B.region A B.value hdissect.1 hA hB
    have hrest := ih (fun x => inner x ∨ B.region x) (A+B.value) hAB
      (fun C hC => hboxes C (by simp only [List.mem_cons]; exact Or.inr hC)) hdissect.2
    have he : ∀ x, ((inner x ∨ B.region x) ∨ cover rest x) ↔
        inner x ∨ cover (B::rest) x := by
      intro x
      simp only [cover,List.mem_cons]
      grind only
    have hv : (A+B.value)+(rest.map Box.value).sum =
        A+((B::rest).map Box.value).sum := by
      simp only [List.map_cons,List.sum_cons]
      grind
    rw [hv] at hrest
    exact area.congr_set _ _ _ he hrest

/-- A maximum-width certificate for the actual finite difference: the
outer union is obtained by adjoining the displayed gap rectangles. The
fixed height bounds their summed heights, as in Lemma III's FAaf rectangle.
No numeric gap identity or limiting conclusion is supplied. -/
structure GapDissection (inner outer : (K × K) → Prop) (mesh height : K) where
  boxes : List (Box K)
  ordered : ∀ B, B∈boxes → B.ordered
  dissects : Dissects inner boxes
  union_eq : ∀ x, outer x ↔ inner x ∨ cover boxes x
  mesh_nonnegative : 0≤mesh
  width_bound : ∀ B, B∈boxes → B.right-B.left≤mesh
  height_bound : (boxes.map (fun B => B.top-B.bottom)).sum≤height

/-- Finite side-product comparison, derived by induction and core ordered
multiplication. This is the maximum-width rectangle comparison, before any
limit is taken. -/
theorem dissection_gap_bound {inner outer : (K × K) → Prop} {mesh height : K}
    (d : GapDissection inner outer mesh height) :
    (d.boxes.map Box.value).sum≤mesh*height := by
  have hb : ∀ boxes : List (Box K),
      (∀ B, B∈boxes → B.ordered ∧ B.right-B.left≤mesh) →
      (boxes.map Box.value).sum≤mesh*(boxes.map (fun B => B.top-B.bottom)).sum := by
    intro boxes h
    induction boxes with
    | nil => simp only [List.map_nil,List.sum_nil,Semiring.mul_zero]; exact Std.le_refl _
    | cons B rest ih =>
      have hB := h B (by simp only [List.mem_cons,true_or])
      have hm := OrderedRing.mul_le_mul_of_nonneg_right hB.2
        (show 0≤B.top-B.bottom by grind only [Box.ordered])
      have hr := ih (fun C hC => h C (by simp only [List.mem_cons]; exact Or.inr hC))
      simp only [List.map_cons,List.sum_cons,Box.value]
      grind
  have h := hb d.boxes (fun B hB => ⟨d.ordered B hB,d.width_bound B hB⟩)
  exact Std.le_trans h
    (OrderedRing.mul_le_mul_of_nonneg_left d.height_bound d.mesh_nonnegative)

omit [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K] in
/-- The finite enclosing figure has its content from the dissection; the
curve itself receives no content assignment. -/
theorem enclosing_content (area : ContentRules K) {inner outer : (K × K) → Prop}
    {A mesh height : K} (hA : area.HasContent inner A)
    (d : GapDissection inner outer mesh height) :
    area.HasContent outer (A+(d.boxes.map Box.value).sum) :=
  area.congr_set _ _ _ (fun x => (d.union_eq x).symm)
    (dissection_content area inner A d.boxes hA d.ordered d.dissects)

/-- Shrinking maximum widths make the *derived* finite dissection gap
vanish. The fixed height is nonnegative; no Archimedean premise is needed. -/
theorem dissection_gap_shrinks (inner outer : Nat → (K × K) → Prop)
    (mesh : Nat → K) (height : K) (hheight : 0≤height)
    (d : ∀ k, GapDissection (inner k) (outer k) (mesh k) height)
    (hmesh : Shrinks mesh) :
    Shrinks (fun k => ((d k).boxes.map Box.value).sum) := by
  intro eps heps
  by_cases hh : height=0
  · obtain ⟨N,_⟩ := hmesh eps heps
    refine ⟨N,fun k _ => ?_⟩
    have hb := dissection_gap_bound (d k)
    have hz : mesh k*height=0 := by rw [hh,Semiring.mul_zero]
    grind only
  · have hp : 0<height := by grind only
    have hnz : height≠0 := hh
    have hinv := Field.IsOrdered.inv_pos_iff.mpr hp
    have hd : 0<eps/height := by
      simpa only [Field.div_eq_mul_inv] using OrderedRing.mul_pos heps hinv
    obtain ⟨N,hN⟩ := hmesh (eps/height) hd
    refine ⟨N,fun k hk => ?_⟩
    have hb := dissection_gap_bound (d k)
    have hm := OrderedRing.mul_lt_mul_of_pos_right (hN k hk) hp
    have he : (eps/height)*height=eps := by
      rw [Field.div_eq_mul_inv,Semiring.mul_assoc,Field.inv_mul_cancel hnz,Semiring.mul_one]
    rw [he] at hm
    exact Std.lt_of_le_of_lt hb hm

def Solid (figure : (K × K) → Prop) : Prop :=
  ∀ x, figure x → ∀ eps, 0<eps → ∃ B : Box K,
    B.positive ∧ (∀ y, B.region y → figure y) ∧
      (∀ y, B.region y → Near eps x y)

def Separated (figure : (K × K) → Prop) : Prop :=
  ∀ x, ¬figure x → ∃ eps, 0<eps ∧ ∀ y, figure y → ¬Near eps x y

/-- Every point of a nondegenerate closed interval has a positive smaller
interval within any prescribed neighborhood, including at either endpoint. -/
private theorem interval_rectangle (l r t eps : K) (hlr : l<r)
    (hl : l≤t) (hr : t≤r) (heps : 0<eps) :
    ∃ u v, u<v ∧ l≤u ∧ v≤r ∧ ∀ s, u≤s → s≤v → -eps<t-s ∧ t-s<eps := by
  classical
  let u := if t-eps/2≤l then l else t-eps/2
  let v := if r≤t+eps/2 then r else t+eps/2
  refine ⟨u,v,?_,?_,?_,?_⟩
  · dsimp only [u,v]; grind
  · dsimp only [u]; grind
  · dsimp only [v]; grind
  · intro s hs ht
    dsimp only [u,v] at hs ht
    grind

/-- Positive closed rectangles satisfy the filled-figure domain condition;
it is proved rather than assumed for the finite non-graph controls. -/
theorem box_solid (B : Box K) (hB : B.positive) : Solid B.region := by
  intro x hx eps heps
  obtain ⟨l,r,hlr,hl,hr,hxnear⟩ := interval_rectangle B.left B.right x.1 eps
    hB.1 hx.1 hx.2.1 heps
  obtain ⟨b,t,hbt,hb,ht,hynear⟩ := interval_rectangle B.bottom B.top x.2 eps
    hB.2 hx.2.2.1 hx.2.2.2 heps
  refine ⟨⟨l,r,b,t⟩,⟨hlr,hbt⟩,?_,?_⟩
  · intro y hy
    obtain ⟨hyl,hyr,hyb,hyt⟩ := hy
    exact ⟨by grind only,by grind only,by grind only,by grind only⟩
  · intro y hy
    exact ⟨(hxnear y.1 hy.1 hy.2.1).1,(hxnear y.1 hy.1 hy.2.1).2,
      (hynear y.2 hy.2.2.1 hy.2.2.2).1,(hynear y.2 hy.2.2.1 hy.2.2.2).2⟩

/-- Every closed rectangle, including a collapsed one, excludes outside
limit points by a positive coordinate separation. -/
theorem box_separated (B : Box K) : Separated B.region := by
  intro x hx
  by_cases hl : x.1<B.left
  · refine ⟨(B.left-x.1)/2,by grind,?_⟩
    intro y hy hn
    have := hy.1
    have := hn.1
    grind
  · by_cases hr : B.right<x.1
    · refine ⟨(x.1-B.right)/2,by grind,?_⟩
      intro y hy hn
      have := hy.2.1
      have := hn.2.1
      grind
    · by_cases hb : x.2<B.bottom
      · refine ⟨(B.bottom-x.2)/2,by grind,?_⟩
        intro y hy hn
        have := hy.2.2.1
        have := hn.2.2.1
        grind
      · have ht : B.top<x.2 := by
          apply Classical.byContradiction
          intro hnot
          exact hx ⟨by grind only,by grind only,by grind only,by grind only⟩
        refine ⟨(x.2-B.top)/2,by grind,?_⟩
        intro y hy hn
        have := hy.2.2.2
        have := hn.2.2.2
        grind

omit [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K] in
/-- A finite two-piece union retains local positive rectangles. No patch
convergence or global graph is used. -/
theorem solid_union (U V : (K × K) → Prop) (hU : Solid U) (hV : Solid V) :
    Solid (fun x => U x ∨ V x) := by
  intro x hx eps heps
  rcases hx with hx | hx
  · obtain ⟨B,hB,hin,hn⟩ := hU x hx eps heps
    exact ⟨B,hB,fun y hy => Or.inl (hin y hy),hn⟩
  · obtain ⟨B,hB,hin,hn⟩ := hV x hx eps heps
    exact ⟨B,hB,fun y hy => Or.inr (hin y hy),hn⟩

/-- Outside separation is preserved by finite union. No compactness or
finite covering theorem is needed for exact pointwise ultimate membership. -/
theorem separated_union (U V : (K × K) → Prop)
    (hU : Separated U) (hV : Separated V) : Separated (fun x => U x ∨ V x) := by
  classical
  intro x hx
  obtain ⟨du,hu,hnu⟩ := hU x (fun h => hx (Or.inl h))
  obtain ⟨dv,hv,hnv⟩ := hV x (fun h => hx (Or.inr h))
  let d := if du≤dv then du else dv
  have hd : 0<d ∧ d≤du ∧ d≤dv := by dsimp only [d]; grind only
  refine ⟨d,hd.1,?_⟩
  intro y hy hn
  rcases hy with hy | hy
  · apply hnu y hy
    obtain ⟨ha,hb,hc,he⟩ := hn
    exact ⟨by grind only,by grind only,by grind only,by grind only⟩
  · apply hnv y hy
    obtain ⟨ha,hb,hc,he⟩ := hn
    exact ⟨by grind only,by grind only,by grind only,by grind only⟩

/-- If a positive rectangle in the figure misses an inscribed finite sum,
finite addition and containment force its full side product below the gap.
This comparison is proved, rather than supplied as an exhaustion oracle. -/
theorem missed_rectangle_le_gap (area : ContentRules K)
    (inner figure outer : (K × K) → Prop) (A C : K) (B : Box K)
    (hA : area.HasContent inner A) (hC : area.HasContent outer C)
    (hB : B.positive) (hinner : ∀ x, inner x → figure x)
    (houter : ∀ x, figure x → outer x) (hin : ∀ x, B.region x → figure x)
    (hmiss : ∀ x, inner x → ¬B.region x) : B.value≤C-A := by
  have hb := area.rectangle B (by obtain ⟨hl,hr⟩ := hB; exact ⟨by grind only,by grind only⟩)
  have ht : Thin (fun x => inner x ∧ B.region x) :=
    ⟨[],[],by intro x hx; exact False.elim (hmiss x hx.1 hx.2)⟩
  have hu := area.union _ _ _ _ ht hA hb
  have hm := area.monotone _ _ _ _
    (fun x hx => hx.elim (fun h => houter x (hinner x h)) (fun h => houter x (hin x h))) hu hC
  grind only

/-- Exact coincidence of the ultimate *filled inscribed sum* with the
whole separated solid figure. The local positive rectangle is fixed before
the late stage is chosen. No graph, ordinate continuity, perimeter assertion
or content of the curved figure occurs in the hypotheses or conclusion. -/
theorem ultimate_eq_of_content_gap (area : ContentRules K)
    (inner outer : Nat → (K × K) → Prop) (figure : (K × K) → Prop)
    (A C : Nat → K) (hA : ∀ k, area.HasContent (inner k) (A k))
    (hC : ∀ k, area.HasContent (outer k) (C k))
    (hinner : ∀ k x, inner k x → figure x) (houter : ∀ k x, figure x → outer k x)
    (hsolid : Solid figure) (hseparated : Separated figure)
    (hgap : Shrinks (fun k => C k-A k)) :
    ∀ x, Ultimate inner x ↔ figure x := by
  intro x
  constructor
  · intro hx
    apply Classical.byContradiction
    intro hnot
    obtain ⟨eps,heps,hsep⟩ := hseparated x hnot
    obtain ⟨N,hN⟩ := hx eps heps
    obtain ⟨y,hy,hn⟩ := hN N (Nat.le_refl _)
    exact hsep y (hinner N y hy) hn
  · intro hx eps heps
    obtain ⟨B,hB,hin,hnear⟩ := hsolid x hx eps heps
    have hv : 0<B.value := OrderedRing.mul_pos
      (by obtain ⟨hl,_⟩ := hB; grind only)
      (by obtain ⟨_,hr⟩ := hB; grind only)
    obtain ⟨N,hN⟩ := hgap B.value hv
    refine ⟨N,fun k hk => ?_⟩
    apply Classical.byContradiction
    intro hnot
    have hmiss : ∀ y, inner k y → ¬B.region y := by
      intro y hy hb
      exact hnot ⟨y,hy,hnear y hb⟩
    have hb := missed_rectangle_le_gap area (inner k) figure (outer k)
      (A k) (C k) B (hA k) (hC k) hB (hinner k) (houter k) hin hmiss
    have hs := hN k hk
    grind only

end NewtonLimitDynamics.Polygon.SolidFigureExhaustion
