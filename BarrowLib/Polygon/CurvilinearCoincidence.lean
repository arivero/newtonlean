import Init

/-! Geometric coincidence of whole rectangle unions with a given curvilinear
figure, independently of area assignments. Coordinates range over any
supplied linearly ordered field, not just rational coordinates. The algebra
and order laws are explicit encoding data; no completeness or curve-existence
principle is imported. Finite partitions cover the entire given interval.

Provenance: the exact English statements and checked elementary derivations
below are project reconstructions, without an external exact-result match or
historical priority claim. Newton's original Latin and the separate edition
clients belong in Historical/LemmaIII/CorollaryI.lean. Uniform continuity is
an explicit interpretation of ordinate control, not a quotation from Newton.
The given graph describes the whole figure between the two fixed sides;
no unproved decomposition of an arbitrary curve into graph patches is used. -/

namespace NewtonLimitDynamics.Polygon.CurvilinearCoincidence
open Lean.Grind Std

variable {K : Type} [LE K] [IsLinearOrder K]

structure Partition (a b : K) where
  count : Nat
  positive_count : 0<count
  nodes : Nat → K
  first : nodes 0=a
  last : nodes count=b
  ordered : ∀ i, i<count → nodes i≤nodes (i+1)

theorem node_order {a b : K} (p : Partition a b) (j : Nat) :
    ∀ i, i≤j → j≤p.count → p.nodes i≤p.nodes j := by
  induction j with
  | zero =>
    intro i hi _
    have : i=0 := by omega
    subst i
    exact Std.le_refl _
  | succ j ih =>
    intro i hij hj
    by_cases hi : i≤j
    · exact Std.le_trans (ih i hi (by omega)) (p.ordered j (by omega))
    · have : i=j+1 := by omega
      subst i
      exact Std.le_refl _

theorem node_bounds {a b : K} (p : Partition a b) (i : Nat) (hi : i≤p.count) :
    a≤p.nodes i ∧ p.nodes i≤b := by
  have hl := node_order p i 0 (by omega) hi
  have hr := node_order p p.count i hi (Nat.le_refl _)
  rw [p.first] at hl
  rw [p.last] at hr
  exact ⟨hl,hr⟩

theorem partition_cover {a b : K} (p : Partition a b) (t : K) (ha : a≤t) (hb : t≤b) :
    ∃ i, i<p.count ∧ p.nodes i≤t ∧ t≤p.nodes (i+1) := by
  have cover (n : Nat) (hn : 0<n) (h0 : p.nodes 0≤t) (h1 : t≤p.nodes n) :
      ∃ i, i<n ∧ p.nodes i≤t ∧ t≤p.nodes (i+1) := by
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hz : n=0
      · subst n; exact ⟨0,by decide,h0,h1⟩
      · by_cases ht : t≤p.nodes n
        · obtain ⟨i,hi,hl,hr⟩ := ih (by omega) ht
          exact ⟨i,by omega,hl,hr⟩
        · exact ⟨n,by omega,by grind,h1⟩
  apply cover p.count p.positive_count
  · simpa only [p.first] using ha
  · simpa only [p.last] using hb

variable [Field K] [LT K] [LawfulOrderLT K] [OrderedRing K]

/-- Coordinate proximity uses strict bounds in both directions. -/
def Near (eps : K) (x y : K × K) : Prop :=
  -eps<x.1-y.1 ∧ x.1-y.1<eps ∧ -eps<x.2-y.2 ∧ x.2-y.2<eps

def UniformOn (g : K → K) (a b : K) : Prop :=
  ∀ eps, 0<eps → ∃ delta, 0<delta ∧ ∀ s t,
    a≤s → s≤b → a≤t → t≤b → -delta≤s-t → s-t≤delta →
    -eps<g s-g t ∧ g s-g t<eps

def Shrinks (mesh : Nat → K) : Prop :=
  ∀ eps, 0<eps → ∃ N, ∀ k, N≤k → mesh k<eps

def Between (u h v : K) : Prop := (u≤h ∧ h≤v) ∨ (v≤h ∧ h≤u)

/-- A rectangle height lies between ordinates attained in its own cell.
The samples need not be endpoints. In particular an inscribed or circumscribed
rectangle touching the curve inside its cell satisfies this finite condition. -/
def CellHeight (g : K → K) {a b : K} (p : Partition a b) (i : Nat) (H : K) : Prop :=
  ∃ u v, p.nodes i≤u ∧ u≤p.nodes (i+1) ∧
    p.nodes i≤v ∧ v≤p.nodes (i+1) ∧ Between (g u) H (g v)

theorem height_nonnegative (g : K → K) {a b : K} (p : Partition a b) (i : Nat)
    (hi : i<p.count) (H : K) (hH : CellHeight g p i H)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t) : 0≤H := by
  obtain ⟨u,v,hul,hur,hvl,hvr,hbetween⟩ := hH
  have hlo := node_bounds p i (by omega)
  have hhi := node_bounds p (i+1) (by omega)
  have hu := hzero u (by grind only) (by grind only)
  have hv := hzero v (by grind only) (by grind only)
  rcases hbetween with h | h <;> grind only

def Figure (g : K → K) (a b : K) (x : K × K) : Prop :=
  a≤x.1 ∧ x.1≤b ∧ 0≤x.2 ∧ x.2≤g x.1

def Rectangles {a b : K} (p : Partition a b) (h : Nat → K) (x : K × K) : Prop :=
  ∃ i, i<p.count ∧ p.nodes i≤x.1 ∧ x.1≤p.nodes (i+1) ∧ 0≤x.2 ∧ x.2≤h i

def Baseline (a b : K) (x : K × K) : Prop := a≤x.1 ∧ x.1≤b ∧ x.2=0

def Side (c H : K) (x : K × K) : Prop := x.1=c ∧ 0≤x.2 ∧ x.2≤H

def Graph (g : K → K) (a b : K) (x : K × K) : Prop :=
  a≤x.1 ∧ x.1≤b ∧ x.2=g x.1

/-- Complete point-set boundary: curved top, baseline and both endpoint
sides. This predicate asserts nothing about perimeter length. -/
def Boundary (g : K → K) (a b : K) (x : K × K) : Prop :=
  Baseline a b x ∨ Side a (g a) x ∨ Side b (g b) x ∨ Graph g a b x

/-- Complete edge trace of the finite rectangle construction. Endpoint
sides stop at the actual first/last rectangle heights. Internal joins may
rise or fall; repeated nodes and zero heights are admitted. -/
def Perimeter {a b : K} (p : Partition a b) (h : Nat → K) (x : K × K) : Prop :=
  Baseline a b x ∨ Side a (h 0) x ∨ Side b (h (p.count-1)) x ∨
    (∃ i, i<p.count ∧ p.nodes i≤x.1 ∧ x.1≤p.nodes (i+1) ∧ x.2=h i) ∨
    (∃ i, i+1<p.count ∧ x.1=p.nodes (i+1) ∧ Between (h i) x.2 (h (i+1)))

/-- Both directed approximations, uniformly over the entire filled sets. -/
def Approaches (sets : Nat → (K × K) → Prop) (figure : (K × K) → Prop) : Prop :=
  ∀ eps, 0<eps → ∃ N, ∀ k, N≤k →
    (∀ x, sets k x → ∃ y, figure y ∧ Near eps x y) ∧
    (∀ y, figure y → ∃ x, sets k x ∧ Near eps y x)

/-- Exact membership in the ultimate figure: every positive neighborhood
contains a point of each sufficiently late finite figure. -/
def Ultimate (sets : Nat → (K × K) → Prop) (x : K × K) : Prop :=
  ∀ eps, 0<eps → ∃ N, ∀ k, N≤k → ∃ y, sets k y ∧ Near eps x y

/-- Whole-figure conclusions, including the complete edge point sets and
their membership in the actual finite unions. No area or length is assumed. -/
def WholeCoincidence (g : K → K) (a b : K) (parts : Nat → Partition a b)
    (heights : Nat → Nat → K) : Prop :=
  Approaches (fun k => Rectangles (parts k) (heights k)) (Figure g a b) ∧
    Approaches (fun k => Perimeter (parts k) (heights k)) (Boundary g a b) ∧
    (∀ x, Ultimate (fun k => Rectangles (parts k) (heights k)) x ↔ Figure g a b x) ∧
    (∀ x, Ultimate (fun k => Perimeter (parts k) (heights k)) x ↔ Boundary g a b x) ∧
    (∀ k x, Perimeter (parts k) (heights k) x → Rectangles (parts k) (heights k) x)

private theorem positive_common_lower (u v : K) (hu : 0<u) (hv : 0<v) :
    ∃ eps, 0<eps ∧ eps≤u ∧ eps≤v := by
  by_cases h : u≤v
  · exact ⟨u,hu,Std.le_refl _,h⟩
  · exact ⟨v,hv,by grind only,Std.le_refl _⟩

/-- The complete boundary is part of the given filled figure. -/
theorem boundary_in_figure (g : K → K) (a b : K) (hab : a≤b)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t) (x : K × K) (hx : Boundary g a b x) :
    Figure g a b x := by
  rcases hx with hb | hl | hr | hg
  · have := hzero x.1 hb.1 hb.2.1
    dsimp only [Figure,Baseline] at *
    grind only
  · dsimp only [Figure,Side] at *
    grind only
  · dsimp only [Figure,Side] at *
    grind only
  · have := hzero x.1 hg.1 hg.2.1
    dsimp only [Figure,Graph] at *
    grind only

/-- Every point outside the given filled figure has a separated neighborhood.
Continuity is used only for the curved top; fixed sides and baseline use
elementary order. No complete coordinate field is required. -/
theorem figure_separated (g : K → K) (a b : K) (hf : UniformOn g a b)
    (x : K × K) (hx : ¬ Figure g a b x) :
    ∃ eps, 0<eps ∧ ∀ y, Figure g a b y → ¬ Near eps x y := by
  classical
  by_cases ha : a≤x.1
  · by_cases hb : x.1≤b
    · by_cases hz : 0≤x.2
      · have htop : g x.1<x.2 := by
          have : ¬ x.2≤g x.1 := by
            intro h
            exact hx ⟨ha,hb,hz,h⟩
          grind only
        let q := (x.2-g x.1)/4
        have hq : 0<q := by dsimp only [q]; grind
        obtain ⟨delta,hd,hnear⟩ := hf q hq
        let eps := if delta≤q then delta else q
        have heps : 0<eps ∧ eps≤delta ∧ eps≤q := by
          dsimp only [eps]
          split <;> grind only
        refine ⟨eps,heps.1,?_⟩
        rintro y ⟨hya,hyb,_,hytop⟩ hn
        obtain ⟨hxl,hxr,hyl,hyr⟩ := hn
        have hg := hnear x.1 y.1 ha hb hya hyb (by grind only) (by grind only)
        dsimp only [q] at *
        grind
      · refine ⟨-x.2,by grind only,?_⟩
        rintro y ⟨_,_,hy0,_⟩ hn
        obtain ⟨_,_,hyl,hyr⟩ := hn
        grind only
    · refine ⟨x.1-b,by grind only,?_⟩
      rintro y ⟨_,hyb,_,_⟩ hn
      obtain ⟨hxl,hxr,_,_⟩ := hn
      grind only
  · refine ⟨a-x.1,by grind only,?_⟩
    rintro y ⟨hya,_,_,_⟩ hn
    obtain ⟨hxl,hxr,_,_⟩ := hn
    grind only

/-- Approximation plus separation gives exact equality of the ultimate
point predicate with the whole figure, not merely equality of closures. -/
theorem ultimate_eq_of_approaches (sets : Nat → (K × K) → Prop)
    (figure : (K × K) → Prop) (happrox : Approaches sets figure)
    (hsep : ∀ x, ¬ figure x → ∃ eps, 0<eps ∧ ∀ y, figure y → ¬ Near eps x y) :
    ∀ x, Ultimate sets x ↔ figure x := by
  intro x
  constructor
  · intro hu
    apply Classical.byContradiction
    intro hx
    obtain ⟨eps,heps,hseparate⟩ := hsep x hx
    have hhalf : 0<eps/2 := by grind
    obtain ⟨N,hN⟩ := hu (eps/2) hhalf
    obtain ⟨M,hM⟩ := happrox (eps/2) hhalf
    obtain ⟨y,hy,hxy⟩ := hN (N+M) (by omega)
    obtain ⟨z,hz,hyz⟩ := (hM (N+M) (by omega)).1 y hy
    apply hseparate z hz
    dsimp only [Near] at *
    grind
  · intro hx eps heps
    obtain ⟨N,hN⟩ := happrox eps heps
    exact ⟨N,fun k hk => (hN k hk).2 x hx⟩

/-- The whole boundary is separated from every point outside it. Interior
points have positive margins from all four boundary components. -/
theorem boundary_separated (g : K → K) (a b : K) (hab : a≤b)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t) (hf : UniformOn g a b)
    (x : K × K) (hx : ¬ Boundary g a b x) :
    ∃ eps, 0<eps ∧ ∀ y, Boundary g a b y → ¬ Near eps x y := by
  by_cases hF : Figure g a b x
  · have hinside : a<x.1 ∧ x.1<b ∧ 0<x.2 ∧ x.2<g x.1 := by
      dsimp only [Figure,Boundary,Baseline,Side,Graph] at *
      grind only
    let q := (g x.1-x.2)/4
    have hq : 0<q := by dsimp only [q]; grind
    obtain ⟨delta,hd,hnear⟩ := hf q hq
    obtain ⟨e0,he0,he0d,he0q⟩ := positive_common_lower delta q hd hq
    obtain ⟨e1,he1,he10,he1a⟩ := positive_common_lower e0 (x.1-a) he0 (by grind only)
    obtain ⟨e2,he2,he21,he2b⟩ := positive_common_lower e1 (b-x.1) he1 (by grind only)
    obtain ⟨eps,heps,he2,hey⟩ := positive_common_lower e2 x.2 he2 hinside.2.2.1
    have he : eps≤delta ∧ eps≤q ∧ eps≤x.1-a ∧ eps≤b-x.1 := by grind only
    refine ⟨eps,heps,?_⟩
    intro y hy hn
    rcases hy with hb | hl | hr | hg
    · dsimp only [Near,Baseline] at *
      grind only
    · dsimp only [Near,Side] at *
      grind only
    · dsimp only [Near,Side] at *
      grind only
    · obtain ⟨hxl,hxr,hyl,hyr⟩ := hn
      have hc := hnear x.1 y.1 hF.1 hF.2.1 hg.1 hg.2.1
        (by grind only) (by grind only)
      have hy := hg.2.2
      dsimp only [q] at *
      grind
  · obtain ⟨eps,heps,hsep⟩ := figure_separated g a b hf x hF
    exact ⟨eps,heps,fun y hy => hsep y (boundary_in_figure g a b hab hzero y hy)⟩

/-- Finite ordinate control derived from continuity and shrinking widths.
Every height between two ordinates sampled in its own cell is admitted, independently
of any selection or re-pairing of the supplied partition family. -/
theorem heights_near (g : K → K) (a b : K) (parts : Nat → Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hf : UniformOn g a b) (hmesh : Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hheight : ∀ k i, i<(parts k).count → CellHeight g (parts k) i (heights k i)) :
    ∀ eps, 0<eps → ∃ N, ∀ k, N≤k → ∀ i, i<(parts k).count → ∀ t,
      (parts k).nodes i≤t → t≤(parts k).nodes (i+1) →
      -eps<heights k i-g t ∧ heights k i-g t<eps := by
  intro eps heps
  obtain ⟨delta,hd,hnear⟩ := hf eps heps
  obtain ⟨N,hN⟩ := hmesh delta hd
  refine ⟨N,fun k hk i hi t hl hr => ?_⟩
  have hlo := node_bounds (parts k) i (by omega)
  have hhi := node_bounds (parts k) (i+1) (by omega)
  have hw := hwidth k i hi
  have hs := hN k hk
  have ht : a≤t ∧ t≤b := by grind only
  obtain ⟨u,v,hul,hur,hvl,hvr,hbetween⟩ := hheight k i hi
  have hu : a≤u ∧ u≤b := by grind only
  have hv : a≤v ∧ v≤b := by grind only
  have hn0 := hnear u t hu.1 hu.2 ht.1 ht.2
    (by grind only) (by grind only)
  have hn1 := hnear v t hv.1 hv.2 ht.1 ht.2
    (by grind only) (by grind only)
  rcases hbetween with h | h <;> grind only

/-- Transfer independently derived ordinate control to whole filled sets. -/
theorem rectangles_approach_of_ordinate_control (g : K → K) (a b : K)
    (parts : Nat → Partition a b) (heights : Nat → Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hpositive : ∀ k i, i<(parts k).count → 0≤heights k i)
    (hcontrol : ∀ eps, 0<eps → ∃ N, ∀ k, N≤k → ∀ i, i<(parts k).count → ∀ t,
      (parts k).nodes i≤t → t≤(parts k).nodes (i+1) →
      -eps<heights k i-g t ∧ heights k i-g t<eps) :
    Approaches (fun k => Rectangles (parts k) (heights k)) (Figure g a b) := by
  intro eps heps
  obtain ⟨N,hN⟩ := hcontrol eps heps
  refine ⟨N,fun k hk => ⟨?_,?_⟩⟩
  · rintro x ⟨i,hi,hl,hr,hy0,hyH⟩
    have hlo := node_bounds (parts k) i (by omega)
    have hhi := node_bounds (parts k) (i+1) (by omega)
    have hx : a≤x.1 ∧ x.1≤b := by grind only
    have hg := hzero x.1 hx.1 hx.2
    have hn := hN k hk i hi x.1 hl hr
    by_cases hy : x.2≤g x.1
    · exact ⟨x,⟨hx.1,hx.2,hy0,hy⟩,by dsimp only [Near]; grind only⟩
    · exact ⟨(x.1,g x.1),⟨hx.1,hx.2,hg,Std.le_refl _⟩,
        by dsimp only [Near]; grind only⟩
  · rintro y ⟨ha,hb,hy0,hyg⟩
    obtain ⟨i,hi,hl,hr⟩ := partition_cover (parts k) y.1 ha hb
    have hn := hN k hk i hi y.1 hl hr
    have hH := hpositive k i hi
    by_cases hy : y.2≤heights k i
    · exact ⟨y,⟨i,hi,hl,hr,hy0,hy⟩,by dsimp only [Near]; grind only⟩
    · exact ⟨(y.1,heights k i),⟨i,hi,hl,hr,hH,Std.le_refl _⟩,
        by dsimp only [Near]; grind only⟩

/-- Whole filled unions approach the entire given figure, including the
baseline and endpoint sides. This is universal in the original partition
family and its sampled heights; no area assignment is needed. -/
theorem rectangles_approach (g : K → K) (a b : K) (parts : Nat → Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : UniformOn g a b) (hmesh : Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hheight : ∀ k i, i<(parts k).count → CellHeight g (parts k) i (heights k i)) :
    Approaches (fun k => Rectangles (parts k) (heights k)) (Figure g a b) :=
  rectangles_approach_of_ordinate_control g a b parts heights hzero
    (fun k i hi => height_nonnegative g (parts k) i hi _ (hheight k i hi) hzero)
    (heights_near g a b parts heights mesh hf hmesh hwidth hheight)

/-- The ultimate sum of whole filled rectangles coincides in every point
with the given figure, for every admissible original shrinking family. -/
theorem rectangles_ultimate_eq (g : K → K) (a b : K) (parts : Nat → Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : UniformOn g a b) (hmesh : Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hheight : ∀ k i, i<(parts k).count → CellHeight g (parts k) i (heights k i)) :
    ∀ x, Ultimate (fun k => Rectangles (parts k) (heights k)) x ↔ Figure g a b x :=
  ultimate_eq_of_approaches _ _
    (rectangles_approach g a b parts heights mesh hzero hf hmesh hwidth hheight)
    (figure_separated g a b hf)

omit [LT K] [LawfulOrderLT K] [OrderedRing K] in
/-- The full finite edge trace belongs to its actual rectangle union,
including both fixed sides, falling joins and degenerate cells. -/
theorem perimeter_in_rectangles {a b : K} (p : Partition a b) (h : Nat → K)
    (hzero : ∀ i, i<p.count → 0≤h i) (x : K × K) (hx : Perimeter p h x) :
    Rectangles p h x := by
  rcases hx with hb | hl | hr | ht | hj
  · obtain ⟨i,hi,hil,hir⟩ := partition_cover p x.1 hb.1 hb.2.1
    exact ⟨i,hi,hil,hir,by rw [hb.2.2]; exact Std.le_refl _,by rw [hb.2.2]; exact hzero i hi⟩
  · refine ⟨0,p.positive_count,?_,?_,hl.2⟩
    · rw [p.first,hl.1]
      exact Std.le_refl _
    · rw [hl.1]
      simpa only [p.first] using p.ordered 0 p.positive_count
  · have hi : p.count-1<p.count := by have := p.positive_count; omega
    have he : p.count-1+1=p.count := by have := p.positive_count; omega
    refine ⟨p.count-1,hi,?_,?_,hr.2⟩
    · rw [hr.1]
      simpa only [he,p.last] using p.ordered (p.count-1) hi
    · rw [he,p.last,hr.1]
      exact Std.le_refl _
  · obtain ⟨i,hi,hl,hr,hh⟩ := ht
    exact ⟨i,hi,hl,hr,by rw [hh]; exact hzero i hi,by rw [hh]; exact Std.le_refl _⟩
  · obtain ⟨i,hi,hx,hbetween⟩ := hj
    have hi0 : i<p.count := by omega
    have hl := p.ordered i hi0
    have hr := p.ordered (i+1) hi
    rcases hbetween with hh | hh
    · refine ⟨i+1,hi,by rw [hx]; exact Std.le_refl _,by rw [hx]; exact hr,?_,hh.2⟩
      exact Std.le_trans (hzero i hi0) hh.1
    · refine ⟨i,hi0,by rw [hx]; exact hl,by rw [hx]; exact Std.le_refl _,?_,hh.2⟩
      exact Std.le_trans (hzero (i+1) hi) hh.1

/-- Complete edge traces approach the complete given boundary, on every
admissible original shrinking family. No terminal rise or fixed side is
silently added at the limiting curve height. -/
theorem perimeters_approach (g : K → K) (a b : K) (parts : Nat → Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : UniformOn g a b) (hmesh : Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hheight : ∀ k i, i<(parts k).count → CellHeight g (parts k) i (heights k i)) :
    Approaches (fun k => Perimeter (parts k) (heights k)) (Boundary g a b) := by
  intro eps heps
  obtain ⟨N,hN⟩ := heights_near g a b parts heights mesh hf hmesh hwidth hheight eps heps
  obtain ⟨M,hM⟩ := hmesh eps heps
  refine ⟨N+M,fun k hk => ?_⟩
  have hn := hN k (by omega)
  have hsmall := hM k (by omega)
  let p := parts k
  have hpcount : p.count=(parts k).count := rfl
  have hp : 0<p.count := p.positive_count
  have hab : a≤b := by simpa only [p.last] using (node_bounds p p.count (Nat.le_refl _)).1
  have ha0 := hzero a (Std.le_refl _) hab
  have hb0 := hzero b hab (Std.le_refl _)
  have hfirst := hn 0 hp a (by rw [p.first]; exact Std.le_refl _) (by
    have := p.ordered 0 hp
    rwa [p.first] at this)
  have hlast : -eps<heights k (p.count-1)-g b ∧ heights k (p.count-1)-g b<eps := by
    have hi : p.count-1<p.count := by omega
    have he : p.count-1+1=p.count := by omega
    exact hn (p.count-1) hi b (node_bounds p (p.count-1) (by omega)).2
      (by rw [he,p.last]; exact Std.le_refl _)
  have hH0 := height_nonnegative g p 0 hp _ (hheight k 0 hp) hzero
  have hH1 := height_nonnegative g p (p.count-1) (by omega) _ (hheight k (p.count-1) (by omega)) hzero
  have side_close (c H J : K) (hJ : 0≤J)
      (hHJ : -eps<H-J ∧ H-J<eps) (x : K × K) (hx : Side c H x) :
      ∃ y, Side c J y ∧ Near eps x y := by
    by_cases hy : x.2≤J
    · exact ⟨x,⟨hx.1,hx.2.1,hy⟩,by dsimp only [Near]; grind only⟩
    · exact ⟨(c,J),⟨rfl,hJ,Std.le_refl _⟩,by dsimp only [Near]; grind only [Side]⟩
  constructor
  · intro x hx
    rcases hx with hb | hl | hr | ht | hj
    · exact ⟨x,Or.inl hb,by dsimp only [Near]; grind only⟩
    · obtain ⟨y,hy,hnear⟩ := side_close a _ _ ha0 hfirst x hl
      exact ⟨y,Or.inr (Or.inl hy),hnear⟩
    · obtain ⟨y,hy,hnear⟩ := side_close b _ _ hb0 hlast x hr
      exact ⟨y,Or.inr (Or.inr (Or.inl hy)),hnear⟩
    · obtain ⟨i,hi,hl,hr,hh⟩ := ht
      have hbounds : a≤x.1 ∧ x.1≤b := by
        have := node_bounds p i (by omega)
        have := node_bounds p (i+1) (by omega)
        grind only
      have hv := hn i hi x.1 hl hr
      exact ⟨(x.1,g x.1),Or.inr (Or.inr (Or.inr ⟨hbounds.1,hbounds.2,rfl⟩)),
        by dsimp only [Near]; grind only⟩
    · obtain ⟨i,hi,hx,hbetween⟩ := hj
      have hbounds := node_bounds p (i+1) (by omega)
      have hv0 := hn i (by omega) (p.nodes (i+1)) (p.ordered i (by omega)) (Std.le_refl _)
      have hv1 := hn (i+1) hi (p.nodes (i+1)) (Std.le_refl _) (p.ordered (i+1) hi)
      refine ⟨(p.nodes (i+1),g (p.nodes (i+1))),
        Or.inr (Or.inr (Or.inr ⟨hbounds.1,hbounds.2,rfl⟩)),?_⟩
      dsimp only [Near]
      rcases hbetween with hh | hh <;> grind only
  · intro y hy
    rcases hy with hb | hl | hr | hg
    · exact ⟨y,Or.inl hb,by dsimp only [Near]; grind only⟩
    · obtain ⟨x,hx,hnear⟩ := side_close a _ _ hH0 (by grind only) y hl
      exact ⟨x,Or.inr (Or.inl hx),hnear⟩
    · obtain ⟨x,hx,hnear⟩ := side_close b _ _ hH1 (by grind only) y hr
      exact ⟨x,Or.inr (Or.inr (Or.inl hx)),hnear⟩
    · obtain ⟨i,hi,hl,hr⟩ := partition_cover p y.1 hg.1 hg.2.1
      have hv := hn i hi y.1 hl hr
      have hw := hwidth k i hi
      refine ⟨(p.nodes i,heights k i),Or.inr (Or.inr (Or.inr (Or.inl
        ⟨i,hi,Std.le_refl _,p.ordered i hi,rfl⟩))),?_⟩
      dsimp only [Near]
      obtain ⟨_,_,he⟩ := hg
      grind only

/-- Exact ultimate coincidence also holds for the complete edge point sets;
neither area existence nor an arclength assertion is used. -/
theorem perimeters_ultimate_eq (g : K → K) (a b : K) (parts : Nat → Partition a b)
    (heights : Nat → Nat → K) (mesh : Nat → K)
    (hzero : ∀ t, a≤t → t≤b → 0≤g t)
    (hf : UniformOn g a b) (hmesh : Shrinks mesh)
    (hwidth : ∀ k i, i<(parts k).count →
      (parts k).nodes (i+1)-(parts k).nodes i≤mesh k)
    (hheight : ∀ k i, i<(parts k).count → CellHeight g (parts k) i (heights k i)) :
    ∀ x, Ultimate (fun k => Perimeter (parts k) (heights k)) x ↔ Boundary g a b x := by
  have hab : a≤b := by
    simpa only [(parts 0).last] using (node_bounds (parts 0) (parts 0).count (Nat.le_refl _)).1
  exact ultimate_eq_of_approaches _ _
    (perimeters_approach g a b parts heights mesh hzero hf hmesh hwidth hheight)
    (boundary_separated g a b hab hzero hf)

end NewtonLimitDynamics.Polygon.CurvilinearCoincidence
