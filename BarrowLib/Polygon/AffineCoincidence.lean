import BarrowLib.Polygon.CurvilinearCoincidence

/-! Affine transport of whole-figure coincidence. An independent pair of
directions gives actual oblique parallelograms, not just coordinate rectangles.
The inverse and both proximity controls are derived from the coefficients.
No area, coordinate completeness or limiting conclusion is supplied.

Provenance: the exact English statements and elementary checked derivations
below are project reconstructions, without an external exact-result match or
historical priority claim. Newton's Latin and edition-local clients remain in
Historical/LemmaIII/CorollaryI.lean. A supplied whole graph/contact description
still needs its historical scope justified; affine transport does not provide
an unproved graph decomposition or contact-extremum existence theorem. -/

namespace NewtonLimitDynamics.Polygon.AffineCoincidence
open Lean.Grind Std CurvilinearCoincidence

variable {K : Type} [Field K] [LE K] [LT K] [IsLinearOrder K]
  [LawfulOrderLT K] [OrderedRing K]

structure Affine (K : Type) where
  origin : K × K
  first : K × K
  second : K × K

def Affine.apply (f : Affine K) (x : K × K) : K × K :=
  (f.origin.1+f.first.1*x.1+f.second.1*x.2,
   f.origin.2+f.first.2*x.1+f.second.2*x.2)

def Affine.det (f : Affine K) : K :=
  f.first.1*f.second.2-f.second.1*f.first.2

structure Frame (K : Type) [Field K] extends Affine K where
  independent : toAffine.det≠0

def Frame.inverse (f : Frame K) : Affine K where
  origin := ((f.second.1*f.origin.2-f.second.2*f.origin.1)/f.toAffine.det,
    (f.first.2*f.origin.1-f.first.1*f.origin.2)/f.toAffine.det)
  first := (f.second.2/f.toAffine.det,-f.first.2/f.toAffine.det)
  second := (-f.second.1/f.toAffine.det,f.first.1/f.toAffine.det)

theorem inverse_apply (f : Frame K) (x : K × K) :
    f.inverse.apply (f.toAffine.apply x)=x := by
  have hcancel := Field.mul_inv_cancel f.independent
  apply Prod.ext <;>
    dsimp only [Frame.inverse,Affine.apply,Affine.det] at * <;>
    grind [Field.div_eq_mul_inv]

theorem apply_inverse (f : Frame K) (x : K × K) :
    f.toAffine.apply (f.inverse.apply x)=x := by
  have hcancel := Field.mul_inv_cancel f.independent
  apply Prod.ext <;>
    dsimp only [Frame.inverse,Affine.apply,Affine.det] at * <;>
    grind [Field.div_eq_mul_inv]

private theorem scalar_small (c eps : K) (heps : 0<eps) :
    ∃ delta, 0<delta ∧ ∀ u, -delta<u → u<delta → -eps<c*u ∧ c*u<eps := by
  have positive_case (d : K) (hd : 0<d) :
      ∃ delta, 0<delta ∧ ∀ u, -delta<u → u<delta → -eps<d*u ∧ d*u<eps := by
    have hnz : d≠0 := by grind only
    have hinv := Field.IsOrdered.inv_pos_iff.mpr hd
    have hdelta : 0<eps/d := by
      simpa only [Field.div_eq_mul_inv] using OrderedRing.mul_pos heps hinv
    have hcancel := Field.mul_inv_cancel hnz
    refine ⟨eps/d,hdelta,?_⟩
    intro u hl hr
    have hlo := OrderedRing.mul_lt_mul_of_pos_left hl hd
    have hhi := OrderedRing.mul_lt_mul_of_pos_left hr hd
    have hprod : d*(eps/d)=eps := by
      calc
        d*(eps/d)=eps*(d*d⁻¹) := by
          rw [Field.div_eq_mul_inv,←Semiring.mul_assoc,
            CommSemiring.mul_comm d eps,Semiring.mul_assoc]
        _=eps := by rw [hcancel,Semiring.mul_one]
    exact ⟨by simpa only [Ring.mul_neg,hprod] using hlo,
      by simpa only [hprod] using hhi⟩
  by_cases hp : 0<c
  · exact positive_case c hp
  · by_cases hn : c<0
    · obtain ⟨delta,hd,h⟩ := positive_case (-c) (by grind only)
      refine ⟨delta,hd,?_⟩
      intro u hl hr
      have := h u hl hr
      grind only
    · have : c=0 := by grind only
      subst c
      exact ⟨eps,heps,by intro u _ _; grind⟩

/-- Every affine map has a derived uniform proximity modulus. -/
theorem affine_uniform (f : Affine K) (eps : K) (heps : 0<eps) :
    ∃ delta, 0<delta ∧ ∀ x y, Near delta x y → Near eps (f.apply x) (f.apply y) := by
  classical
  have he : 0<eps/2 := by grind
  obtain ⟨d₁,h₁,c₁⟩ := scalar_small f.first.1 (eps/2) he
  obtain ⟨d₂,h₂,c₂⟩ := scalar_small f.second.1 (eps/2) he
  obtain ⟨d₃,h₃,c₃⟩ := scalar_small f.first.2 (eps/2) he
  obtain ⟨d₄,h₄,c₄⟩ := scalar_small f.second.2 (eps/2) he
  let d₁₂ := if d₁≤d₂ then d₁ else d₂
  let d₃₄ := if d₃≤d₄ then d₃ else d₄
  let delta := if d₁₂≤d₃₄ then d₁₂ else d₃₄
  have hd : 0<delta ∧ delta≤d₁ ∧ delta≤d₂ ∧ delta≤d₃ ∧ delta≤d₄ := by
    dsimp only [delta,d₁₂,d₃₄]
    grind only
  refine ⟨delta,hd.1,?_⟩
  intro x y hn
  obtain ⟨hxl,hxr,hyl,hyr⟩ := hn
  have hfirst := c₁ (x.1-y.1) (by grind only) (by grind only)
  have hsecond := c₂ (x.2-y.2) (by grind only) (by grind only)
  have hthird := c₃ (x.1-y.1) (by grind only) (by grind only)
  have hfourth := c₄ (x.2-y.2) (by grind only) (by grind only)
  dsimp only [Near,Affine.apply]
  grind

def Image (f : Affine K) (set : (K × K) → Prop) (x : K × K) : Prop :=
  ∃ y, set y ∧ f.apply y=x

/-- A filled parallelogram has two independent frame directions, with
parameters spanning a base interval and a nonnegative height interval. -/
def Parallelogram (f : Frame K) (l r H : K) (x : K × K) : Prop :=
  ∃ s t, l≤s ∧ s≤r ∧ 0≤t ∧ t≤H ∧ f.toAffine.apply (s,t)=x

def Parallelograms (f : Frame K) {a b : K} (p : Partition a b)
    (heights : Nat → K) (x : K × K) : Prop :=
  ∃ i, i<p.count ∧ Parallelogram f (p.nodes i) (p.nodes (i+1)) (heights i) x

omit [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K] in
theorem parallelograms_image (f : Frame K) {a b : K} (p : Partition a b)
    (heights : Nat → K) (x : K × K) :
    Parallelograms f p heights x ↔ Image f.toAffine (Rectangles p heights) x := by
  constructor
  · rintro ⟨i,hi,s,t,hl,hr,h0,hH,hx⟩
    exact ⟨(s,t),⟨i,hi,hl,hr,h0,hH⟩,hx⟩
  · rintro ⟨y,⟨i,hi,hl,hr,h0,hH⟩,hx⟩
    exact ⟨i,hi,y.1,y.2,hl,hr,h0,hH,hx⟩

theorem approaches_image (f : Affine K) (sets : Nat → (K × K) → Prop)
    (figure : (K × K) → Prop) (h : Approaches sets figure) :
    Approaches (fun k => Image f (sets k)) (Image f figure) := by
  intro eps heps
  obtain ⟨delta,hd,hmap⟩ := affine_uniform f eps heps
  obtain ⟨N,hN⟩ := h delta hd
  refine ⟨N,?_⟩
  intro k hk
  obtain ⟨hforward,hbackward⟩ := hN k hk
  constructor
  · rintro x ⟨u,hu,rfl⟩
    obtain ⟨v,hv,hn⟩ := hforward u hu
    exact ⟨f.apply v,⟨v,hv,rfl⟩,hmap u v hn⟩
  · rintro y ⟨v,hv,rfl⟩
    obtain ⟨u,hu,hn⟩ := hbackward v hv
    exact ⟨f.apply u,⟨u,hu,rfl⟩,hmap v u hn⟩

/-- Invertibility and the derived forward/inverse moduli preserve exact
ultimate membership, not merely directed approximation. -/
theorem ultimate_image (f : Frame K) (sets : Nat → (K × K) → Prop) (x : K × K) :
    Ultimate (fun k => Image f.toAffine (sets k)) x ↔
      Ultimate sets (f.inverse.apply x) := by
  constructor
  · intro h eps heps
    obtain ⟨delta,hd,hmap⟩ := affine_uniform f.inverse eps heps
    obtain ⟨N,hN⟩ := h delta hd
    refine ⟨N,?_⟩
    intro k hk
    obtain ⟨y,⟨u,hu,rfl⟩,hn⟩ := hN k hk
    refine ⟨u,hu,?_⟩
    simpa only [inverse_apply] using hmap x (f.toAffine.apply u) hn
  · intro h eps heps
    obtain ⟨delta,hd,hmap⟩ := affine_uniform f.toAffine eps heps
    obtain ⟨N,hN⟩ := h delta hd
    refine ⟨N,?_⟩
    intro k hk
    obtain ⟨u,hu,hn⟩ := hN k hk
    refine ⟨f.toAffine.apply u,⟨u,hu,rfl⟩,?_⟩
    simpa only [apply_inverse] using hmap (f.inverse.apply x) u hn

theorem image_iff_inverse (f : Frame K) (set : (K × K) → Prop) (x : K × K) :
    Image f.toAffine set x ↔ set (f.inverse.apply x) := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [inverse_apply] using hy
  · intro hx
    exact ⟨f.inverse.apply x,hx,apply_inverse f x⟩

omit [LE K] [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K] in
/-- Affine maps carry each parameter segment to its actual straight segment.
Applied to the four rectangle edges, the two direction pairs are parallel. -/
theorem affine_segment (f : Affine K) (u v : K × K) (t : K) :
    f.apply ((1-t)*u.1+t*v.1,(1-t)*u.2+t*v.2)=
      ((1-t)*(f.apply u).1+t*(f.apply v).1,
       (1-t)*(f.apply u).2+t*(f.apply v).2) := by
  apply Prod.ext <;> dsimp only [Affine.apply] <;> grind

/-- Contact is a finite attained ordinate, not a postulated limiting
coincidence or an unproved extrema-attainment theorem. -/
def Touches (g : K → K) {a b : K} (p : Partition a b) (i : Nat) (H : K) : Prop :=
  ∃ t, p.nodes i≤t ∧ t≤p.nodes (i+1) ∧ H=g t

def InscribedContact (g : K → K) {a b : K} (p : Partition a b)
    (i : Nat) (H : K) : Prop :=
  Touches g p i H ∧ ∀ t, p.nodes i≤t → t≤p.nodes (i+1) → H≤g t

def CircumscribedContact (g : K → K) {a b : K} (p : Partition a b)
    (i : Nat) (H : K) : Prop :=
  Touches g p i H ∧ ∀ t, p.nodes i≤t → t≤p.nodes (i+1) → g t≤H

omit [Field K] [LT K] [LawfulOrderLT K] [OrderedRing K] in
theorem cell_height_of_contact (g : K → K) {a b : K} (p : Partition a b)
    (i : Nat) (H : K) (h : Touches g p i H) : CellHeight g p i H := by
  obtain ⟨t,hl,hr,rfl⟩ := h
  exact ⟨t,t,hl,hr,hl,hr,Or.inl ⟨Std.le_refl _,Std.le_refl _⟩⟩

omit [LT K] [LawfulOrderLT K] [OrderedRing K] in
/-- The actual inscribed union lies in the entire given figure. -/
theorem inscribed_in_figure (g : K → K) {a b : K} (p : Partition a b)
    (heights : Nat → K) (h : ∀ i, i<p.count → InscribedContact g p i (heights i))
    (x : K × K) (hx : Rectangles p heights x) : Figure g a b x := by
  obtain ⟨i,hi,hl,hr,h0,hH⟩ := hx
  have hlo := node_bounds p i (by omega)
  have hhi := node_bounds p (i+1) (by omega)
  have htop := (h i hi).2 x.1 hl hr
  exact ⟨by grind only,by grind only,h0,Std.le_trans hH htop⟩

omit [LT K] [LawfulOrderLT K] [OrderedRing K] in
/-- The entire given figure lies in the actual circumscribed union. -/
theorem figure_in_circumscribed (g : K → K) {a b : K} (p : Partition a b)
    (heights : Nat → K) (h : ∀ i, i<p.count → CircumscribedContact g p i (heights i))
    (x : K × K) (hx : Figure g a b x) : Rectangles p heights x := by
  obtain ⟨ha,hb,h0,hg⟩ := hx
  obtain ⟨i,hi,hl,hr⟩ := partition_cover p x.1 ha hb
  exact ⟨i,hi,hl,hr,h0,Std.le_trans hg ((h i hi).2 x.1 hl hr)⟩

def WholeCoincidence (f : Frame K) (g : K → K) (a b : K)
    (parts : Nat → Partition a b) (heights : Nat → Nat → K) : Prop :=
  Approaches (fun k => Parallelograms f (parts k) (heights k))
    (Image f.toAffine (Figure g a b)) ∧
  Approaches (fun k => Image f.toAffine (Perimeter (parts k) (heights k)))
    (Image f.toAffine (Boundary g a b)) ∧
  (∀ x, Ultimate (fun k => Parallelograms f (parts k) (heights k)) x ↔
    Image f.toAffine (Figure g a b) x) ∧
  (∀ x, Ultimate (fun k => Image f.toAffine (Perimeter (parts k) (heights k))) x ↔
    Image f.toAffine (Boundary g a b) x) ∧
  (∀ k x, Image f.toAffine (Perimeter (parts k) (heights k)) x →
    Parallelograms f (parts k) (heights k) x)

/-- Whole-figure coincidence transfers to actual oblique parallelogram
unions. Both exact ultimate equalities use the proved inverse modulus. -/
theorem whole_coincidence_image (f : Frame K) (g : K → K) (a b : K)
    (parts : Nat → Partition a b) (heights : Nat → Nat → K)
    (h : CurvilinearCoincidence.WholeCoincidence g a b parts heights) :
    WholeCoincidence f g a b parts heights := by
  have hsets : (fun k => Parallelograms f (parts k) (heights k))=
      (fun k => Image f.toAffine (Rectangles (parts k) (heights k))) := by
    funext k x
    exact propext (parallelograms_image f (parts k) (heights k) x)
  unfold WholeCoincidence
  rw [hsets]
  obtain ⟨hfilled,hedges,hultimate,hboundary,hin⟩ := h
  refine ⟨approaches_image f.toAffine _ _ hfilled,
    approaches_image f.toAffine _ _ hedges,?_,?_,?_⟩
  · intro x
    exact (ultimate_image f _ x).trans
      ((hultimate (f.inverse.apply x)).trans (image_iff_inverse f _ x).symm)
  · intro x
    exact (ultimate_image f _ x).trans
      ((hboundary (f.inverse.apply x)).trans (image_iff_inverse f _ x).symm)
  · rintro k x ⟨y,hy,rfl⟩
    exact (parallelograms_image f (parts k) (heights k) _).mpr ⟨y,hin k y hy,rfl⟩

def TwoSideBoundary (f : Frame K) (curve : (K × K) → Prop)
    (g : K → K) (a b : K) (x : K × K) : Prop :=
  Image f.toAffine (Baseline a b) x ∨
    Image f.toAffine (Side a (g a)) x ∨ curve x

omit [LT K] [LawfulOrderLT K] [OrderedRing K] in
/-- When the entire curved side ends on the baseline, the apparent terminal
vertical side is just a baseline point. The boundary has the two supplied
straight sides and the supplied whole curved side. -/
theorem two_side_boundary (f : Frame K) (curve : (K × K) → Prop)
    (g : K → K) (a b : K) (hab : a≤b) (hend : g b=0)
    (hcurve : ∀ x, curve x ↔ Image f.toAffine (Graph g a b) x) (x : K × K) :
    Image f.toAffine (Boundary g a b) x ↔ TwoSideBoundary f curve g a b x := by
  constructor
  · rintro ⟨y,hy,he⟩
    rcases hy with hb | hl | hr | hg
    · exact Or.inl ⟨y,hb,he⟩
    · exact Or.inr (Or.inl ⟨y,hl,he⟩)
    · have hb : Baseline a b y := by
        dsimp only [Side] at hr
        rw [hend] at hr
        exact ⟨by grind only,by grind only,by grind only⟩
      exact Or.inl ⟨y,hb,he⟩
    · exact Or.inr (Or.inr ((hcurve x).mpr ⟨y,hg,he⟩))
  · intro hx
    rcases hx with hb | hl | hg
    · obtain ⟨y,hy,he⟩ := hb
      exact ⟨y,Or.inl hy,he⟩
    · obtain ⟨y,hy,he⟩ := hl
      exact ⟨y,Or.inr (Or.inl hy),he⟩
    · obtain ⟨y,hy,he⟩ := (hcurve x).mp hg
      exact ⟨y,Or.inr (Or.inr (Or.inr hy)),he⟩

omit [LawfulOrderLT K] [OrderedRing K] in
/-- Source-shaped boundary specialization; the whole curve identification
and endpoint incidence are explicit finite premises, not inferred from the
word "curve". The exact ultimate conclusion comes from the proved transport. -/
theorem two_side_coincidence (f : Frame K) (curve : (K × K) → Prop)
    (g : K → K) (a b : K) (parts : Nat → Partition a b) (heights : Nat → Nat → K)
    (hend : g b=0) (hcurve : ∀ x, curve x ↔ Image f.toAffine (Graph g a b) x)
    (h : WholeCoincidence f g a b parts heights) :
    WholeCoincidence f g a b parts heights ∧
      ∀ x, Ultimate (fun k => Image f.toAffine (Perimeter (parts k) (heights k))) x ↔
        TwoSideBoundary f curve g a b x := by
  have hab : a≤b := by
    have hn := node_bounds (parts 0) 0 (Nat.zero_le _)
    simpa only [(parts 0).first] using hn.2
  exact ⟨h,fun x => (h.2.2.2.1 x).trans (two_side_boundary f curve g a b hab hend hcurve x)⟩

end NewtonLimitDynamics.Polygon.AffineCoincidence
