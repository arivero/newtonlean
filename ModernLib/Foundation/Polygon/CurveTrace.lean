import ModernLib.Foundation.Polygon.CompletionGeometry
import ModernLib.Foundation.Polygon.DyadicNodes

/-! Closed chord traces on a given Cauchy-plane curve. Shrinking maximum
cell size and uniform continuity imply convergence of entire closed boundaries
in both directions. This is a trace statement, not scalar area convergence or
arclength convergence. The curve is supplied here, not constructed by a force.
No derivative, tangent or integral is a primitive. -/

namespace NewtonLimitDynamics.Polygon.CurveTrace
open NewtonLimitDynamics
open TimeSubdivision PositionValues ConvexCover ConvexValues CompletionGeometry
open CauchyValues BinaryTime HarmonicTimeRealization HarmonicDyadic HarmonicBinaryPrefix DyadicNodes

def ImageTrace {I : Type} (f : I → PositionValue) (x : PositionValue) : Prop :=
  ∃ t, f t=x

def TraceNear (A B : PositionValue → Prop) (R : Fraction) : Prop :=
  ∀ x, A x → ∃ y, B y ∧ Within x.val y.val R

def BoundaryLimit (P : Nat → PositionValue → Prop) (C : PositionValue → Prop) : Prop :=
  ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
    TraceNear (P m) C eps ∧ TraceNear C (P m) eps

/-- An explicitly uniform modulus on the given compact time domain. Its
availability for an arbitrary source curve remains a geometric premise; the
force-construction client below must derive it for its own curve. -/
def UniformCurve (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) : Prop :=
  ∀ eps : Fraction, 0<eps.num → ∃ delta : Fraction, 0<delta.num ∧
    ∀ x y, TimeWithin T hT x y delta → Within (f x).val (f y).val eps

/-- Closure includes every completed point of the chord, rather than only
vertices or rational interpolation weights. -/
def ClosedChord (x y z : PositionValue) : Prop :=
  Closure (fun p => ∃ a : Fraction, ∃ ha : UnitInterval a,
    p=convexPosition a ha x y) z

def chordTrace {I : Type} (f : I → PositionValue) (nodes : Nat → I)
    (n : Nat) (x : PositionValue) : Prop :=
  ∃ k, k<n ∧ ClosedChord (f (nodes k)) (f (nodes (k+1))) x

-- Modern dependency score: 33/90 (M=33, H=57; transitive project theorems/axioms).
theorem closedChord_ball (x y z centre : PositionValue) (R : Fraction)
    (hx : Within x.val centre.val R) (hy : Within y.val centre.val R)
    (hz : ClosedChord x y z) : Within z.val centre.val R := by
  apply closure_image_bound _ z hz id (fun _ _ _ h => h) centre.val R
  intro p hp
  obtain ⟨a,ha,hp⟩ := hp
  subst p
  have hb := convexValue_relative_bound a ha x.val y.val centre.val R hx hy
  rw [centre.property] at hb
  exact hb

-- Modern dependency score: 36/93 (M=36, H=57; transitive project theorems/axioms).
theorem closedChord_anchor (x y z : PositionValue) (R : Fraction)
    (hR : 0≤R.num) (hy : Within y.val x.val R) (hz : ClosedChord x y z) :
    Within z.val x.val R :=
  closedChord_ball x y z x R (within_mono _ _ _ _
    (by simpa only [Fraction.le,Fraction.ofInt,Int.zero_mul,Int.one_mul,Int.mul_one] using hR)
    ((within_zero_iff _ _).mpr rfl)) hy hz

-- Modern dependency score: 33/94 (M=33, H=61; transitive project theorems/axioms).
theorem chordTrace_node {I : Type} (f : I → PositionValue) (nodes : Nat → I)
    (n : Nat) (hn : 0<n) (k : Nat) (hk : k≤n) :
    chordTrace f nodes n (f (nodes k)) := by
  by_cases hkn : k<n
  · refine ⟨k,hkn,closure_contains _ _ ?_⟩
    refine ⟨Fraction.ofInt 0,by constructor <;> decide,?_⟩
    exact (convexPosition_zero (by constructor <;> decide) _ _).symm
  · have he : n-1+1=k := by omega
    refine ⟨n-1,by omega,closure_contains _ _ ?_⟩
    rw [he]
    refine ⟨Fraction.ofInt 1,by constructor <;> decide,?_⟩
    exact (convexPosition_one (by constructor <;> decide) _ _).symm

/-- The mesh assumptions concern time nodes and their coverage, not the
desired curve or boundary limit. Unequal cells are allowed; `mesh` bounds
their largest time span. -/
-- Modern dependency score: 55/130 (M=55, H=75; transitive project theorems/axioms).
theorem chordTrace_near (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (eps delta mesh : Fraction)
    (heps : 0<eps.num) (nodes : Nat → BinaryTime T hT) (n : Nat) (hn : 0<n)
    (hmesh : Fraction.le mesh delta)
    (hc : ∀ x y, TimeWithin T hT x y delta → Within (f x).val (f y).val eps)
    (hadj : ∀ k, k<n → TimeWithin T hT (nodes k) (nodes (k+1)) mesh)
    (hcover : ∀ t, ∃ k, k≤n ∧ TimeWithin T hT t (nodes k) mesh) :
    TraceNear (chordTrace f nodes n) (ImageTrace f) eps ∧
    TraceNear (ImageTrace f) (chordTrace f nodes n) eps := by
  constructor
  · intro x hx
    obtain ⟨k,hk,hx⟩ := hx
    refine ⟨f (nodes k),⟨nodes k,rfl⟩,?_⟩
    have ht := within_mono _ _ _ _ hmesh (hadj k hk)
    exact closedChord_anchor _ _ x eps (Int.le_of_lt heps)
      (within_symm _ _ _ (hc _ _ ht)) hx
  · intro x hx
    obtain ⟨t,ht⟩ := hx
    obtain ⟨k,hk,hkt⟩ := hcover t
    refine ⟨f (nodes k),chordTrace_node f nodes n hn k hk,?_⟩
    rw [← ht]
    exact hc t (nodes k) (within_mono _ _ _ _ hmesh hkt)

-- Modern dependency score: 56/131 (M=56, H=75; transitive project theorems/axioms).
theorem chordTrace_limit (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f)
    (nodes : Nat → Nat → BinaryTime T hT) (count : Nat → Nat) (mesh : Nat → Fraction)
    (hn : ∀ m, 0<count m)
    (hadj : ∀ m k, k<count m → TimeWithin T hT (nodes m k) (nodes m (k+1)) (mesh m))
    (hcover : ∀ m t, ∃ k, k≤count m ∧ TimeWithin T hT t (nodes m k) (mesh m))
    (hmesh : ∀ delta : Fraction, 0<delta.num → ∃ N : Nat, ∀ m, N≤m → Fraction.le (mesh m) delta) :
    BoundaryLimit (fun m => chordTrace f (nodes m) (count m)) (ImageTrace f) := by
  intro eps heps
  obtain ⟨delta,hd,hc⟩ := hf eps heps
  obtain ⟨N,hN⟩ := hmesh delta hd
  exact ⟨N,fun m hm => chordTrace_near T hT f eps delta (mesh m) heps
    (nodes m) (count m) (hn m) (hN m hm) hc (hadj m) (hcover m)⟩

/-- An actual dyadic chord family on the given curve, with no supplied
boundary convergence field. Right endpoints, aliases and T=0 are included. -/
-- Modern dependency score: 77/163 (M=77, H=86; transitive project theorems/axioms).
theorem dyadic_chordTrace_limit (T : Fraction) (hT : 0≤T.num)
    (f : BinaryTime T hT → PositionValue) (hf : UniformCurve T hT f) :
    BoundaryLimit (fun m => chordTrace f (nodeTime T hT m) (blocks m)) (ImageTrace f) := by
  apply chordTrace_limit T hT f hf (nodeTime T hT) blocks (duration T)
  · intro m; unfold blocks; exact Nat.pow_pos (by decide)
  · exact fun m k hk => adjacent_node_time_within T hT m k hk
  · intro m t
    induction t using Quotient.inductionOn with
    | _ b =>
      exact ⟨ticks b m,ticks_le_blocks b m,
        within_symm _ _ _ (truncation_time_within b T hT m)⟩
  · intro delta hd
    obtain ⟨N,hN⟩ := duration_eventually_small T delta hT hd
    exact ⟨N,fun m hm => Fraction.magnitudes.lt_implies_le (hN m hm)⟩

/-- Pointwise uniform whole-edge convergence of any actual polygon maps
implies two-sided convergence of their image boundaries. -/
-- Modern dependency score: 21/60 (M=21, H=39; transitive project theorems/axioms).
theorem imageTrace_limit {I : Type} (p : Nat → I → PositionValue) (f : I → PositionValue)
    (h : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      ∀ t, Within (p m t).val (f t).val eps) :
    BoundaryLimit (fun m => ImageTrace (p m)) (ImageTrace f) := by
  intro eps heps
  obtain ⟨N,hN⟩ := h eps heps
  refine ⟨N,fun m hm => ⟨?_,?_⟩⟩
  · intro x hx; obtain ⟨t,ht⟩ := hx
    exact ⟨f t,⟨t,rfl⟩,ht ▸ hN m hm t⟩
  · intro x hx; obtain ⟨t,ht⟩ := hx
    exact ⟨p m t,⟨t,rfl⟩,ht ▸ within_symm _ _ _ (hN m hm t)⟩

end NewtonLimitDynamics.Polygon.CurveTrace
