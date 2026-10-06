import NewtonLimitDynamics

namespace NewtonLimitDynamics.Polygon.SupportingBoundaryControls
open NewtonLimitDynamics TimeSubdivision PositionValues CauchyValues CompletionGeometry
open ConvexCover CurveTrace SupportingTangents SupportingBoundary Parallelogram
open BinaryTime HarmonicDyadic DyadicNodes HarmonicTimeRealization

local instance (a b : Fraction) : Decidable (Fraction.le a b) :=
  inferInstanceAs (Decidable (a.num*b.den≤b.num*a.den))
local instance (a x b : Fraction) : Decidable (Between a x b) :=
  inferInstanceAs (Decidable ((Fraction.le a x ∧ Fraction.le x b) ∨
    (Fraction.le b x ∧ Fraction.le x a)))
local instance (p x q : Point) : Decidable (RectangleBetween p x q) :=
  inferInstanceAs (Decidable (Between p.1 x.1 q.1 ∧ Between p.2 x.2 q.2))
local instance (p q v : Point) : Decidable (ParallelThrough p q v) :=
  inferInstanceAs (Decidable (Fraction.equiv (TimeSubdivision.det p v) (TimeSubdivision.det q v)))

private def p (x y : Int) : Point := (Fraction.ofInt x,Fraction.ofInt y)
private def half : Fraction := ⟨1,2,by decide⟩

private def upper : Cell (p 0 0) (p 2 2) where
  leftEnd := p 2 4
  rightStart := p 0 2
  left_x := by decide
  right_x := by decide
  support := Or.inl ⟨by decide,by decide⟩
  monotone := Or.inl ⟨by decide,by decide⟩

private def lower : Cell (p 0 0) (p 2 2) where
  leftEnd := p 2 0
  rightStart := p 0 (-2)
  left_x := by decide
  right_x := by decide
  support := Or.inr ⟨by decide,by decide⟩
  monotone := Or.inl ⟨by decide,by decide⟩

private def descending : Cell (p 0 2) (p 2 0) where
  leftEnd := p 2 2
  rightStart := p 0 4
  left_x := by decide
  right_x := by decide
  support := Or.inl ⟨by decide,by decide⟩
  monotone := Or.inr ⟨by decide,by decide⟩

-- Both support orientations and decreasing ordinates have nonvacuous meetings.
example : Meeting (p 0 0) (p 2 2) upper (p 1 2) := by
  refine ⟨half,by constructor <;> decide,?_,?_⟩ <;> constructor <;> decide
example : Meeting (p 0 0) (p 2 2) lower (p 1 0) := by
  refine ⟨half,by constructor <;> decide,?_,?_⟩ <;> constructor <;> decide
example : Meeting (p 0 2) (p 2 0) descending (p 1 2) := by
  refine ⟨half,by constructor <;> decide,?_,?_⟩ <;> constructor <;> decide

-- Arbitrary intersections are identified, rather than assumed to have a unit parameter.
example (x : Point)
    (hx : ParallelThrough x (p 0 0) (pointSub upper.leftEnd (p 0 0)))
    (hy : ParallelThrough x upper.rightStart (pointSub (p 2 2) upper.rightStart)) :
    pointEquiv x (p 1 2) := by
  apply meeting_unique (p 0 0) (p 2 2) upper (p 1 2) x
  · refine ⟨half,by constructor <;> decide,?_,?_⟩ <;> constructor <;> decide
  · decide
  · exact hx
  · exact hy

private def horizontal : Cell (p 0 1) (p 2 1) where
  leftEnd := p 2 1
  rightStart := p 0 1
  left_x := by decide
  right_x := by decide
  support := Or.inl ⟨by decide,by decide⟩
  monotone := Or.inl ⟨by decide,by decide⟩

-- The coincident case is constructed; arbitrary infinite-line points are excluded.
example : ∃ r : Point, Meeting (p 0 1) (p 2 1) horizontal r :=
  meeting_exists _ _ horizontal
example : ParallelThrough (p 10 1) (p 0 1) (pointSub horizontal.leftEnd (p 0 1)) := by decide
example : ¬ Meeting (p 0 1) (p 2 1) horizontal (p 10 1) := by
  intro h
  have hb := (meeting_rectangle _ _ horizontal _ h).1
  have hn : ¬ Between (Fraction.ofInt 0) (Fraction.ofInt 10) (Fraction.ofInt 2) := by decide
  exact hn hb

-- Reversed horizontal coordinates do not silently force a left-to-right orientation.
example : ∃ r : Point, RectangleBetween (p 2 0) r (p 0 2) := by
  let c : Cell (p 2 0) (p 0 2) :=
    ⟨p 0 4,p 2 2,by decide,by decide,Or.inl ⟨by decide,by decide⟩,
      Or.inl ⟨by decide,by decide⟩⟩
  obtain ⟨r,hr⟩ := meeting_exists _ _ c
  exact ⟨r,meeting_rectangle _ _ c r hr⟩

-- Support inequalities alone allow an intersection outside the endpoint rectangle.
-- The shared monotone direction is therefore a real premise, not redundant metadata.
example : Fraction.le (p 0 0).2 (p 0 2).2 ∧ Fraction.le (p 2 0).2 (p 2 2).2 := by
  constructor <;> decide
example : pointEquiv (p 1 1) (lerp half (p 0 0) (p 2 2)) ∧
    pointEquiv (p 1 1) (lerp half (p 0 2) (p 2 0)) := by
  constructor <;> constructor <;> decide
example : ¬ RectangleBetween (p 0 0) (p 1 1) (p 2 0) := by decide
example : ¬ ((Fraction.le (p 0 0).2 (p 2 2).2 ∧ Fraction.le (p 0 2).2 (p 2 0).2) ∨
    (Fraction.le (p 2 2).2 (p 0 0).2 ∧ Fraction.le (p 2 0).2 (p 0 2).2)) := by decide

-- Every completed boundary point is bounded, not only the finite meeting vertex.
example (x : PositionValue) (hx : cellTrace (p 0 0) (p 2 2) upper x) :
    Within x.val (embedPosition (p 0 0)).val (Fraction.ofInt 4) := by
  exact within_mono _ _ _ _ (by decide) (cellTrace_bound _ _ upper x hx)

private def constantCell (q : Point) : Cell q q :=
  ⟨q,q,Fraction.equiv_refl _,Fraction.equiv_refl _,
    Or.inl ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩,
    Or.inl ⟨Fraction.magnitudes.le_refl _,Fraction.magnitudes.le_refl _⟩⟩

-- Zero windows, identical endpoints, coincident lines and the final node all occur.
example : supportingTrace (fun _ => p 0 0) (fun _ => constantCell (p 0 0)) 1
    (embedPosition (p 0 0)) :=
  supportingTrace_node _ _ 1 (by decide) 1 (by decide)

private theorem constantUniform (T : Fraction) (hT : 0≤T.num) (q : Point) :
    UniformCurve T hT (fun _ => embedPosition q) := by
  intro eps heps
  refine ⟨Fraction.ofInt 1,by decide,?_⟩
  intro t u _
  exact within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le
    ((Fraction.positive_iff_zero_lt eps).mp heps)) ((within_zero_iff _ _).mpr rfl)

-- Both stage wrappers have satisfiable premises, even at T=0.
example : BoundaryLimit (fun m => supportingTrace (fun _ => p 0 0)
    (fun _ => constantCell (p 0 0)) (blocks m))
    (ImageTrace (fun _ : BinaryTime (Fraction.ofInt 0) (by decide) => embedPosition (p 0 0))) := by
  apply Principia1687.LemmaIII.corollary3_4_supporting_boundary_reconstruction
    (Fraction.ofInt 0) (by decide) _ (constantUniform _ _ _) (fun _ _ => p 0 0)
    (fun _ _ => constantCell (p 0 0))
  intro eps heps
  refine ⟨0,?_⟩
  intro m _ k _
  exact within_mono _ _ _ _ (Fraction.magnitudes.lt_implies_le
    ((Fraction.positive_iff_zero_lt eps).mp heps)) ((within_zero_iff _ _).mpr rfl)

example (T : Fraction) (hT : 0≤T.num) (f : BinaryTime T hT → PositionValue)
    (hf : UniformCurve T hT f) (points : Nat → Nat → Point)
    (cells : ∀ m k, Cell (points m k) (points m (k+1)))
    (hpoints : ∀ eps : Fraction, 0<eps.num → ∃ N : Nat, ∀ m, N≤m →
      ∀ k, k≤blocks m → Within (embedPosition (points m k)).val
        (f (nodeTime T hT m k)).val eps) :
    BoundaryLimit (fun m => supportingTrace (points m) (cells m) (blocks m)) (ImageTrace f) :=
  Principia1713.LemmaIII.corollary3_4_supporting_boundary_reconstruction T hT f hf points cells hpoints

#print axioms SupportingTangents.affine_crossing
#print axioms SupportingTangents.meeting_exists
#print axioms SupportingTangents.meeting_unique
#print axioms SupportingTangents.meeting_rectangle
#print axioms SupportingBoundary.supportingTrace_limit
#print axioms Principia1687.LemmaIII.corollary3_4_supporting_boundary_reconstruction
#print axioms Principia1713.LemmaIII.corollary3_4_supporting_boundary_reconstruction
end NewtonLimitDynamics.Polygon.SupportingBoundaryControls
