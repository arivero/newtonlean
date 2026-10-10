import NewtonLimitDynamics.Historical.LemmaIII.CorollaryIV

/-!
Target: identify the joined endpoint-contact tangent trace with the upper
boundary of TangentContact.figure, in the existing rational concave increasing
Patch regime. Upper boundary means the point is in its active cell, below
both contact lines and on at least one. Nonnegative graph height at the
patch's left endpoint makes these points belong to the region above baseline.
Also prove that every point of this region lies vertically below such a
trace point at the same abscissa.

May assume the existing Patch contact/concavity conditions and proved support,
meeting, monotonicity and segment arithmetic. Must not assume trace/region
agreement, strict concavity, distinct tangent slopes or distinct nodes.
No area-existence, arclength or unrestricted Proposition I conclusion.

Exact control: g(x)=4-x² on [-2,-1]. At x=-7/4 the upper tangent boundary
has height 1 (left tangent); the other line has height 3/2. At x=-5/4 the
boundary has height 5/2 (right tangent); the other line has height 3. At
x=-3/2 both lines have height 2. The higher line away from the meeting
must be excluded from both the joined trace and the region. Also exercise
coincident lines, a repeated node and equivalent rational representatives.

The quadratic Trace and region-inclusion controls below are conditional on
`Patch parabola derivative a b`; they independently check exact finite
coordinates but do not construct that nonlinear Patch. The flat coincident
line control constructs its own Patch. The printed convergence controls use
this concrete flat Patch but retain the explicit shrinking-mesh premise.
`VerticalTop` means membership in the filled region and maximality at the
same rational abscissa; it is tested across adjacent and repeated cells.
-/

namespace NewtonLimitDynamics.Polygon.TangentContact.Verification
open NewtonLimitDynamics TimeSubdivision HarmonicStability HarmonicTimeComparison

private def a : Fraction := ⟨-2, 1, by decide⟩
private def b : Fraction := ⟨-1, 1, by decide⟩
private def leftX : Fraction := ⟨-7, 4, by decide⟩
private def midX : Fraction := ⟨-3, 2, by decide⟩
private def rightX : Fraction := ⟨-5, 4, by decide⟩
private def oneHalf : Fraction := ⟨3, 2, by decide⟩
private def fiveHalf : Fraction := ⟨5, 2, by decide⟩

private def parabola (x : Fraction) : Fraction :=
  Fraction.add (Fraction.ofInt 4) (negF (Fraction.mul x x))
private def derivative (x : Fraction) : Fraction :=
  Fraction.mul (Fraction.ofInt (-2)) x

private def single : MonotoneRectangles.Partition a b where
  count := 1
  positive_count := by decide
  nodes := fun i => if i = 0 then a else b
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have : i = 0 := by
      change i < 1 at hi
      omega
    subst i
    simp only [Fraction.le, a, b]
    decide

private theorem line_values :
    Fraction.equiv (line parabola derivative a leftX) (Fraction.ofInt 1) ∧
    Fraction.equiv (line parabola derivative b leftX) oneHalf ∧
    Fraction.equiv (line parabola derivative a midX) (Fraction.ofInt 2) ∧
    Fraction.equiv (line parabola derivative b midX) (Fraction.ofInt 2) ∧
    Fraction.equiv (line parabola derivative a rightX) (Fraction.ofInt 3) ∧
    Fraction.equiv (line parabola derivative b rightX) fiveHalf := by
  simp only [Fraction.equiv, line, parabola, derivative, a, b, leftX, midX,
    rightX, oneHalf, fiveHalf, negF, durationDifference, Fraction.ofInt,
    Fraction.add, Fraction.mul]
  decide

private theorem left_upper :
    UpperBoundary parabola derivative single (leftX, Fraction.ofInt 1) := by
  refine ⟨0, by decide, ?_⟩
  simp only [CellUpper, single, Fraction.le, OnTangent, Fraction.equiv,
    line, parabola, derivative, a, b, leftX, negF, durationDifference,
    Fraction.ofInt, Fraction.add, Fraction.mul]
  decide

private theorem middle_upper :
    UpperBoundary parabola derivative single (midX, Fraction.ofInt 2) := by
  refine ⟨0, by decide, ?_⟩
  simp only [CellUpper, single, Fraction.le, OnTangent, Fraction.equiv,
    line, parabola, derivative, a, b, midX, negF, durationDifference,
    Fraction.ofInt, Fraction.add, Fraction.mul]
  decide

private theorem right_upper :
    UpperBoundary parabola derivative single (rightX, fiveHalf) := by
  refine ⟨0, by decide, ?_⟩
  simp only [CellUpper, single, Fraction.le, OnTangent, Fraction.equiv,
    line, parabola, derivative, a, b, rightX, fiveHalf, negF, durationDifference,
    Fraction.ofInt, Fraction.add, Fraction.mul]
  decide

private theorem left_high_excluded :
    ¬ UpperBoundary parabola derivative single (leftX, oneHalf) := by
  intro h
  obtain ⟨i, hi, hc⟩ := h
  have : i = 0 := by
    change i < 1 at hi
    omega
  subst i
  have hbad : ¬ Fraction.le oneHalf (line parabola derivative a leftX) := by
    simp only [Fraction.le, line, parabola, derivative, a, leftX, oneHalf,
      negF, durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
    decide
  exact hbad (by simpa only [CellUpper, single] using! hc.2.2.1)

private theorem right_high_excluded :
    ¬ UpperBoundary parabola derivative single (rightX, Fraction.ofInt 3) := by
  intro h
  obtain ⟨i, hi, hc⟩ := h
  have : i = 0 := by
    change i < 1 at hi
    omega
  subst i
  have hbad : ¬ Fraction.le (Fraction.ofInt 3) (line parabola derivative b rightX) := by
    simp only [Fraction.le, line, parabola, derivative, b, rightX,
      negF, durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
    decide
  exact hbad (by simpa only [CellUpper, single] using! hc.2.2.2.1)

private theorem higher_lines_outside_region :
    ¬ figure parabola derivative single (leftX, oneHalf) ∧
    ¬ figure parabola derivative single (rightX, Fraction.ofInt 3) := by
  constructor
  · intro h
    obtain ⟨i, hi, _, _, _, hL, _⟩ := h
    have he : i = 0 := by
      change i < 1 at hi
      omega
    subst i
    have hbad : ¬ Fraction.le oneHalf (line parabola derivative a leftX) := by
      simp only [Fraction.le, line, parabola, derivative, a, leftX, oneHalf,
        negF, durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
      decide
    exact hbad (by simpa only [single] using! hL)
  · intro h
    obtain ⟨i, hi, _, _, _, _, hR⟩ := h
    have he : i = 0 := by
      change i < 1 at hi
      omega
    subst i
    have hbad : ¬ Fraction.le (Fraction.ofInt 3) (line parabola derivative b rightX) := by
      simp only [Fraction.le, line, parabola, derivative, b, rightX,
        negF, durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
      decide
    exact hbad (by simpa only [single] using! hR)

private theorem parabola_trace_controls
    (C : Patch parabola derivative a b) :
    Trace C single (leftX, Fraction.ofInt 1) ∧
    Trace C single (midX, Fraction.ofInt 2) ∧
    Trace C single (rightX, fiveHalf) ∧
    ¬ Trace C single (leftX, oneHalf) ∧
    ¬ Trace C single (rightX, Fraction.ofInt 3) := by
  exact ⟨(trace_iff_upperBoundary C single _).2 left_upper,
    (trace_iff_upperBoundary C single _).2 middle_upper,
    (trace_iff_upperBoundary C single _).2 right_upper,
    fun h => left_high_excluded ((trace_iff_upperBoundary C single _).1 h),
    fun h => right_high_excluded ((trace_iff_upperBoundary C single _).1 h)⟩

private theorem parabola_boundary_in_region (C : Patch parabola derivative a b) :
    figure parabola derivative single (leftX, Fraction.ofInt 1) ∧
    figure parabola derivative single (midX, Fraction.ofInt 2) ∧
    figure parabola derivative single (rightX, fiveHalf) := by
  have hbase : 0 ≤ (parabola a).num := by decide
  exact ⟨upperBoundary_in_figure C single hbase _ left_upper,
    upperBoundary_in_figure C single hbase _ middle_upper,
    upperBoundary_in_figure C single hbase _ right_upper⟩

private def flat (_ : Fraction) : Fraction := Fraction.ofInt 1
private def flatSlope (_ : Fraction) : Fraction := Fraction.ofInt 0

private theorem flat_right (x h : Fraction) (hh : Fraction.positive h) :
    Fraction.equiv (rightSlope flat x h) (Fraction.ofInt 0) := by
  simp only [rightSlope, dite_eq_left hh, flat, durationDifference, negF,
    Fraction.quotient, Fraction.add, Fraction.ofInt, Fraction.equiv]
  simp

private theorem flat_left (x h : Fraction) (hh : Fraction.positive h) :
    Fraction.equiv (leftSlope flat x h) (Fraction.ofInt 0) := by
  simp only [leftSlope, dite_eq_left hh, flat, durationDifference, negF,
    Fraction.quotient, Fraction.add, Fraction.ofInt, Fraction.equiv]
  simp

private theorem flat_ultimate (r : Fraction → Fraction)
    (hr : ∀ h, Fraction.positive h → Fraction.equiv (r h) (Fraction.ofInt 0)) :
    Ultimate Fraction.magnitudes r (Fraction.ofInt 0) := by
  intro l u hl hu
  refine ⟨Fraction.ofInt 1, by change Fraction.positive (Fraction.ofInt 1); decide, ?_⟩
  intro h hh _
  have he := hr h hh
  exact ⟨Fraction.magnitudes.lt_of_lt_le hl
      (Fraction.le_of_equiv (Fraction.equiv_symm he)),
    Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv he) hu⟩

private theorem flat_patch : Patch flat flatSlope a b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y _
    exact Fraction.equiv_refl _
  · intro x y _
    exact Fraction.equiv_refl _
  · intro x h k _ _ hh hk _
    exact Fraction.le_equiv_left (flat_right x k hk)
      (Fraction.le_equiv_right (Fraction.magnitudes.le_refl _)
        (Fraction.equiv_symm (flat_right x h hh)))
  · intro x h k _ _ hh hk _
    exact Fraction.le_equiv_left (flat_left x h hh)
      (Fraction.le_equiv_right (Fraction.magnitudes.le_refl _)
        (Fraction.equiv_symm (flat_left x k hk)))
  · intro x _ _
    exact flat_ultimate _ (flat_right x)
  · intro x _ _
    exact flat_ultimate _ (flat_left x)
  · intro x _ _
    simp only [flatSlope, Fraction.ofInt]
    decide

private theorem coincident_lines :
    UpperBoundary flat flatSlope single (midX, Fraction.ofInt 1) ∧
    ¬ UpperBoundary flat flatSlope single (midX, Fraction.ofInt 2) := by
  constructor
  · refine ⟨0, by decide, ?_⟩
    simp only [CellUpper, single, Fraction.le, OnTangent, Fraction.equiv,
      line, flat, flatSlope, a, b, midX, durationDifference,
      Fraction.ofInt, Fraction.add, Fraction.mul]
    decide
  · intro h
    obtain ⟨i, hi, hc⟩ := h
    have he : i = 0 := by
      change i < 1 at hi
      omega
    subst i
    have hbad : ¬ Fraction.le (Fraction.ofInt 2) (line flat flatSlope a midX) := by
      simp only [Fraction.le, line, flat, flatSlope, a, midX,
        durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
      decide
    exact hbad (by simpa only [CellUpper, single] using! hc.2.2.1)

private theorem coincident_trace (C : Patch flat flatSlope a b) :
    Trace C single (midX, Fraction.ofInt 1) ∧
    ¬ Trace C single (midX, Fraction.ofInt 2) :=
  ⟨(trace_iff_upperBoundary C single _).2 coincident_lines.1,
    fun h => coincident_lines.2 ((trace_iff_upperBoundary C single _).1 h)⟩

private theorem coincident_trace_concrete :
    Trace flat_patch single (midX, Fraction.ofInt 1) ∧
    ¬ Trace flat_patch single (midX, Fraction.ofInt 2) :=
  coincident_trace flat_patch

private def repeated : MonotoneRectangles.Partition a b where
  count := 2
  positive_count := by decide
  nodes := fun i => if i = 0 then a else if i = 1 then a else b
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have h : i = 0 ∨ i = 1 := by
      change i < 2 at hi
      omega
    rcases h with h | h
    · subst i
      exact Fraction.magnitudes.le_refl _
    · subst i
      change Fraction.le a b
      simp only [Fraction.le, a, b]
      decide

private theorem repeated_zero_width :
    UpperBoundary parabola derivative repeated (a, Fraction.ofInt 0) := by
  refine ⟨0, by decide, ?_⟩
  simp only [CellUpper, repeated, Fraction.le, OnTangent, Fraction.equiv,
    line, parabola, derivative, a, negF, durationDifference,
    Fraction.ofInt, Fraction.add, Fraction.mul]
  decide

private theorem repeated_trace (C : Patch parabola derivative a b) :
    Trace C repeated (a, Fraction.ofInt 0) :=
  (trace_iff_upperBoundary C repeated _).2 repeated_zero_width

private def altA : Fraction := ⟨-4, 2, by decide⟩
private def altB : Fraction := ⟨-3, 3, by decide⟩

private def equivalentNodes : MonotoneRectangles.Partition a b where
  count := 1
  positive_count := by decide
  nodes := fun i => if i = 0 then altA else altB
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have he : i = 0 := by
      change i < 1 at hi
      omega
    subst i
    change Fraction.le altA altB
    simp only [Fraction.le, altA, altB]
    decide

private theorem equivalent_representatives :
    UpperBoundary parabola derivative equivalentNodes (leftX, Fraction.ofInt 1) := by
  refine ⟨0, by decide, ?_⟩
  simp only [CellUpper, equivalentNodes, Fraction.le, OnTangent, Fraction.equiv,
    line, parabola, derivative, altA, altB, leftX, negF, durationDifference,
    Fraction.ofInt, Fraction.add, Fraction.mul]
  decide

private theorem equivalent_trace (C : Patch parabola derivative a b) :
    Trace C equivalentNodes (leftX, Fraction.ofInt 1) :=
  (trace_iff_upperBoundary C equivalentNodes _).2 equivalent_representatives

private def sharedEndpoint : MonotoneRectangles.Partition a b where
  count := 2
  positive_count := by decide
  nodes := fun i => if i = 0 then a else if i = 1 then midX else b
  first := by decide
  last := by decide
  ordered := by
    intro i hi
    have h : i = 0 ∨ i = 1 := by
      change i < 2 at hi
      omega
    rcases h with h | h
    · subst i
      change Fraction.le a midX
      simp only [Fraction.le, a, midX]
      decide
    · subst i
      change Fraction.le midX b
      simp only [Fraction.le, midX, b]
      decide

private theorem shared_upper_first :
    UpperBoundary flat flatSlope sharedEndpoint (midX, Fraction.ofInt 1) := by
  refine ⟨0, by decide, ?_⟩
  simp only [CellUpper, sharedEndpoint, Fraction.le, OnTangent, Fraction.equiv,
    line, flat, flatSlope, a, midX, durationDifference,
    Fraction.ofInt, Fraction.add, Fraction.mul]
  decide

private theorem shared_region_second :
    figure flat flatSlope sharedEndpoint (midX, Fraction.ofInt 0) := by
  refine ⟨1, by decide, ?_, ?_, by decide, ?_, ?_⟩
  all_goals
    simp only [sharedEndpoint, Fraction.le, line, flat, flatSlope, midX, b,
      durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
    decide

private theorem repeated_flat_upper_first :
    UpperBoundary flat flatSlope repeated (a, Fraction.ofInt 1) := by
  refine ⟨0, by decide, ?_⟩
  simp only [CellUpper, repeated, Fraction.le, OnTangent, Fraction.equiv,
    line, flat, flatSlope, a, durationDifference,
    Fraction.ofInt, Fraction.add, Fraction.mul]
  decide

private theorem repeated_flat_region_second :
    figure flat flatSlope repeated (a, Fraction.ofInt 0) := by
  refine ⟨1, by decide, ?_, ?_, by decide, ?_, ?_⟩
  all_goals
    simp only [repeated, Fraction.le, line, flat, flatSlope, a, b,
      durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
    decide

/-- The region witness is in the second cell while the upper-boundary witness
is in the first, so this applies the cross-cell arm of maximality. -/
private theorem shared_global_maximality :
    Fraction.le (Fraction.ofInt 0) (Fraction.ofInt 1) :=
  upperBoundary_maximal flat_patch sharedEndpoint (midX, Fraction.ofInt 0)
    (Fraction.ofInt 1) shared_region_second shared_upper_first

private theorem repeated_global_maximality :
    Fraction.le (Fraction.ofInt 0) (Fraction.ofInt 1) :=
  upperBoundary_maximal flat_patch repeated (a, Fraction.ofInt 0)
    (Fraction.ofInt 1) repeated_flat_region_second repeated_flat_upper_first

/-- This top is assembled as region membership plus global maximality, then
sent through the inverse VerticalTop-to-trace direction. -/
private theorem shared_vertical_top_direct :
    VerticalTop flat flatSlope sharedEndpoint (midX, Fraction.ofInt 1) := by
  constructor
  · refine ⟨0, by decide, ?_, ?_, by decide, ?_, ?_⟩
    all_goals
      simp only [sharedEndpoint, Fraction.le, line, flat, flatSlope, a, midX,
        durationDifference, Fraction.ofInt, Fraction.add, Fraction.mul]
      decide
  · intro h hh
    obtain ⟨i, _, _, _, _, hL, _⟩ := hh
    have he : Fraction.equiv
        (line flat flatSlope (sharedEndpoint.nodes i) midX) (Fraction.ofInt 1) := by
      simp [line, flat, flatSlope, Fraction.equiv, Fraction.add, Fraction.mul,
        Fraction.ofInt]
    exact Fraction.le_equiv_right hL he

private theorem shared_vertical_top_inverse :
    Trace flat_patch sharedEndpoint (midX, Fraction.ofInt 1) :=
  (trace_iff_verticalTop flat_patch sharedEndpoint (by decide) _).2
    shared_vertical_top_direct

private theorem repeated_vertical_top_identity :
    VerticalTop flat flatSlope repeated (a, Fraction.ofInt 1) :=
  (upperBoundary_iff_verticalTop flat_patch repeated (by decide) _).1
    repeated_flat_upper_first

private theorem repeated_vertical_top_inverse :
    UpperBoundary flat flatSlope repeated (a, Fraction.ofInt 1) :=
  (upperBoundary_iff_verticalTop flat_patch repeated (by decide) _).2
    repeated_vertical_top_identity

private theorem printed_vertical_top_interfaces
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches (fun m => VerticalTop flat flatSlope (parts m))
      (RationalBoundary.CurveTrace (graph flat) a b) ∧
    RationalBoundary.Approaches (fun m => VerticalTop flat flatSlope (parts m))
      (RationalBoundary.CurveTrace (graph flat) a b) :=
  ⟨Principia1687.LemmaIII.corollary3_tangent_polygon_boundary
      flat_patch parts (by decide) hmesh,
    Principia1713.LemmaIII.corollary3_tangent_polygon_boundary
      flat_patch parts (by decide) hmesh⟩

private theorem printed_perimeter_interfaces
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (graph flat) (parts m))
      (RationalBoundary.CurveTrace (graph flat) a b) ∧
    RationalBoundary.Approaches (fun m => VerticalTop flat flatSlope (parts m))
      (RationalBoundary.CurveTrace (graph flat) a b) :=
  Principia1687.LemmaIII.corollary4_tangent_polygon_perimeters
    flat_patch parts (by decide) hmesh

private theorem printed_perimeter_interface_1713
    (parts : Nat → MonotoneRectangles.Partition a b)
    (hmesh : Exhaustion.VanishingDifference Fraction.magnitudes
      (fun m => MonotoneRectangles.maxWidth (parts m))) :
    RationalBoundary.Approaches
      (fun m => RationalBoundary.ChordTrace (graph flat) (parts m))
      (RationalBoundary.CurveTrace (graph flat) a b) ∧
    RationalBoundary.Approaches (fun m => VerticalTop flat flatSlope (parts m))
      (RationalBoundary.CurveTrace (graph flat) a b) :=
  Principia1713.LemmaIII.corollary4_tangent_polygon_perimeters
    flat_patch parts (by decide) hmesh

end NewtonLimitDynamics.Polygon.TangentContact.Verification
