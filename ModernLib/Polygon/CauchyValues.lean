import ModernLib.Foundation.Polygon.CauchyValues
import ModernLib.Foundation.Polygon.TailValues
import ModernLib.Polygon.HarmonicBinaryPrefix

namespace NewtonLimitDynamics.Polygon.CauchyValues
open NewtonLimitDynamics
open TimeSubdivision
open PointBounds
open HarmonicComparison
open HarmonicAccumulation
open HarmonicDyadic
open HarmonicTimeComparison
open HarmonicBinaryPrefix

def timeValue (w : Fraction) (s : Point × Point)
    (T : ShortRationalTime w) : Value := realize (timeName w s T)

def binaryValue (b : Nat → Bool) (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) : Value :=
  realize (prefixName b w T s hT hs)

-- Modern dependency score: 115/209 (M=115, H=94; transitive project theorems/axioms).
theorem timeValue_bound (w : Fraction) (s : Point × Point)
    (T U : ShortRationalTime w) :
    Within (timeValue w s U) (timeValue w s T)
      (Fraction.mul (timeLipschitz w s)
        (durationDifference T.val U.val).abs) := by
  apply nameBound_of_eventual_le _ _ _ 0
  intro n _
  exact endpoint_time_bound w T.val U.val s n
    T.property.1 U.property.1 T.property.2 U.property.2

-- Modern dependency score: 120/217 (M=120, H=97; transitive project theorems/axioms).
theorem binaryValue_prefix_bound (b : Nat → Bool) (w T : Fraction)
    (s : Point × Point) (hT : 0 ≤ T.num)
    (hs : DyadicSmallTime w T) (m : Nat) :
    Within (embed (prefixState b w T s m))
      (binaryValue b w T s hT hs) (HarmonicBinaryPrefix.tailCap w T s m) := by
  exact TailValues.approximant_bound (prefixName b w T s hT hs)
    (HarmonicBinaryPrefix.coefficient w T s) (HarmonicBinaryPrefix.coefficient_nonnegative w T s hT)
    (fun j => HarmonicBinaryPrefix.adjacent_error_le b w T s j hT hs) m

-- Modern dependency score: 121/215 (M=121, H=94; transitive project theorems/axioms).
theorem rational_time_uniform_value_bound (w : Fraction) (s : Point × Point)
    (eps : Fraction) (heps : 0 < eps.num)
    (T U : ShortRationalTime w)
    (hnear : Fraction.lt (durationDifference T.val U.val).abs
      (timeDelta w s eps.half)) :
    Within (timeValue w s U) (timeValue w s T) eps.half := by
  have hb := parameter_delta_control w s eps.half
    (durationDifference T.val U.val).abs heps
    (Fraction.abs_num_nonnegative _) hnear
  apply nameBound_of_eventual_le _ _ _ 0
  intro n _
  have hlevel := endpoint_time_bound w T.val U.val s n
    T.property.1 U.property.1 T.property.2 U.property.2
  exact Fraction.magnitudes.lt_implies_le
    (Fraction.magnitudes.lt_of_le_lt hlevel hb)

def endpointValue (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) : Value :=
  realize (endpointName w T s hT hs)

private def sampleOne : Fraction := ⟨1, 1, by decide⟩
private def sampleZero : Fraction := ⟨0, 1, by decide⟩
private def sampleQuarter : Fraction := ⟨1, 4, by decide⟩
private def sampleState : Point × Point :=
  ((sampleOne, sampleZero), (sampleZero, sampleOne))
private def sampleTail : Fraction := ⟨3, 8, by decide⟩
private def sampleLower : Fraction := ⟨3, 16, by decide⟩

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_endpoint_zero_distance :
    Fraction.equiv (distance
      (endpoint sampleOne sampleQuarter sampleState 0) sampleState)
      ⟨9, 16, by decide⟩ := by decide

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem sample_tail_zero :
    Fraction.equiv (HarmonicDyadic.tailCap sampleOne sampleQuarter sampleState 0)
      sampleTail := by decide

-- Modern dependency score: 75/161 (M=75, H=86; transitive project theorems/axioms).
theorem sample_lower_all_levels (j : Nat) :
    Fraction.le sampleLower
      (distance (endpoint sampleOne sampleQuarter sampleState j) sampleState) := by
  let e₀ := endpoint sampleOne sampleQuarter sampleState 0
  let eⱼ := endpoint sampleOne sampleQuarter sampleState j
  have hs : DyadicSmallTime sampleOne sampleQuarter := by
    unfold DyadicSmallTime Fraction.le
    decide
  have hgap := HarmonicDyadic.finite_gap_error sampleOne sampleQuarter
    sampleState (by decide) hs j 0
  have hgap' : Fraction.le (distance e₀ eⱼ)
      (HarmonicDyadic.tailCap sampleOne sampleQuarter sampleState 0) :=
    Fraction.le_equiv_left (stateSub_norm_symm e₀ eⱼ)
      (by simpa only [Nat.zero_add] using hgap)
  have htri := stateSub_triangle e₀ eⱼ sampleState
  have hchain := Fraction.magnitudes.le_trans htri
    (Fraction.add_le_add_right hgap' (distance eⱼ sampleState))
  have hL : Fraction.equiv (Fraction.add sampleTail sampleLower)
      (distance e₀ sampleState) :=
    Fraction.equiv_trans (by decide)
      (Fraction.equiv_symm sample_endpoint_zero_distance)
  have hR : Fraction.equiv
      (Fraction.add
        (HarmonicDyadic.tailCap sampleOne sampleQuarter sampleState 0)
        (distance eⱼ sampleState))
      (Fraction.add sampleTail (distance eⱼ sampleState)) :=
    Fraction.add_equiv sample_tail_zero (Fraction.equiv_refl _)
  have hfull := Fraction.le_equiv_right (Fraction.le_equiv_left hL hchain) hR
  exact le_add_cancel_left sampleTail sampleLower (distance eⱼ sampleState) hfull

-- Modern dependency score: 86/177 (M=86, H=91; transitive project theorems/axioms).
theorem sample_endpoint_value_ne_initial :
    endpointValue sampleOne sampleQuarter sampleState
        (by decide) (by unfold DyadicSmallTime Fraction.le; decide) ≠
      embed sampleState := by
  intro heq
  have hnames : NameEquiv
      (endpointName sampleOne sampleQuarter sampleState
        (by decide) (by unfold DyadicSmallTime Fraction.le; decide))
      (constantName sampleState) := Quotient.exact heq
  let eps : Fraction := ⟨3, 32, by decide⟩
  have heps : 0 < eps.num := by decide
  obtain ⟨N, hN⟩ := hnames eps heps
  have hsmall : Fraction.lt
      (distance (endpoint sampleOne sampleQuarter sampleState N) sampleState)
      eps := hN N (Nat.le_refl N)
  have hlower := sample_lower_all_levels N
  have hhalf : Fraction.lt eps sampleLower := by unfold Fraction.lt; decide
  have hloop := Fraction.magnitudes.lt_of_le_lt hlower hsmall
  have hloop' := Fraction.magnitudes.lt_of_lt_le hloop
    (Fraction.magnitudes.lt_implies_le hhalf)
  exact (Fraction.magnitudes.lt_irrefl sampleLower) hloop'

end NewtonLimitDynamics.Polygon.CauchyValues
