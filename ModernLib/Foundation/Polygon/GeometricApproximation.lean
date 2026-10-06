import ModernLib.Foundation.Polygon.CauchyValues

/-! A geometrically close sequence has its own Cauchy name. The name retains
the supplied finite approximants exactly; the reference only proves Cauchy
convergence and representative equivalence. -/

namespace NewtonLimitDynamics.Polygon.GeometricApproximation
open NewtonLimitDynamics
open TimeSubdivision PointBounds HarmonicComparison HarmonicAccumulation
open HarmonicDyadic CauchyValues HarmonicTimeRealization

abbrev State := Point × Point

theorem eventually_close (reference : EndpointCauchyName) (approx : Nat → State)
    (C : Fraction) (hC : 0 ≤ C.num)
    (hbound : ∀ j, Fraction.le (distance (approx j) (reference.approx j))
      (duration C j))
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j, N ≤ j →
      Fraction.lt (distance (approx j) (reference.approx j)) eps := by
  obtain ⟨N,hN⟩ := duration_eventually_small C eps hC heps
  exact ⟨N,fun j hj => Fraction.magnitudes.lt_of_le_lt (hbound j) (hN j hj)⟩

def name (reference : EndpointCauchyName) (approx : Nat → State)
    (C : Fraction) (hC : 0 ≤ C.num)
    (hbound : ∀ j, Fraction.le (distance (approx j) (reference.approx j))
      (duration C j)) : EndpointCauchyName where
  approx := approx
  cauchy := by
    intro eps heps
    let q := eps.half.half
    obtain ⟨Na,hNa⟩ := eventually_close reference approx C hC hbound q heps
    obtain ⟨Nr,hNr⟩ := reference.cauchy eps.half heps
    refine ⟨max Na Nr,fun i j hi hj => ?_⟩
    have ha := hNa i (by omega)
    have hb := hNa j (by omega)
    have hr := hNr i j (by omega) (by omega)
    have hbs : Fraction.lt (distance (reference.approx j) (approx j)) q :=
      Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_of_equiv (stateSub_norm_symm _ _)) hb
    have ht1 := stateSub_triangle (approx i) (reference.approx i) (approx j)
    have ht2 := stateSub_triangle (reference.approx i) (reference.approx j) (approx j)
    have ht := Fraction.magnitudes.le_trans ht1
      (Fraction.add_le_add_left ht2 (distance (approx i) (reference.approx i)))
    have hsum : Fraction.lt
        (Fraction.add (distance (approx i) (reference.approx i))
          (Fraction.add (distance (reference.approx i) (reference.approx j))
            (distance (reference.approx j) (approx j)))) eps := by
      have hpair := Fraction.add_lt_add ha hbs
      have hpair' : Fraction.lt
          (Fraction.add (distance (approx i) (reference.approx i))
            (distance (reference.approx j) (approx j))) eps.half :=
        lt_equiv_right hpair (Fraction.half_add_self eps.half)
      have htotal := Fraction.add_lt_add hpair' hr
      have htotal' := lt_equiv_right htotal (Fraction.half_add_self eps)
      exact Fraction.magnitudes.lt_of_le_lt
        (Fraction.le_of_equiv (by
          simp only [distance,Fraction.equiv,Fraction.add,Int.add_mul,Int.mul_add]
          ac_nf <;> omega)) htotal'
    exact Fraction.magnitudes.lt_of_le_lt ht hsum

theorem name_equiv (reference : EndpointCauchyName) (approx : Nat → State)
    (C : Fraction) (hC : 0 ≤ C.num)
    (hbound : ∀ j, Fraction.le (distance (approx j) (reference.approx j))
      (duration C j)) :
    NameEquiv (name reference approx C hC hbound) reference :=
  eventually_close reference approx C hC hbound

end NewtonLimitDynamics.Polygon.GeometricApproximation
