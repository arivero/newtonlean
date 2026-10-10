import BarrowLib.Polygon.FiniteEstimates

/-!
Finite position and velocity bounds for iteration of an arbitrary triangular
point map with bounded sampled values. No regularity, trajectory, derivative
or ODE result is used. The sampled-value bound must be derived on the region
or supplied explicitly; the iterates themselves are recursively constructed.
-/

namespace NewtonLimitDynamics.Polygon.BoundedIteration

open NewtonLimitDynamics
open TimeSubdivision PointBounds FiniteEstimates

def run (a : Point → Point) (h : Fraction) (s : Point × Point) : Nat → Point × Point
  | 0 => s
  | n + 1 => cell a h (run a h s n)

theorem zero_duration_run (a : Point → Point) (h : Fraction) (hh : h.num = 0)
    (s : Point × Point) : (n : Nat) → stateEquiv (run a h s n) s
  | 0 => ⟨⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩⟩
  | n+1 => by
      have hstep := zero_duration_cell a h hh (run a h s n)
      have hi := zero_duration_run a h hh s n
      exact ⟨pointEquiv_trans hstep.1 hi.1,pointEquiv_trans hstep.2 hi.2⟩

def time (h : Fraction) (n : Nat) : Fraction := Fraction.mul (Fraction.ofInt (n : Int)) h

theorem run_commute (a : Point → Point) (h : Fraction) (s : Point × Point) (n : Nat) :
    run a h (cell a h s) n = cell a h (run a h s n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih]

def BoundedSamples (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B : Fraction) (n : Nat) : Prop :=
  ∀ i : Nat, i < n → Fraction.le (pointNorm (a (run a h s (i+1)).1)) B

theorem time_nonnegative (h : Fraction) (hh : 0 ≤ h.num) (n : Nat) :
    0 ≤ (time h n).num := Fraction.nonnegative_mul _ _ (Int.natCast_nonneg _) hh

theorem time_monotone (h : Fraction) (hh : 0 ≤ h.num) (i n : Nat) (hin : i ≤ n) :
    Fraction.le (time h i) (time h n) := by
  have hc : Fraction.le (Fraction.ofInt (i : Int)) (Fraction.ofInt (n : Int)) := by
    simpa only [Fraction.le,Fraction.ofInt,Int.mul_one] using
      (show (i : Int) ≤ (n : Int) by omega)
  exact Fraction.mul_le_mul_nonnegative hc h hh

theorem velocity_bound (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B : Fraction) (hh : 0 ≤ h.num) (n : Nat) (hb : BoundedSamples a h s B n) :
    Fraction.le (pointNorm (run a h s n).2)
      (Fraction.add (pointNorm s.2) (Fraction.mul (time h n) B)) := by
  induction n with
  | zero =>
      apply Fraction.le_of_equiv
      simp only [run, time, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
        Int.natCast_zero, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.one_mul, Int.mul_one]
      ac_nf
  | succ n ih =>
      have hb0 : BoundedSamples a h s B n := fun i hi => hb i (by omega)
      have hc := cell_velocity_growth a h B (run a h s n) (hb n (by omega))
      have hi := Fraction.add_le_add_right (ih hb0) (Fraction.mul h.abs B)
      have he : Fraction.equiv
          (Fraction.add (Fraction.add (pointNorm s.2) (Fraction.mul (time h n) B))
            (Fraction.mul h.abs B))
          (Fraction.add (pointNorm s.2) (Fraction.mul (time h (n+1)) B)) := by
        apply Fraction.equiv_trans (Fraction.add_equiv
          (Fraction.equiv_refl (Fraction.add (pointNorm s.2) (Fraction.mul (time h n) B)))
          (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh) (Fraction.equiv_refl B)))
        simp only [time, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
          Int.natCast_add, Int.natCast_one, Int.add_mul, Int.mul_add,
          Int.one_mul, Int.mul_one]
        ac_nf
      exact Fraction.le_equiv_right (Fraction.magnitudes.le_trans hc hi) he

def positionCap (h : Fraction) (s : Point × Point) (B : Fraction) (n : Nat) : Fraction :=
  Fraction.add (pointNorm s.1)
    (Fraction.add (Fraction.mul (time h n) (pointNorm s.2))
      (Fraction.mul (Fraction.mul (time h n) (time h n)) B))

theorem position_cap_step (h P V B : Fraction) (n : Nat)
    (hh : 0 ≤ h.num) (hB : 0 ≤ B.num) :
    Fraction.le
      (Fraction.add (Fraction.add P
        (Fraction.add (Fraction.mul (time h n) V)
          (Fraction.mul (Fraction.mul (time h n) (time h n)) B)))
        (Fraction.mul h (Fraction.add V (Fraction.mul (time h n) B))))
      (Fraction.add P
        (Fraction.add (Fraction.mul (time h (n+1)) V)
          (Fraction.mul (Fraction.mul (time h (n+1)) (time h (n+1))) B))) := by
  let A := Fraction.add (Fraction.add P
    (Fraction.add (Fraction.mul (time h n) V)
      (Fraction.mul (Fraction.mul (time h n) (time h n)) B)))
    (Fraction.mul h (Fraction.add V (Fraction.mul (time h n) B)))
  let E := Fraction.mul (Fraction.mul (time h (n+1)) h) B
  have hE : 0 ≤ E.num := Fraction.nonnegative_mul _ _
    (Fraction.nonnegative_mul _ _ (time_nonnegative h hh _) hh) hB
  apply Fraction.le_equiv_right (Fraction.le_add_nonnegative A E hE)
  simp only [A, E, time, Fraction.equiv, Fraction.add, Fraction.mul, Fraction.ofInt,
    Int.natCast_add, Int.natCast_one, Int.add_mul, Int.mul_add,
    Int.one_mul, Int.mul_one]
  ac_nf

theorem position_bound (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num) (n : Nat)
    (hb : BoundedSamples a h s B n) :
    Fraction.le (pointNorm (run a h s n).1) (positionCap h s B n) := by
  induction n with
  | zero =>
      apply Fraction.le_of_equiv
      simp only [run, positionCap, time, Fraction.equiv, Fraction.add, Fraction.mul,
        Fraction.ofInt, Int.natCast_zero, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.one_mul, Int.mul_one]
      ac_nf
  | succ n ih =>
      have hb0 : BoundedSamples a h s B n := fun i hi => hb i (by omega)
      have hc := cell_position_growth a h (run a h s n)
      have hv := velocity_bound a h s B hh n hb0
      have hv' := Fraction.mul_le_mul_nonnegative_left hv h.abs
        (Fraction.abs_num_nonnegative h)
      have hi := Fraction.add_le_add (ih hb0) hv'
      have he := Fraction.add_equiv (Fraction.equiv_refl (positionCap h s B n))
        (Fraction.mul_equiv (Fraction.abs_of_nonnegative h hh)
          (Fraction.equiv_refl (Fraction.add (pointNorm s.2) (Fraction.mul (time h n) B))))
      exact Fraction.magnitudes.le_trans
        (Fraction.le_equiv_right (Fraction.magnitudes.le_trans hc hi) he)
        (position_cap_step h (pointNorm s.1) (pointNorm s.2) B n hh hB)

def uniformPositionCap (T : Fraction) (s : Point × Point) (B : Fraction) : Fraction :=
  Fraction.add (pointNorm s.1)
    (Fraction.add (Fraction.mul T (pointNorm s.2))
      (Fraction.mul (Fraction.mul T T) B))

/-- A bound depending on the total window, uniformly in the cell count. -/
theorem velocity_bound_at_time (a : Point → Point) (h : Fraction)
    (s : Point × Point) (B T : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num)
    (n : Nat) (hb : BoundedSamples a h s B n) (ht : Fraction.le (time h n) T) :
    Fraction.le (pointNorm (run a h s n).2)
      (Fraction.add (pointNorm s.2) (Fraction.mul T B)) :=
  Fraction.magnitudes.le_trans (velocity_bound a h s B hh n hb)
    (Fraction.add_le_add_left (Fraction.mul_le_mul_nonnegative ht B hB) (pointNorm s.2))

theorem position_bound_at_time (a : Point → Point) (h : Fraction)
    (s : Point × Point) (B T : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num)
    (hT : 0 ≤ T.num) (n : Nat) (hb : BoundedSamples a h s B n)
    (ht : Fraction.le (time h n) T) :
    Fraction.le (pointNorm (run a h s n).1) (uniformPositionCap T s B) := by
  have hsquare := Fraction.magnitudes.le_trans
    (Fraction.mul_le_mul_nonnegative ht (time h n) (time_nonnegative h hh n))
    (Fraction.mul_le_mul_nonnegative_left ht T hT)
  have hvel := Fraction.mul_le_mul_nonnegative ht (pointNorm s.2) (pointNorm_nonnegative _)
  have hforce := Fraction.mul_le_mul_nonnegative hsquare B hB
  exact Fraction.magnitudes.le_trans (position_bound a h s B hh hB n hb)
    (Fraction.add_le_add_left (Fraction.add_le_add hvel hforce) (pointNorm s.1))

theorem state_bound_at_time (a : Point → Point) (h : Fraction)
    (s : Point × Point) (B T : Fraction) (hh : 0 ≤ h.num) (hB : 0 ≤ B.num)
    (hT : 0 ≤ T.num) (n : Nat) (hb : BoundedSamples a h s B n)
    (ht : Fraction.le (time h n) T) :
    Fraction.le (stateNorm (run a h s n))
      (Fraction.add (uniformPositionCap T s B)
        (Fraction.add (pointNorm s.2) (Fraction.mul T B))) :=
  Fraction.add_le_add (position_bound_at_time a h s B T hh hB hT n hb ht)
    (velocity_bound_at_time a h s B T hh hB n hb ht)

theorem run_add (a : Point → Point) (h : Fraction) (s : Point × Point) (n : Nat) :
    (k : Nat) → run a h s (n+k) = run a h (run a h s n) k
  | 0 => rfl
  | k+1 => by
      change FiniteEstimates.cell a h (run a h s (n+k)) =
        FiniteEstimates.cell a h (run a h (run a h s n) k)
      rw [run_add a h s n k]

theorem boundedSamples_restart (a : Point → Point) (h : Fraction) (s : Point × Point)
    (B : Fraction) (N n k : Nat) (hnk : n+k ≤ N) (hb : BoundedSamples a h s B N) :
    BoundedSamples a h (run a h s n) B k := by
  intro i hi
  have h := hb (n+i) (by omega)
  rw [show n+i+1=n+(i+1) by omega,run_add] at h
  exact h

end NewtonLimitDynamics.Polygon.BoundedIteration
