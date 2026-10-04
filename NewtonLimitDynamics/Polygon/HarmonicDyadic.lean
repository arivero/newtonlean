import BarrowLib.Polygon.GeometricTail
import BarrowLib.Polygon.DyadicArithmetic
import BarrowLib.Polygon.FinitePower
import BarrowLib.Polygon.EndpointCauchyName
import BarrowLib.Polygon.StateDistance
import NewtonLimitDynamics.Polygon.HarmonicUniform

/-!
Actual dyadic harmonic endpoint data at one fixed represented rational time.
The Cauchy estimates are derived from the finite end-kick cells. A Cauchy
name is not a limit point, continuous trajectory, or geometric region between
polygon and trajectory. Kepler swept area remains a separate quantity.
-/

namespace NewtonLimitDynamics.Polygon.HarmonicDyadic

open NewtonLimitDynamics
open TimeSubdivision
open CentralSchedule
open HarmonicStability
open HarmonicRefinement
open HarmonicComparison
open HarmonicAccumulation
open HarmonicUniform
open PointBounds

/-- `2^j` actual end-kick cells, each of duration `T/2^j`. -/
def endpoint (w T : Fraction) (s : Point × Point) (j : Nat) : Point × Point :=
  schedule (linearField w) (List.replicate (blocks j) (duration T j)) s

theorem totalTime_dyadic (T : Fraction) (j : Nat) :
    Fraction.equiv (totalTime (duration T (j + 1)) (blocks j)) T := by
  simp only [totalTime, duration, blocks, Fraction.equiv, Fraction.mul,
    Fraction.ofInt, Int.pow_succ, Int.natCast_pow]
  ac_nf

private theorem pointScale_congr {a b : Fraction} {p q : Point}
    (ha : Fraction.equiv a b) (hp : pointEquiv p q) :
    pointEquiv (pointScale a p) (pointScale b q) :=
  ⟨Fraction.mul_equiv ha hp.1, Fraction.mul_equiv ha hp.2⟩

private theorem cell_congr {d e : Fraction} {s t : Point × Point}
    (hd : Fraction.equiv d e) (hs : stateEquiv s t) (w : Fraction) :
    stateEquiv (cell (linearField w) d s) (cell (linearField w) e t) := by
  have hpos := pointAdd_congr hs.1 (pointScale_congr hd hs.2)
  have hfield : pointEquiv (linearField w (cell (linearField w) d s).1)
      (linearField w (cell (linearField w) e t).1) :=
    pointScale_congr (Fraction.equiv_refl _) hpos
  exact ⟨hpos, pointAdd_congr hs.2 (pointScale_congr hd hfield)⟩

theorem schedule_replicate_congr (w d e : Fraction)
    (hd : Fraction.equiv d e) :
    (n : Nat) → (s t : Point × Point) → stateEquiv s t →
      stateEquiv (schedule (linearField w) (List.replicate n d) s)
        (schedule (linearField w) (List.replicate n e) t)
  | 0, _, _, hs => hs
  | n + 1, _, _, hs =>
      schedule_replicate_congr w d e hd n _ _ (cell_congr hd hs w)

theorem fineDurations_replicate (h : Fraction) :
    (n : Nat) → fineDurations h n = List.replicate (n + n) h
  | 0 => rfl
  | n + 1 => by
      have ih := fineDurations_replicate h n
      have hn : (n + 1) + (n + 1) = 2 + (n + n) := by omega
      rw [hn]
      have hc : 2 + (n + n) = (n + n) + 2 := by omega
      rw [hc]
      simp only [fineDurations, Nat.add_succ, List.replicate_succ]
      rw [ih]

/-- The coarser dyadic endpoint is value-equivalent to the actual coarse
block schedule at half the next level's duration. -/
theorem endpoint_coarse (w T : Fraction) (s : Point × Point) (j : Nat) :
    stateEquiv (endpoint w T s j)
      (coarseAt w (duration T (j + 1)) s (blocks j)) := by
  have hc := schedule_replicate_congr w (duration T j)
    (Fraction.add (duration T (j + 1)) (duration T (j + 1)))
    (duration_halving T j) (blocks j) s s
    ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
  simpa only [endpoint, coarseAt_schedule] using hc

/-- The next dyadic endpoint is the actual two-half-cell schedule. -/
theorem endpoint_fine (w T : Fraction) (s : Point × Point) (j : Nat) :
    endpoint w T s (j + 1) =
      fineAt w (duration T (j + 1)) s (blocks j) := by
  unfold endpoint
  rw [blocks_succ]
  rw [← fineDurations_replicate]
  exact fineAt_schedule w (duration T (j + 1)) s (blocks j)

theorem elapsed_replicate_congr {d e : Fraction}
    (hd : Fraction.equiv d e) :
    (n : Nat) →
      Fraction.equiv (elapsed (List.replicate n d)) (elapsed (List.replicate n e))
  | 0 => Fraction.equiv_refl _
  | n + 1 => Fraction.add_equiv hd (elapsed_replicate_congr hd n)

theorem endpoint_elapsed (T : Fraction) (j : Nat) :
    Fraction.equiv (elapsed (List.replicate (blocks j) (duration T j))) T :=
  Fraction.equiv_trans
    (elapsed_replicate_congr (duration_halving T j) (blocks j))
    (Fraction.equiv_trans
      (coarse_elapsed_totalTime (duration T (j + 1)) (blocks j))
      (totalTime_dyadic T j))

theorem endpoint_next_elapsed (T : Fraction) (j : Nat) :
    Fraction.equiv
      (elapsed (List.replicate (blocks (j + 1)) (duration T (j + 1)))) T := by
  rw [blocks_succ, ← fineDurations_replicate]
  exact Fraction.equiv_trans
    (fine_elapsed_totalTime (duration T (j + 1)) (blocks j))
    (totalTime_dyadic T j)

def halfThreshold : Fraction := ⟨1, 2, by decide⟩

def DyadicSmallTime (w T : Fraction) : Prop :=
  Fraction.le
    (Fraction.mul T (Fraction.add (Fraction.ofInt 1) w.abs)) halfThreshold

theorem dyadic_smallTime (w T : Fraction) (j : Nat)
    (hs : DyadicSmallTime w T) :
    SmallTime w (duration T (j + 1)) (blocks j) := by
  have ht := totalTime_dyadic T j
  have he := Fraction.mul_equiv ht
    (Fraction.equiv_refl (Fraction.add (Fraction.ofInt 1) w.abs))
  exact Fraction.le_equiv_left he hs

def adjacentCap (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  Fraction.mul (Fraction.ofInt 3)
    (Fraction.mul T
      (Fraction.mul (duration T (j + 1))
        (Fraction.mul w.abs (stateNorm s))))

theorem adjacent_error_le (w T : Fraction) (s : Point × Point) (j : Nat)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    Fraction.le
      (stateNorm (stateSub (endpoint w T s (j + 1)) (endpoint w T s j)))
      (adjacentCap w T s j) := by
  let h := duration T (j + 1)
  let n := blocks j
  have hf := endpoint_fine w T s j
  have hc := endpoint_coarse w T s j
  have he : stateEquiv (stateSub (endpoint w T s (j + 1)) (endpoint w T s j))
      (stateSub (fineAt w h s n) (coarseAt w h s n)) :=
    stateSub_congr
      (by rw [hf]; exact ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
          ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩)
      hc
  have hbound := actual_uniform_error w h s n hT (dyadic_smallTime w T j hs)
  have hfirst := Fraction.le_equiv_left (stateNorm_equiv he) hbound
  apply Fraction.le_equiv_right hfirst
  exact Fraction.mul_equiv (Fraction.equiv_refl _)
    (Fraction.mul_equiv (totalTime_dyadic T j) (Fraction.equiv_refl _))

/-- The finite tail coefficient `A=3*T²*|w|*M`. -/
def coefficient (w T : Fraction) (s : Point × Point) : Fraction :=
  Fraction.mul (Fraction.ofInt 3)
    (Fraction.mul T (Fraction.mul T (Fraction.mul w.abs (stateNorm s))))

def tailCap (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  let A := coefficient w T s
  ⟨A.num, A.den * (2 : Int) ^ j,
    Int.mul_pos A.den_pos (Int.pow_pos (by decide))⟩

def doubleTail (w T : Fraction) (s : Point × Point) (j : Nat) : Fraction :=
  let A := coefficient w T s
  ⟨2 * A.num, A.den * (2 : Int) ^ j,
    Int.mul_pos A.den_pos (Int.pow_pos (by decide))⟩

theorem adjacentCap_tail (w T : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv (adjacentCap w T s j) (tailCap w T s (j + 1)) := by
  simp only [adjacentCap, tailCap, coefficient, duration, Fraction.equiv,
    Fraction.mul, Fraction.ofInt, Int.pow_succ]
  ac_nf

theorem tail_halving (w T : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv
      (Fraction.add (tailCap w T s (j + 1)) (tailCap w T s (j + 1)))
      (tailCap w T s j) := by
  exact GeometricTail.tail_halving (coefficient w T s) j

theorem tail_double (w T : Fraction) (s : Point × Point) (j : Nat) :
    Fraction.equiv (Fraction.add (tailCap w T s j) (tailCap w T s j))
      (doubleTail w T s j) := by
  exact GeometricTail.tail_double (coefficient w T s) j

theorem coefficient_nonnegative (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) : 0 ≤ (coefficient w T s).num :=
  Int.mul_nonneg (by decide)
    (Int.mul_nonneg hT (Int.mul_nonneg hT
      (Int.mul_nonneg (Fraction.abs_num_nonnegative w) (stateNorm_nonnegative s))))

/-- Any finite separation of dyadic levels has error within the tail at its
coarser endpoint. The proof uses actual neighboring schedules. -/
theorem finite_gap_error (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    (k j : Nat) → Fraction.le
      (stateNorm (stateSub (endpoint w T s (j + k))
        (endpoint w T s j))) (tailCap w T s j) := by
  intro k j
  exact GeometricTail.finite_gap (endpoint w T s) (coefficient w T s)
    (coefficient_nonnegative w T s hT)
    (fun i => Fraction.le_equiv_right (adjacent_error_le w T s i hT hs)
      (adjacentCap_tail w T s i)) k j

/-- Both later endpoints are compared to the same earlier actual endpoint. -/
theorem two_sided_error (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T)
    (N m n : Nat) (hm : N ≤ m) (hn : N ≤ n) :
    Fraction.le
      (stateNorm (stateSub (endpoint w T s m) (endpoint w T s n)))
      (doubleTail w T s N) := by
  exact GeometricTail.two_sided (endpoint w T s) (coefficient w T s)
    (coefficient_nonnegative w T s hT)
    (fun i => Fraction.le_equiv_right (adjacent_error_le w T s i hT hs)
      (adjacentCap_tail w T s i)) N m n hm hn

/-- A deliberately simple, potentially large explicit precision modulus. -/
def modulus (w T : Fraction) (s : Point × Point) (eps : Fraction) : Nat :=
  (2 * (coefficient w T s).num * eps.den).toNat

theorem doubleTail_lt_tolerance (w T : Fraction) (s : Point × Point)
    (eps : Fraction) (hT : 0 ≤ T.num) (heps : 0 < eps.num) :
    Fraction.lt (doubleTail w T s (modulus w T s eps)) eps := by
  exact GeometricTail.doubleTail_lt_tolerance (coefficient w T s) eps
    (coefficient_nonnegative w T s hT) heps

/-- A Cauchy name stores finite rational endpoint approximants and a proved
positive-tolerance condition. It does not supply a limit point. -/
theorem endpoint_cauchy (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) :
    ∀ eps : Fraction, 0 < eps.num →
      ∃ N : Nat, ∀ m n : Nat, N ≤ m → N ≤ n →
        Fraction.lt
          (stateNorm (stateSub (endpoint w T s m) (endpoint w T s n))) eps := by
  intro eps heps
  refine ⟨modulus w T s eps, ?_⟩
  intro m n hm hn
  exact Fraction.magnitudes.lt_of_le_lt
    (two_sided_error w T s hT hs _ m n hm hn)
    (doubleTail_lt_tolerance w T s eps hT heps)

def endpointName (w T : Fraction) (s : Point × Point)
    (hT : 0 ≤ T.num) (hs : DyadicSmallTime w T) : EndpointCauchyName where
  approx := endpoint w T s
  cauchy := endpoint_cauchy w T s hT hs

private theorem stateEquiv_refl (s : Point × Point) : stateEquiv s s :=
  ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
    ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩

private theorem stateEquiv_trans {a b c : Point × Point}
    (hab : stateEquiv a b) (hbc : stateEquiv b c) : stateEquiv a c :=
  ⟨⟨Fraction.equiv_trans hab.1.1 hbc.1.1,
      Fraction.equiv_trans hab.1.2 hbc.1.2⟩,
    ⟨Fraction.equiv_trans hab.2.1 hbc.2.1,
      Fraction.equiv_trans hab.2.2 hbc.2.2⟩⟩

private theorem zero_duration_cell (w d : Fraction) (s : Point × Point)
    (hd : d.num = 0) : stateEquiv (cell (linearField w) d s) s := by
  let z : Fraction := ⟨0, 1, by decide⟩
  have he : Fraction.equiv d z := by
    unfold Fraction.equiv z
    simp [hd]
  exact stateEquiv_trans (cell_congr he (stateEquiv_refl s) w)
    (zero_step w s)

theorem zero_duration_schedule (w d : Fraction) (hd : d.num = 0) :
    (n : Nat) → (s : Point × Point) →
      stateEquiv (schedule (linearField w) (List.replicate n d) s) s
  | 0, s => stateEquiv_refl s
  | n + 1, s =>
      stateEquiv_trans
        (zero_duration_schedule w d hd n (cell (linearField w) d s))
        (zero_duration_cell w d s hd)

theorem zero_time_endpoint (w T : Fraction) (s : Point × Point) (j : Nat)
    (hT : T.num = 0) : stateEquiv (endpoint w T s j) s := by
  exact zero_duration_schedule w (duration T j) (by exact hT) (blocks j) s

private def sampleOne : Fraction := ⟨1, 1, by decide⟩
private def sampleZero : Fraction := ⟨0, 1, by decide⟩
private def sampleTime : Fraction := ⟨1, 4, by decide⟩
private def sampleState : Point × Point :=
  ((sampleOne, sampleZero), (sampleZero, sampleOne))

theorem sample_dyadic_small_time : DyadicSmallTime sampleOne sampleTime := by
  unfold DyadicSmallTime Fraction.le
  decide

theorem sample_adjacent_error :
    Fraction.equiv
      (stateNorm (stateSub (endpoint sampleOne sampleTime sampleState 1)
        (endpoint sampleOne sampleTime sampleState 0)))
      ⟨145, 4096, by decide⟩ := by decide

theorem sample_adjacent_cap :
    Fraction.equiv (adjacentCap sampleOne sampleTime sampleState 0)
      ⟨3, 16, by decide⟩ := by decide

theorem sample_tail_cap :
    Fraction.equiv (tailCap sampleOne sampleTime sampleState 0)
      ⟨3, 8, by decide⟩ := by decide

end NewtonLimitDynamics.Polygon.HarmonicDyadic
