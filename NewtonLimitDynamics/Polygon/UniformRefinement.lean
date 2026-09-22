import NewtonLimitDynamics.Polygon.PartitionControl

namespace NewtonLimitDynamics.Polygon.UniformRefinement

open NewtonLimitDynamics
open TimeSubdivision
open PartitionControl

/-- `n` equal unit cells over a common denominator. -/
def unitCells (n : Nat) : List Nat := List.replicate n 1

private theorem unitCells_T_from (s : PartitionStats) : (n : Nat) ->
    ((unitCells n).foldl next s).T = s.T + n
  | 0 => rfl
  | n + 1 => by
      show ((unitCells n).foldl next (next s 1)).T = s.T + (n + 1)
      rw [unitCells_T_from (next s 1) n]
      simp only [next]
      omega

theorem unitCells_total (n : Nat) : total (unitCells n) = n := by
  unfold total stats
  rw [unitCells_T_from]
  exact Nat.zero_add n

theorem unitCells_le_one (n : Nat) : ∀ w ∈ unitCells n, w ≤ 1 := by
  intro w hw
  rw [List.eq_of_mem_replicate hw]
  exact Nat.le_refl 1

/-- Refining the rational time `N/E` by a factor `K` keeps the same time. -/
theorem refined_time (N E K : Nat) (hE : 0 < E) (hEK : 0 < E * K) :
    Fraction.equiv (duration (E * K) (total (unitCells (N * K))) hEK) (duration E N hE) := by
  rw [unitCells_total]
  unfold Fraction.equiv duration
  dsimp
  simp only [Int.ofNat_mul]
  ac_rfl

/-- Nat core of the estimate: `N*K*d ≤ n*2*(E*K)*(E*K)` once `K > N*d`,
    `n ≥ 1` and `E ≥ 1`. -/
private theorem nat_bound (N E n d : Nat) (hE : 0 < E) (hn : 0 < n) :
    N * (N * d + 1) * d ≤ n * (2 * ((E * (N * d + 1)) * (E * (N * d + 1)))) := by
  have hK : N * d ≤ N * d + 1 := Nat.le_succ _
  have h1 : N * (N * d + 1) * d ≤ (N * d + 1) * (N * d + 1) := by
    calc N * (N * d + 1) * d = (N * d) * (N * d + 1) := by ac_rfl
      _ ≤ (N * d + 1) * (N * d + 1) := Nat.mul_le_mul_right _ hK
  have hE1 : 1 ≤ E * E := Nat.mul_le_mul hE hE
  have h2 : (N * d + 1) * (N * d + 1) ≤ (E * E) * ((N * d + 1) * (N * d + 1)) := by
    calc (N * d + 1) * (N * d + 1) = 1 * ((N * d + 1) * (N * d + 1)) := (Nat.one_mul _).symm
      _ ≤ (E * E) * ((N * d + 1) * (N * d + 1)) := Nat.mul_le_mul_right _ hE1
  have h3 : (E * E) * ((N * d + 1) * (N * d + 1)) ≤
      n * (2 * ((E * (N * d + 1)) * (E * (N * d + 1)))) := by
    calc (E * E) * ((N * d + 1) * (N * d + 1))
        = 1 * (1 * ((E * (N * d + 1)) * (E * (N * d + 1)))) := by
          simp only [Nat.one_mul]; ac_rfl
      _ ≤ n * (2 * ((E * (N * d + 1)) * (E * (N * d + 1)))) :=
          Nat.mul_le_mul hn (Nat.mul_le_mul_right _ (by decide))
  exact Nat.le_trans h1 (Nat.le_trans h2 h3)

/-- For every positive rational tolerance and rational time `N/E`, an explicit
    uniform refinement (factor `K = N*den(ε)+1`, unit cells over `E*K`) makes
    the exact constant-force residual coefficient `Q/(2D²)` at most the
    tolerance.  Together with `candidate_partitionMotion_residual`, the actual
    polygon position at `N/E` is within that coefficient (along `a`) of the
    constructed candidate. -/
theorem uniform_refinement_small (N E : Nat) (hE : 0 < E) (eps : Fraction)
    (heps : Fraction.positive eps) :
    ∃ K : Nat, ∃ hEK : 0 < E * K,
      Fraction.equiv (duration (E * K) (total (unitCells (N * K))) hEK) (duration E N hE) ∧
      Fraction.le (residualCoefficient (E * K) (squares (unitCells (N * K))) hEK) eps := by
  have hdpos := eps.den_pos
  have hnpos : 0 < eps.num := heps
  let d := eps.den.toNat
  let n := eps.num.toNat
  have hd : (d : Int) = eps.den := Int.toNat_of_nonneg (Int.le_of_lt hdpos)
  have hn : (n : Int) = eps.num := Int.toNat_of_nonneg (Int.le_of_lt hnpos)
  have hn0 : 0 < n := by omega
  have hEK : 0 < E * (N * d + 1) := Nat.mul_pos hE (Nat.succ_pos _)
  refine ⟨N * d + 1, hEK, refined_time N E _ hE hEK, ?_⟩
  have hq := stats_bound 1 (unitCells (N * (N * d + 1))) (unitCells_le_one _)
  rw [Nat.one_mul] at hq
  change squares (unitCells (N * (N * d + 1))) ≤ total (unitCells (N * (N * d + 1))) at hq
  rw [unitCells_total] at hq
  have hnat := nat_bound N E n d hE hn0
  have hchain : squares (unitCells (N * (N * d + 1))) * d ≤
      n * (2 * ((E * (N * d + 1)) * (E * (N * d + 1)))) :=
    Nat.le_trans (Nat.mul_le_mul_right d hq) hnat
  have hint := Int.ofNat_le.mpr hchain
  unfold Fraction.le residualCoefficient Fraction.half squareDuration
  dsimp
  rw [← hd, ← hn]
  simp only [Int.ofNat_mul] at hint ⊢
  have h2 : ((2 : Nat) : Int) = 2 := rfl
  rw [h2] at hint
  simpa only [Int.ofNat_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hint

end NewtonLimitDynamics.Polygon.UniformRefinement
