import NewtonLimitDynamics.Polygon.Enclosure

namespace NewtonLimitDynamics.Contact

def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => nsum f n + f n

/-- Lower rectangles for a linear velocity diagram. With n equal cells the
    doubled lower sum differs from n² by n, yielding coefficient 1/2. -/
theorem linear_rectangles (n : Nat) : 2 * nsum (fun i => i) n + n = n*n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [nsum, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-- Lower rectangles for y=x². Division by 6n³ yields the area coefficient
    1/3 with explicit corrections -1/(2n)+1/(6n²), not an integral theorem. -/
theorem quadratic_rectangles (n : Nat) :
    6 * nsum (fun i => i*i) n + 3*(n*n) = 2*(n*n*n)+n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [nsum, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem upper_lower_gap (n : Nat) :
    nsum (fun i => (i+1)*(i+1)) n = nsum (fun i => i*i) n + n*n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [nsum, ih]

/-- Error of the lower quadratic rectangle sum in units of 6n³ is ≤3n²;
    after positive division this is ≤1/(2n). -/
theorem quadratic_lower_error (n : Nat) :
    2*(n*n*n) ≤ 6*nsum (fun i => i*i) n + 3*(n*n) := by
  have := quadratic_rectangles n
  omega

theorem sum_bound (f : Nat → Nat) (C n : Nat) (hf : ∀ i, i < n → f i ≤ C) :
    nsum f n ≤ n*C := by
  induction n with
  | zero => simp [nsum]
  | succ n ih =>
    have h := ih (fun i hi => hf i (by omega))
    have hn := hf n (by omega)
    simp only [nsum, Nat.add_mul, Nat.one_mul]
    omega

/-- Uniform partition error, expressed without division: n²*Σ error_i ≤ C.
    All errors use a common unit; the local bound is n³*error_i ≤ C for EVERY
    cell of the fixed interval. C must include the fixed interval's T³ factor.
    Positivity of n permits cancellation; pointwise local scaling is not enough. -/
theorem uniform_partition_error (error : Nat → Nat) (C n : Nat) (hn : 0 < n)
    (hlocal : ∀ i, i < n → n*n*n*error i ≤ C) :
    n*n*nsum error n ≤ C := by
  have hs := sum_bound (fun i => n*n*n*error i) C n hlocal
  have hmul : ∀ k, nsum (fun i => n*n*n*error i) k = n*n*n*nsum error k := by
    intro k
    induction k with
    | zero => simp [nsum]
    | succ k ih => simp [nsum, ih, Nat.mul_add]
  rw [hmul] at hs
  have he : n*n*n*nsum error n = n*(n*n*nsum error n) := by ac_rfl
  rw [he] at hs
  exact Nat.le_of_mul_le_mul_left hs hn

theorem nsum_mul (f : Nat → Nat) (k n : Nat) :
    nsum (fun i => f i*k) n = nsum f n*k := by
  induction n with
  | zero => simp [nsum]
  | succ n ih => simp [nsum, ih, Nat.add_mul]

/-- Rational version: errors have a common denominator D within this partition,
    and the fixed uniform coefficient is Knum/Kden. D may vary with refinement.
    Hence this is not restricted to integer errors eventually becoming zero. -/
theorem rational_uniform_partition_error (error : Nat → Nat)
    (Knum Kden D n : Nat) (hk : 0 < Kden) (hd : 0 < D) (hn : 0 < n)
    (hlocal : ∀ i, i < n → n*n*n*(error i*Kden) ≤ Knum*D) :
    Fraction.le
      ⟨(nsum error n : Int), (D : Int), Int.ofNat_lt.mpr hd⟩
      ⟨(Knum : Int), (Kden*(n*n) : Nat),
        Int.ofNat_lt.mpr (Nat.mul_pos hk (Nat.mul_pos hn hn))⟩ := by
  have h := uniform_partition_error (fun i => error i*Kden) (Knum*D) n hn hlocal
  rw [nsum_mul] at h
  have he : n*n*(nsum error n*Kden) = nsum error n*(Kden*(n*n)) := by ac_rfl
  rw [he] at h
  unfold Fraction.le
  dsimp
  simpa only [Int.ofNat_mul] using (Int.ofNat_le.mpr h)

/-- The same error sum with a nonuniform coefficient cannot in general obey
    the proposed uniform budget. This boundary is executable without analysis. -/
example : ¬ (2*2*nsum (fun _ => 1) 2 ≤ 1) := by decide

/-- Sequential vanishing appropriate to a finite-sum refinement index. -/
def SeqVanishes (error : Nat → Fraction) : Prop :=
  ∀ epsilon, Fraction.positive epsilon →
    ∃ N : Nat, ∀ n, N ≤ n → Fraction.lt (error n) epsilon

/-- An explicit Archimedean argument for rational error budgets C/n.
    This imports no analytic convergence theorem. -/
theorem reciprocal_budget_vanishes (error : Nat → Fraction) (C : Nat)
    (hbound : ∀ n, (hn : 0 < n) → Fraction.le (error n)
      ⟨(C : Int), (n : Int), Int.ofNat_lt.mpr hn⟩) : SeqVanishes error := by
  intro e he
  refine ⟨C * e.den.natAbs + 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  have hd : (e.den.natAbs : Int) = e.den := Int.natAbs_of_nonneg (Int.le_of_lt e.den_pos)
  have hlarge : (C : Int) * e.den < (n : Int) := by
    have hnat : C * e.den.natAbs < n := by omega
    have hi := Int.ofNat_lt.mpr hnat
    simpa only [Int.ofNat_mul, hd] using hi
  have hen : 1 ≤ e.num := by unfold Fraction.positive at he; omega
  have hm := Int.mul_le_mul_of_nonneg_right hen (Int.le_of_lt (Int.ofNat_lt.mpr hnpos))
  have hbracket : Fraction.lt ⟨(C : Int), (n : Int), Int.ofNat_lt.mpr hnpos⟩ e := by
    unfold Fraction.lt
    dsimp
    simp only [Int.one_mul] at hm
    omega
  exact Fraction.magnitudes.lt_of_le_lt (hbound n hnpos) hbracket

end NewtonLimitDynamics.Contact
