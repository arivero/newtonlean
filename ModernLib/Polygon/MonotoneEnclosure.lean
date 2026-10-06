/-!
Finite form of the enclosure behind Lemma X, under the force clause that 1713
added (NATP00082 par28: *Vi finita, sive Vis illa determinata & immutabilis
sit, sive eadem continuo augetur vel continuo diminuatur*; 1687 NATP00077
par27 has *vi regulari*).  One-dimensional impulse construction with unit
time cells and integer magnitudes, starting at rest: drift with the current
velocity, then the impulse `a i` of cell `i`.  If every impulse lies between
`lo` and `hi`, the space described lies between the spaces described under the
constant forces `lo` and `hi`.  For a monotone force history these are the
initial and final forces.  A finite but non-monotone history escapes that
enclosure.  Rational cells follow by a common scaling (not formalized); no
limit, curve, or continuous force is produced.
-/

namespace NewtonLimitDynamics.Polygon.MonotoneEnclosure

/-- Velocity before cell `k`. -/
def vel (a : Nat → Int) : Nat → Int
  | 0 => 0
  | k + 1 => vel a k + a k

/-- Space described after `n` cells. -/
def pos (a : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => pos a n + vel a n

/-- `0 + 1 + ... + (n-1)`: the space coefficient of a constant unit force. -/
def tri : Nat → Int
  | 0 => 0
  | n + 1 => tri n + n

/-- Under a constant force the space described is `force * tri n`. -/
theorem pos_const (c : Int) : (n : Nat) → pos (fun _ => c) n = c * tri n ∧ vel (fun _ => c) n = c * n
  | 0 => by simp [pos, vel, tri]
  | n + 1 => by
      obtain ⟨hp, hv⟩ := pos_const c n
      simp only [pos, vel, tri, hp, hv, Int.mul_add, Int.mul_one, Int.ofNat_add]
      refine ⟨trivial, ?_⟩
      rw [Int.ofNat_one, Int.mul_one]

theorem vel_bounds (a : Nat → Int) (lo hi : Int) (n : Nat)
    (h : ∀ i, i < n → lo ≤ a i ∧ a i ≤ hi) :
    ∀ k, k ≤ n → lo * k ≤ vel a k ∧ vel a k ≤ hi * k := by
  intro k
  induction k with
  | zero => intro _; simp [vel]
  | succ k ih =>
      intro hk
      obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨h3, h4⟩ := h k (Nat.lt_of_succ_le hk)
      simp only [vel, Int.ofNat_add, Int.mul_add, Int.mul_one]
      constructor <;> omega

/-- Enclosure: impulses between `lo` and `hi` put the space described between
    the spaces described under the constant forces `lo` and `hi`. -/
theorem enclosure (a : Nat → Int) (lo hi : Int) (n : Nat)
    (h : ∀ i, i < n → lo ≤ a i ∧ a i ≤ hi) :
    lo * tri n ≤ pos a n ∧ pos a n ≤ hi * tri n := by
  have hv := vel_bounds a lo hi n h
  have key : ∀ m, m ≤ n → lo * tri m ≤ pos a m ∧ pos a m ≤ hi * tri m := by
    intro m
    induction m with
    | zero => intro _; simp [pos, tri]
    | succ m ih =>
        intro hm
        obtain ⟨h1, h2⟩ := ih (Nat.le_of_succ_le hm)
        obtain ⟨h3, h4⟩ := hv m (Nat.le_of_succ_le hm)
        simp only [pos, tri, Int.mul_add]
        constructor <;> omega
  exact key n (Nat.le_refl n)

/-- The 1713 clause: a force that continually increases (monotone history)
    gives the enclosure between the initial and final forces. -/
theorem monotone_enclosure (a : Nat → Int) (n : Nat)
    (hmono : ∀ i j, i ≤ j → j ≤ n → a i ≤ a j) :
    a 0 * tri (n + 1) ≤ pos a (n + 1) ∧ pos a (n + 1) ≤ a n * tri (n + 1) :=
  enclosure a (a 0) (a n) (n + 1) (fun i hi =>
    ⟨hmono 0 i (Nat.zero_le i) (Nat.le_of_lt_succ hi),
     hmono i n (Nat.le_of_lt_succ hi) (Nat.le_refl n)⟩)

/-- And a force that continually decreases, symmetrically. -/
theorem antitone_enclosure (a : Nat → Int) (n : Nat)
    (hanti : ∀ i j, i ≤ j → j ≤ n → a j ≤ a i) :
    a n * tri (n + 1) ≤ pos a (n + 1) ∧ pos a (n + 1) ≤ a 0 * tri (n + 1) :=
  enclosure a (a n) (a 0) (n + 1) (fun i hi =>
    ⟨hanti i n (Nat.le_of_lt_succ hi) (Nat.le_refl n),
     hanti 0 i (Nat.zero_le i) (Nat.le_of_lt_succ hi)⟩)

/-- A finite force that rises and falls (impulses 0, 5, 0) describes space 5,
    outside the enclosure `0 ≤ pos ≤ 0` fixed by its initial and final forces. -/
theorem nonmonotone_escapes :
    pos (fun i => if i = 1 then 5 else 0) 3 = 5 ∧
      (fun i => if i = 1 then (5 : Int) else 0) 0 * tri 3 = 0 ∧
      (fun i => if i = 1 then (5 : Int) else 0) 2 * tri 3 = 0 := by
  decide

end NewtonLimitDynamics.Polygon.MonotoneEnclosure
