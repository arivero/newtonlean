import NewtonLimitDynamics.Common.Quadratic
import Std

namespace NewtonLimitDynamics
/-- Signed rational representatives, deliberately unnormalised. Equality of
    magnitudes is cross multiplication, not equality of representations. -/
structure Fraction where
  num : Int
  den : Int
  den_pos : 0 < den

namespace Fraction

def lt (a b : Fraction) := a.num * b.den < b.num * a.den
def le (a b : Fraction) := a.num * b.den ≤ b.num * a.den
def equiv (a b : Fraction) := a.num * b.den = b.num * a.den
def positive (a : Fraction) := 0 < a.num
def ofInt (n : Int) : Fraction := ⟨n, 1, by decide⟩
def add (a b : Fraction) : Fraction :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩
def mul (a b : Fraction) : Fraction :=
  ⟨a.num * b.num, a.den * b.den, Int.mul_pos a.den_pos b.den_pos⟩
def half (a : Fraction) : Fraction := ⟨a.num, 2 * a.den, Int.mul_pos (by decide) a.den_pos⟩

/-- Unsigned scalar magnitude. This arithmetic operation does not identify a
    geometric region between paths or erase the need to sum separate lobes. -/
def abs (a : Fraction) : Fraction := ⟨a.num.natAbs, a.den, a.den_pos⟩

theorem abs_num_nonnegative (a : Fraction) : 0 ≤ a.abs.num := Int.ofNat_nonneg _

/-- Unsigned magnitude respects equality of rational values, not just equality
    of their unnormalised representations. -/
theorem abs_equiv {a b : Fraction} (h : equiv a b) : equiv a.abs b.abs := by
  have hn := congrArg Int.natAbs h
  have hi := congrArg (fun n : Nat => (n : Int)) hn
  simp only [Int.natAbs_mul, Int.ofNat_mul,
    Int.natAbs_of_nonneg (Int.le_of_lt a.den_pos),
    Int.natAbs_of_nonneg (Int.le_of_lt b.den_pos)] at hi
  exact hi

theorem abs_mul (a b : Fraction) : equiv (mul a b).abs (mul a.abs b.abs) := by
  unfold equiv abs mul
  dsimp
  rw [Int.natAbs_mul, Int.ofNat_mul]

theorem abs_of_nonnegative (a : Fraction) (ha : 0 ≤ a.num) : equiv a.abs a := by
  unfold equiv abs
  dsimp
  rw [Int.natAbs_of_nonneg ha]

theorem abs_neg (a : Fraction) : equiv (⟨-a.num, a.den, a.den_pos⟩ : Fraction).abs a.abs := by
  unfold equiv abs
  dsimp
  rw [Int.natAbs_neg]

/-- Rational triangle estimate for finite perturbation accounting. -/
theorem abs_add_le (a b : Fraction) : le (add a b).abs (add a.abs b.abs) := by
  have hn := Int.natAbs_add_le (a.num * b.den) (b.num * a.den)
  have hi := Int.ofNat_le.mpr hn
  simp only [Int.ofNat_add, Int.natAbs_mul, Int.ofNat_mul,
    Int.natAbs_of_nonneg (Int.le_of_lt a.den_pos),
    Int.natAbs_of_nonneg (Int.le_of_lt b.den_pos)] at hi
  unfold le abs add
  dsimp
  exact Int.mul_le_mul_of_nonneg_right hi
    (Int.le_of_lt (Int.mul_pos a.den_pos b.den_pos))

private theorem transfer {a b c : Fraction} (h : le a b) (k : le b c) : le a c := by
  have h' := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt c.den_pos)
  have k' := Int.mul_le_mul_of_nonneg_right k (Int.le_of_lt a.den_pos)
  unfold le at *
  have mid : b.num * a.den * c.den = b.num * c.den * a.den := by ac_rfl
  rw [mid] at h'
  have z := Int.le_trans h' k'
  have l : a.num * b.den * c.den = (a.num * c.den) * b.den := by ac_rfl
  have r : c.num * b.den * a.den = (c.num * a.den) * b.den := by ac_rfl
  rw [l, r] at z
  exact Int.le_of_mul_le_mul_right z b.den_pos

private theorem mixed {a b c : Fraction} (h : lt a b) (k : le b c) : lt a c := by
  have h' := Int.mul_lt_mul_of_pos_right h c.den_pos
  have k' := Int.mul_le_mul_of_nonneg_right k (Int.le_of_lt a.den_pos)
  unfold lt le at *
  have mid : b.num * a.den * c.den = b.num * c.den * a.den := by ac_rfl
  rw [mid] at h'
  have z := Int.lt_of_lt_of_le h' k'
  have l : a.num * b.den * c.den = (a.num * c.den) * b.den := by ac_rfl
  have r : c.num * b.den * a.den = (c.num * a.den) * b.den := by ac_rfl
  rw [l, r] at z
  exact Int.lt_of_mul_lt_mul_right z (Int.le_of_lt b.den_pos)

private theorem mixed' {a b c : Fraction} (h : le a b) (k : lt b c) : lt a c := by
  have h' := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt c.den_pos)
  have k' := Int.mul_lt_mul_of_pos_right k a.den_pos
  unfold lt le at *
  have mid : b.num * a.den * c.den = b.num * c.den * a.den := by ac_rfl
  rw [mid] at h'
  have z := Int.lt_of_le_of_lt h' k'
  have l : a.num * b.den * c.den = (a.num * c.den) * b.den := by ac_rfl
  have r : c.num * b.den * a.den = (c.num * a.den) * b.den := by ac_rfl
  rw [l, r] at z
  exact Int.lt_of_mul_lt_mul_right z (Int.le_of_lt b.den_pos)

theorem half_lt (a : Fraction) (h : positive a) : lt a.half a := by
  have hp := Int.mul_pos h a.den_pos
  unfold lt half
  dsimp
  have e : a.num * (2 * a.den) = 2 * (a.num * a.den) := by ac_rfl
  rw [e]
  omega

def magnitudes : Magnitudes Fraction where
  positive := positive
  lt := lt
  le := le
  inhabited_positive := ⟨ofInt 1, by unfold positive ofInt; decide⟩
  lt_irrefl := fun _ => Int.lt_irrefl _
  le_refl := fun _ => Int.le_refl _
  le_trans := transfer
  lt_implies_le := Int.le_of_lt
  surrounds := by
    intro c
    refine ⟨⟨c.num - 1, c.den, c.den_pos⟩, ⟨c.num + 1, c.den, c.den_pos⟩, ?_, ?_⟩
    · unfold lt
      dsimp
      rw [Int.sub_mul, Int.one_mul]
      have := c.den_pos
      omega
    · unfold lt
      dsimp
      rw [Int.add_mul, Int.one_mul]
      have := c.den_pos
      omega
  lt_of_lt_le := mixed
  lt_of_le_lt := mixed'
  shrink := fun d hd => ⟨d.half, hd, half_lt d hd⟩
  refine := by
    intro a b ha hb
    by_cases h : le a b
    · exact ⟨a, ha, fun _ _ hx => ⟨hx, mixed hx h⟩⟩
    · have hba : le b a := by unfold le at *; omega
      exact ⟨b, hb, fun _ _ hx => ⟨mixed hx hba, hx⟩⟩

theorem equiv_iff_mutual_le (a b : Fraction) : equiv a b ↔ le a b ∧ le b a := by
  unfold equiv le
  omega

theorem equiv_refl (a : Fraction) : equiv a a := rfl

theorem equiv_symm {a b : Fraction} (h : equiv a b) : equiv b a := h.symm

theorem equiv_trans {a b c : Fraction} (h : equiv a b) (k : equiv b c) : equiv a c := by
  obtain ⟨hab, hba⟩ := (equiv_iff_mutual_le a b).mp h
  obtain ⟨hbc, hcb⟩ := (equiv_iff_mutual_le b c).mp k
  exact (equiv_iff_mutual_le a c).mpr ⟨transfer hab hbc, transfer hcb hba⟩

theorem le_of_equiv {a b : Fraction} (h : equiv a b) : le a b :=
  ((equiv_iff_mutual_le a b).mp h).1

theorem le_equiv_right {a b c : Fraction} (h : le a b) (k : equiv b c) : le a c :=
  transfer h (le_of_equiv k)

theorem le_equiv_left {a b c : Fraction} (h : equiv a b) (k : le b c) : le a c :=
  transfer (le_of_equiv h) k

/-- Addition preserves weak order: arithmetic and comparisons are compatible. -/
theorem add_le_add_right {a b : Fraction} (h : le a b) (c : Fraction) :
    le (add a c) (add b c) := by
  have hp := Int.mul_pos c.den_pos c.den_pos
  have hm := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hp)
  unfold le add at *
  dsimp
  simp only [Int.add_mul]
  have e1 : a.num * c.den * (b.den * c.den) = (a.num * b.den) * (c.den * c.den) := by ac_rfl
  have e2 : b.num * c.den * (a.den * c.den) = (b.num * a.den) * (c.den * c.den) := by ac_rfl
  have e3 : c.num * a.den * (b.den * c.den) = c.num * b.den * (a.den * c.den) := by ac_rfl
  rw [e1, e2, e3]
  omega

theorem mul_le_mul_positive {a b : Fraction} (h : le a b) (c : Fraction)
    (hc : positive c) : le (mul a c) (mul b c) := by
  have hp := Int.mul_pos hc c.den_pos
  have hm := Int.mul_le_mul_of_nonneg_right h (Int.le_of_lt hp)
  unfold le mul at *
  dsimp
  have e1 : a.num * c.num * (b.den * c.den) = (a.num * b.den) * (c.num * c.den) := by ac_rfl
  have e2 : b.num * c.num * (a.den * c.den) = (b.num * a.den) * (c.num * c.den) := by ac_rfl
  rw [e1, e2]
  exact hm

theorem add_comm (a b : Fraction) : equiv (add a b) (add b a) := by
  unfold equiv add
  dsimp
  simp only [Int.mul_comm, Int.add_comm]

theorem add_le_add_left {a b : Fraction} (h : le a b) (c : Fraction) :
    le (add c a) (add c b) :=
  le_equiv_left (add_comm c a)
    (le_equiv_right (add_le_add_right h c) (add_comm b c))

theorem add_le_add {a b c d : Fraction} (h : le a b) (k : le c d) :
    le (add a c) (add b d) :=
  transfer (add_le_add_right h c) (add_le_add_left k b)

/-- Weak-order multiplication also permits a zero factor. -/
theorem mul_le_mul_nonnegative {a b : Fraction} (h : le a b) (c : Fraction)
    (hc : 0 ≤ c.num) : le (mul a c) (mul b c) := by
  have hp := Int.mul_nonneg hc (Int.le_of_lt c.den_pos)
  have hm := Int.mul_le_mul_of_nonneg_right h hp
  unfold le mul at *
  dsimp
  have e1 : a.num * c.num * (b.den * c.den) = (a.num * b.den) * (c.num * c.den) := by ac_rfl
  have e2 : b.num * c.num * (a.den * c.den) = (b.num * a.den) * (c.num * c.den) := by ac_rfl
  rw [e1, e2]
  exact hm

theorem mul_comm (a b : Fraction) : equiv (mul a b) (mul b a) := by
  unfold equiv mul
  dsimp
  ac_rfl

theorem mul_le_mul_nonnegative_left {a b : Fraction} (h : le a b) (c : Fraction)
    (hc : 0 ≤ c.num) : le (mul c a) (mul c b) :=
  le_equiv_left (mul_comm c a)
    (le_equiv_right (mul_le_mul_nonnegative h c hc) (mul_comm b c))

/-- Cancellation can make the triangle estimate strict; absolute sums cannot
    be replaced by the absolute value of the total signed sum. -/
theorem abs_add_strict_example :
    lt (add (⟨1, 2, by decide⟩ : Fraction) ⟨-1, 2, by decide⟩).abs
      (add (⟨1, 2, by decide⟩ : Fraction).abs (⟨-1, 2, by decide⟩ : Fraction).abs) := by
  unfold lt add abs
  decide

/-- The actual ratio s/t²; time has to be positive before division is built. -/
def deflectionRatio (s t : Fraction) (ht : positive t) : Fraction :=
  ⟨s.num * (t.den * t.den), s.den * (t.num * t.num),
    Int.mul_pos s.den_pos (Int.mul_pos ht ht)⟩

/-- For a triangle of height k*t, twice its area is k*t². No geometric
    existence is inferred from this algebraic cancellation. -/
theorem square_ratio (k t : Fraction) (ht : positive t) :
    equiv (deflectionRatio (mul k (mul t t)) t ht) k := by
  unfold equiv deflectionRatio mul
  dsimp
  ac_rfl

theorem add_assoc (a b c : Fraction) : equiv (add (add a b) c) (add a (add b c)) := by
  unfold equiv add
  dsimp
  simp only [Int.add_mul, Int.mul_add]
  ac_rfl

theorem mul_assoc (a b c : Fraction) : equiv (mul (mul a b) c) (mul a (mul b c)) := by
  unfold equiv mul
  dsimp
  ac_rfl

theorem mul_add (a b c : Fraction) : equiv (mul a (add b c)) (add (mul a b) (mul a c)) := by
  unfold equiv mul add
  dsimp
  simp only [Int.add_mul, Int.mul_add]
  ac_rfl

theorem positive_mul (a b : Fraction) (ha : positive a) (hb : positive b) :
    positive (mul a b) := Int.mul_pos ha hb

theorem positive_iff_zero_lt (a : Fraction) : positive a ↔ lt (ofInt 0) a := by
  unfold positive lt ofInt
  simp

instance (a : Fraction) : Decidable (positive a) := inferInstanceAs (Decidable (0 < a.num))

def ratio (s : Fraction → Fraction) (t : Fraction) : Fraction :=
  if ht : positive t then deflectionRatio (s t) t ht else ofInt 0

/-- Transfer under pointwise equality of represented ratios on positive times. -/
theorem ultimate_congr (f k : Fraction → Fraction) (c : Fraction)
    (he : ∀ t, positive t → equiv (f t) (k t))
    (hk : Ultimate magnitudes k c) : Ultimate magnitudes f c := by
  intro a b hac hcb
  obtain ⟨d, hd, hp⟩ := hk a b hac hcb
  refine ⟨d, hd, ?_⟩
  intro t ht htd
  obtain ⟨hal, hub⟩ := hp t ht htd
  obtain ⟨hfk, hkf⟩ := (equiv_iff_mutual_le _ _).mp (he t ht)
  exact ⟨mixed hal hkf, mixed' hfk hub⟩

/-- Normalised doubled triangle area has the secant-slope limit. The slope
    limit is the remaining contact premise; a triangle limit is not a field. -/
theorem triangle_normalized_limit (slope : Fraction → Fraction) (c : Fraction)
    (hs : Ultimate magnitudes slope c) :
    Ultimate magnitudes (ratio (fun t => mul (slope t) (mul t t))) c := by
  apply ultimate_congr _ slope c
  · intro t ht
    simp only [ratio, dif_pos ht]
    exact square_ratio (slope t) t ht
  · exact hs

/-- Euclidean triangle area from base and corresponding perpendicular height. -/
def triangleArea (base height : Fraction) : Fraction := half (mul base height)

theorem triangle_area_ratio (slope time : Fraction) (ht : positive time) :
    equiv (deflectionRatio (triangleArea time (mul slope time)) time ht) (half slope) := by
  unfold equiv deflectionRatio triangleArea half mul
  dsimp
  ac_rfl

/-- Actual half-base-times-height triangles, with the contact limit displayed
    as the limit of half the secant slope. -/
theorem constructed_triangle_limit (slope : Fraction → Fraction) (c : Fraction)
    (hs : Ultimate magnitudes (fun t => half (slope t)) c) :
    Ultimate magnitudes (ratio (fun t => triangleArea t (mul (slope t) t))) c := by
  apply ultimate_congr _ (fun t => half (slope t)) c
  · intro t ht
    simp only [ratio, dif_pos ht]
    exact triangle_area_ratio (slope t) t ht
  · exact hs

/-- Arithmetic respects equality of represented magnitudes. -/
theorem mul_equiv_left (k : Fraction) {a b : Fraction} (h : equiv a b) :
    equiv (mul k a) (mul k b) := by
  unfold equiv mul at *
  dsimp
  calc
    k.num*a.num*(k.den*b.den) = (k.num*k.den)*(a.num*b.den) := by ac_rfl
    _ = (k.num*k.den)*(b.num*a.den) := by rw [h]
    _ = k.num*b.num*(k.den*a.den) := by ac_rfl

theorem add_equiv_right (k : Fraction) {a b : Fraction} (h : equiv a b) :
    equiv (add a k) (add b k) := by
  obtain ⟨hab, hba⟩ := (equiv_iff_mutual_le a b).mp h
  exact (equiv_iff_mutual_le _ _).mpr ⟨add_le_add_right hab k, add_le_add_right hba k⟩

-- Congruence, distributivity and sign lemmas shared by the Polygon modules.

theorem add_equiv {a b c d : Fraction} (h : equiv a b)
    (k : equiv c d) :
    equiv (add a c) (add b d) :=
  equiv_trans (add_equiv_right c h)
    (equiv_trans (add_comm b c)
      (equiv_trans (add_equiv_right b k) (add_comm d b)))

theorem mul_equiv {a b c d : Fraction} (h : equiv a b)
    (k : equiv c d) :
    equiv (mul a c) (mul b d) :=
  equiv_trans (mul_comm a c)
    (equiv_trans (mul_equiv_left c h)
      (equiv_trans (mul_comm c b) (mul_equiv_left b k)))

theorem add_equiv_left (c : Fraction) {a b : Fraction} (h : equiv a b) :
    equiv (add c a) (add c b) := by
  exact equiv_trans (add_comm c a)
    (equiv_trans (add_equiv_right c h) (add_comm b c))

theorem mul_equiv_right (c : Fraction) {a b : Fraction} (h : equiv a b) :
    equiv (mul a c) (mul b c) := by
  exact equiv_trans (mul_comm a c)
    (equiv_trans (mul_equiv_left c h) (mul_comm c b))

theorem le_add_nonnegative (a b : Fraction) (hb : 0 ≤ b.num) :
    le a (add a b) := by
  unfold le add
  dsimp
  have hp := Int.mul_nonneg (Int.mul_nonneg hb (Int.le_of_lt a.den_pos))
    (Int.le_of_lt a.den_pos)
  simp only [Int.add_mul]
  have he : a.num * (a.den * b.den) = a.num * b.den * a.den := by ac_rfl
  rw [he]
  omega

theorem nonnegative_add (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    0 ≤ (add a b).num := by
  unfold add
  exact Int.add_nonneg
    (Int.mul_nonneg ha (Int.le_of_lt b.den_pos))
    (Int.mul_nonneg hb (Int.le_of_lt a.den_pos))

theorem nonnegative_mul (a b : Fraction) (ha : 0 ≤ a.num) (hb : 0 ≤ b.num) :
    0 ≤ (mul a b).num := Int.mul_nonneg ha hb

theorem mul_zero (d : Fraction) :
    equiv (mul d (ofInt 0)) (ofInt 0) := by
  unfold equiv mul ofInt
  simp

theorem add_zero (c : Fraction) :
    equiv (add c (ofInt 0)) c := by
  unfold equiv add ofInt
  simp only [Int.mul_one, Int.zero_mul, Int.add_zero]
  try ac_rfl

theorem add_mul (a b c : Fraction) :
    equiv (mul (add a b) c)
      (add (mul a c) (mul b c)) := by
  unfold equiv add mul
  dsimp
  simp only [Int.add_mul, Int.mul_add]
  try ac_nf

end Fraction
end NewtonLimitDynamics
