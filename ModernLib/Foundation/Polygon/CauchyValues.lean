import ModernLib.Foundation.Polygon.EndpointCauchyName
import BarrowLib.Polygon.GeometricTail

namespace NewtonLimitDynamics.Polygon.CauchyValues
open NewtonLimitDynamics
open TimeSubdivision
open PointBounds
open HarmonicComparison
open HarmonicAccumulation
open HarmonicDyadic

def distance (a b : Point × Point) : Fraction := stateNorm (stateSub a b)

/-- Position magnitudes on a Cauchy tail are bounded by the magnitude of one
actual approximant plus one. This is derived, rather than a field of a name. -/
theorem position_bounded_tail (a : EndpointCauchyName) :
    ∃ R : Fraction, 0 ≤ R.num ∧ ∃ N : Nat, ∀ j, N≤j →
      Fraction.le (pointNorm (a.approx j).1) R := by
  obtain ⟨N,hN⟩ := a.cauchy (Fraction.ofInt 1) (by decide)
  let R := Fraction.add (Fraction.ofInt 1) (pointNorm (a.approx N).1)
  refine ⟨R,Fraction.nonnegative_add _ _ (by decide) (pointNorm_nonnegative _),N,fun j hj => ?_⟩
  have hp := Fraction.magnitudes.le_trans (point_le_state (stateSub (a.approx j) (a.approx N)))
    (Fraction.magnitudes.lt_implies_le (hN j N hj (Nat.le_refl _)))
  exact Fraction.magnitudes.le_trans
    (FiniteEstimates.pointNorm_le_distance_add (a.approx j).1 (a.approx N).1)
    (Fraction.add_le_add_right hp (pointNorm (a.approx N).1))

/-- A Cauchy name is bounded on a proved tail, so its position magnitude
times a geometric mesh tends to zero. No boundedness field is supplied. -/
theorem mesh_position_product_vanishes (a : EndpointCauchyName)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ j, N≤j →
      Fraction.lt (Fraction.mul (duration (Fraction.ofInt 1) j) (pointNorm (a.approx j).1)) eps := by
  obtain ⟨R,hR,N,hN⟩ := position_bounded_tail a
  obtain ⟨M,hM⟩ := HarmonicTimeRealization.duration_eventually_small R eps hR heps
  refine ⟨max N M,fun j hj => ?_⟩
  have hc := Fraction.mul_le_mul_nonnegative_left (hN j (by omega)) (duration (Fraction.ofInt 1) j)
    (by change (0 : Int)≤1; omega)
  have he : Fraction.equiv (Fraction.mul (duration (Fraction.ofInt 1) j) R) (duration R j) := by
    simp only [duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,Int.one_mul,Int.mul_one]
    ac_nf
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_equiv_right hc he) (hM j (by omega))

private theorem equiv_zero_num (a : Fraction)
    (h : Fraction.equiv a (Fraction.ofInt 0)) : a.num = 0 := by
  unfold Fraction.equiv Fraction.ofInt at h
  simpa only [Int.mul_one, Int.zero_mul] using h

private theorem zero_lt_positive (eps : Fraction) (heps : 0 < eps.num) :
    Fraction.lt (Fraction.ofInt 0) eps := by
  unfold Fraction.lt Fraction.ofInt
  dsimp
  simp only [Int.zero_mul, Int.mul_one]
  exact heps

theorem distance_self_lt (a : Point × Point) (eps : Fraction)
    (heps : 0 < eps.num) : Fraction.lt (distance a a) eps := by
  have hz := equiv_zero_num _ (stateSub_self_norm_zero a)
  unfold Fraction.lt distance
  simp only [hz, Int.zero_mul, Int.mul_one]
  exact Int.mul_pos heps (distance a a).den_pos

def NameEquiv (a b : EndpointCauchyName) : Prop :=
  ∀ eps : Fraction, 0 < eps.num →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Fraction.lt (distance (a.approx n) (b.approx n)) eps

theorem nameEquiv_refl (a : EndpointCauchyName) : NameEquiv a a := by
  intro eps heps
  exact ⟨0, fun n _ => distance_self_lt (a.approx n) eps heps⟩

theorem nameEquiv_symm {a b : EndpointCauchyName}
    (hab : NameEquiv a b) : NameEquiv b a := by
  intro eps heps
  obtain ⟨N, hN⟩ := hab eps heps
  refine ⟨N, ?_⟩
  intro n hn
  have hs := stateSub_norm_symm (b.approx n) (a.approx n)
  exact Fraction.magnitudes.lt_of_le_lt
    ((Fraction.equiv_iff_mutual_le _ _).mp hs).1 (hN n hn)

private theorem half_add_equiv (eps : Fraction) :
    Fraction.equiv (Fraction.add eps.half eps.half) eps :=
  Fraction.half_add_self eps

private theorem half_lt (eps : Fraction) (heps : 0 < eps.num) :
    Fraction.lt eps.half eps := Fraction.half_lt eps heps

theorem nameEquiv_trans {a b c : EndpointCauchyName}
    (hab : NameEquiv a b) (hbc : NameEquiv b c) : NameEquiv a c := by
  intro eps heps
  let q := eps.half.half
  obtain ⟨N₁, h₁⟩ := hab q heps
  obtain ⟨N₂, h₂⟩ := hbc q heps
  refine ⟨N₁ + N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have htri := stateSub_triangle (a.approx n) (b.approx n) (c.approx n)
  have hadd := Fraction.add_le_add
    (Fraction.magnitudes.lt_implies_le (h₁ n hn₁))
    (Fraction.magnitudes.lt_implies_le (h₂ n hn₂))
  have hbound := Fraction.le_equiv_right
    (Fraction.magnitudes.le_trans htri hadd) (half_add_equiv eps.half)
  exact Fraction.magnitudes.lt_of_le_lt hbound (half_lt eps heps)

instance : Setoid EndpointCauchyName where
  r := NameEquiv
  iseqv := ⟨nameEquiv_refl, @nameEquiv_symm, @nameEquiv_trans⟩

def Value := Quotient (inferInstance : Setoid EndpointCauchyName)

def realize (a : EndpointCauchyName) : Value := Quotient.mk _ a

private theorem add_zero_split (a b : Fraction)
    (ha : 0 ≤ a.num) (hb : 0 ≤ b.num)
    (h : Fraction.equiv (Fraction.add a b) (Fraction.ofInt 0)) :
    a.num = 0 ∧ b.num = 0 := by
  have hz := equiv_zero_num _ h
  have h₁ : 0 ≤ a.num * b.den :=
    Int.mul_nonneg ha (Int.le_of_lt b.den_pos)
  have h₂ : 0 ≤ b.num * a.den :=
    Int.mul_nonneg hb (Int.le_of_lt a.den_pos)
  have hs : a.num * b.den + b.num * a.den = 0 := hz
  have ha' : a.num * b.den = 0 := by omega
  have hb' : b.num * a.den = 0 := by omega
  constructor
  · rcases (Int.mul_eq_zero.mp ha') with hz' | hz'
    · exact hz'
    · have hd := b.den_pos
      omega
  · rcases (Int.mul_eq_zero.mp hb') with hz' | hz'
    · exact hz'
    · have hd := a.den_pos
      omega

private theorem pointNorm_zero_coords (p : Point)
    (h : (pointNorm p).num = 0) : p.1.num = 0 ∧ p.2.num = 0 := by
  have he : Fraction.equiv (pointNorm p) (Fraction.ofInt 0) := by
    unfold Fraction.equiv Fraction.ofInt
    simp [h]
  have hs := add_zero_split p.1.abs p.2.abs
    (Fraction.abs_num_nonnegative p.1)
    (Fraction.abs_num_nonnegative p.2) he
  constructor
  · have hh : p.1.num.natAbs = 0 := Int.ofNat_eq_zero.mp hs.1
    exact Int.natAbs_eq_zero.mp hh
  · have hh : p.2.num.natAbs = 0 := Int.ofNat_eq_zero.mp hs.2
    exact Int.natAbs_eq_zero.mp hh

private theorem fraction_sub_zero_equiv (a b : Fraction)
    (h : (Fraction.add a ⟨-b.num, b.den, b.den_pos⟩).num = 0) :
    Fraction.equiv a b := by
  unfold Fraction.equiv Fraction.add at *
  dsimp at *
  rw [Int.neg_mul] at h
  omega

theorem distance_zero_iff_stateEquiv (a b : Point × Point) :
    Fraction.equiv (distance a b) (Fraction.ofInt 0) ↔ stateEquiv a b := by
  constructor
  · intro hz
    have hs := add_zero_split (pointNorm (stateSub a b).1)
      (pointNorm (stateSub a b).2)
      (pointNorm_nonnegative _) (pointNorm_nonnegative _) hz
    have hp := pointNorm_zero_coords (stateSub a b).1 hs.1
    have hv := pointNorm_zero_coords (stateSub a b).2 hs.2
    exact ⟨⟨fraction_sub_zero_equiv a.1.1 b.1.1 hp.1,
        fraction_sub_zero_equiv a.1.2 b.1.2 hp.2⟩,
      ⟨fraction_sub_zero_equiv a.2.1 b.2.1 hv.1,
        fraction_sub_zero_equiv a.2.2 b.2.2 hv.2⟩⟩
  · intro hab
    have hs : stateEquiv (stateSub a b) (stateSub b b) :=
      stateSub_congr hab
        ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
          ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
    exact Fraction.equiv_trans (stateNorm_equiv hs)
      (stateSub_self_norm_zero b)

def constantName (s : Point × Point) : EndpointCauchyName where
  approx := fun _ => s
  cauchy := by
    intro eps heps
    exact ⟨0, fun _ _ _ _ => distance_self_lt s eps heps⟩

def embed (s : Point × Point) : Value := realize (constantName s)

theorem nameEquiv_of_levelwise_stateEquiv (a b : EndpointCauchyName)
    (h : ∀ n, stateEquiv (a.approx n) (b.approx n)) : NameEquiv a b := by
  intro eps heps
  refine ⟨0, ?_⟩
  intro n _
  have hr : stateEquiv (b.approx n) (b.approx n) :=
    ⟨⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩,
      ⟨Fraction.equiv_refl _, Fraction.equiv_refl _⟩⟩
  have he : Fraction.equiv (distance (a.approx n) (b.approx n))
      (distance (b.approx n) (b.approx n)) :=
    stateNorm_equiv (stateSub_congr (h n) hr)
  exact Fraction.magnitudes.lt_of_le_lt (Fraction.le_of_equiv he)
    (distance_self_lt _ eps heps)

theorem constantName_equiv_iff (a b : Point × Point) :
    NameEquiv (constantName a) (constantName b) ↔ stateEquiv a b := by
  constructor
  · intro hab
    let d := distance a b
    have hnon := stateNorm_nonnegative (stateSub a b)
    have hnon' : 0 ≤ d.num := hnon
    by_cases hz : d.num = 0
    · have he : Fraction.equiv d (Fraction.ofInt 0) := by
        unfold Fraction.equiv Fraction.ofInt
        simp [hz]
      exact (distance_zero_iff_stateEquiv a b).mp he
    · have hd : 0 < d.num := by omega
      obtain ⟨N, hN⟩ := hab d.half hd
      have hbad : Fraction.lt d d.half := hN N (Nat.le_refl N)
      have hhalf := Fraction.half_lt d hd
      have hloop := Fraction.magnitudes.lt_of_lt_le hbad
        (Fraction.magnitudes.lt_implies_le hhalf)
      exact False.elim ((Fraction.magnitudes.lt_irrefl d) hloop)
  · intro hab eps heps
    have hz := (distance_zero_iff_stateEquiv a b).mpr hab
    have hnum := equiv_zero_num _ hz
    refine ⟨0, ?_⟩
    intro n _
    change Fraction.lt (distance a b) eps
    unfold Fraction.lt
    simp only [hnum, Int.zero_mul, Int.mul_one]
    exact Int.mul_pos heps (distance a b).den_pos

theorem embed_eq_iff_stateEquiv (a b : Point × Point) :
    embed a = embed b ↔ stateEquiv a b := by
  constructor
  · intro h
    exact (constantName_equiv_iff a b).mp (Quotient.exact h)
  · intro h
    exact Quotient.sound ((constantName_equiv_iff a b).mpr h)

theorem add_lt_add_left {a b : Fraction}
    (hab : Fraction.lt a b) (c : Fraction) :
    Fraction.lt (Fraction.add c a) (Fraction.add c b) :=
  Fraction.add_lt_add_left hab c

private theorem add_lt_add_right {a b : Fraction}
    (hab : Fraction.lt a b) (c : Fraction) :
    Fraction.lt (Fraction.add a c) (Fraction.add b c) :=
  Fraction.add_lt_add_right hab c

private theorem lt_equiv_left {a b c : Fraction}
    (hab : Fraction.equiv a b) (hbc : Fraction.lt b c) : Fraction.lt a c :=
  Fraction.magnitudes.lt_of_le_lt
    ((Fraction.equiv_iff_mutual_le _ _).mp hab).1 hbc

theorem lt_equiv_right {a b c : Fraction}
    (hab : Fraction.lt a b) (hbc : Fraction.equiv b c) : Fraction.lt a c :=
  Fraction.magnitudes.lt_of_lt_le hab
    ((Fraction.equiv_iff_mutual_le _ _).mp hbc).1

private theorem three_quarters_lt (R eps : Fraction) (heps : 0 < eps.num) :
    Fraction.lt
      (Fraction.add (Fraction.add
        (Fraction.add R eps.half.half) eps.half.half) eps.half.half)
      (Fraction.add R eps) := by
  let q := eps.half.half
  have hq : Fraction.lt q eps.half := Fraction.half_lt eps.half heps
  have h₁ := add_lt_add_left hq eps.half
  have h₂ : Fraction.lt (Fraction.add q eps.half) eps :=
    lt_equiv_right
      (lt_equiv_left (Fraction.add_comm q eps.half) h₁)
      (half_add_equiv eps)
  have h₃ := add_lt_add_left h₂ R
  have hp : Fraction.equiv (Fraction.add q q) eps.half :=
    half_add_equiv eps.half
  have hi := Fraction.add_equiv (Fraction.equiv_refl q) hp
  have ho := Fraction.add_equiv (Fraction.equiv_refl R) hi
  have he := Fraction.equiv_trans
    (Fraction.add_assoc (Fraction.add R q) q q)
    (Fraction.equiv_trans (Fraction.add_assoc R q (Fraction.add q q)) ho)
  exact lt_equiv_left he h₃

def NameBound (a b : EndpointCauchyName) (R : Fraction) : Prop :=
  ∀ eps : Fraction, 0 < eps.num →
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Fraction.lt (distance (a.approx n) (b.approx n))
        (Fraction.add R eps)

theorem nameBound_symm {a b : EndpointCauchyName} {R : Fraction}
    (h : NameBound a b R) : NameBound b a R := by
  intro eps heps
  obtain ⟨N, hN⟩ := h eps heps
  refine ⟨N, ?_⟩
  intro n hn
  exact lt_equiv_left
    (stateSub_norm_symm (b.approx n) (a.approx n)) (hN n hn)

private theorem distance_three (a a' b b' : Point × Point) :
    Fraction.le (distance a' b')
      (Fraction.add (distance a' a)
        (Fraction.add (distance a b) (distance b b'))) := by
  have h₁ := stateSub_triangle a' a b'
  have h₂ := stateSub_triangle a b b'
  exact Fraction.magnitudes.le_trans h₁
    (Fraction.add_le_add_left h₂ (distance a' a))

private theorem three_quarters_reordered (R eps : Fraction)
    (heps : 0 < eps.num) :
    Fraction.lt
      (Fraction.add eps.half.half
        (Fraction.add (Fraction.add R eps.half.half) eps.half.half))
      (Fraction.add R eps) := by
  let q := eps.half.half
  have he : Fraction.equiv
      (Fraction.add q (Fraction.add (Fraction.add R q) q))
      (Fraction.add (Fraction.add (Fraction.add R q) q) q) := by
    simp only [Fraction.equiv, Fraction.add]
    simp only [Int.add_mul, Int.mul_add]
    ac_nf
  exact lt_equiv_left he (three_quarters_lt R eps heps)

private theorem nameBound_transport {a a' b b' : EndpointCauchyName} {R : Fraction}
    (ha : NameEquiv a a') (hb : NameEquiv b b') :
    NameBound a b R → NameBound a' b' R := by
  intro h eps heps
  let q := eps.half.half
  obtain ⟨N₁, h₁⟩ := nameEquiv_symm ha q heps
  obtain ⟨N₂, h₂⟩ := h q heps
  obtain ⟨N₃, h₃⟩ := hb q heps
  refine ⟨N₁ + N₂ + N₃, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have hn₃ : N₃ ≤ n := by omega
  have htri := distance_three (a.approx n) (a'.approx n)
    (b.approx n) (b'.approx n)
  have hsum := Fraction.add_le_add
    (Fraction.magnitudes.lt_implies_le (h₁ n hn₁))
    (Fraction.add_le_add
      (Fraction.magnitudes.lt_implies_le (h₂ n hn₂))
      (Fraction.magnitudes.lt_implies_le (h₃ n hn₃)))
  have hbound := Fraction.magnitudes.le_trans htri hsum
  exact Fraction.magnitudes.lt_of_le_lt hbound
    (three_quarters_reordered R eps heps)

theorem nameBound_congr {a a' b b' : EndpointCauchyName} {R : Fraction}
    (ha : NameEquiv a a') (hb : NameEquiv b b') :
    NameBound a b R ↔ NameBound a' b' R :=
  ⟨nameBound_transport ha hb,
    nameBound_transport (nameEquiv_symm ha) (nameEquiv_symm hb)⟩

/-- A closed rational radius bound, defined first on names and lifted only
after representative invariance has been proved. -/
def Within (x y : Value) (R : Fraction) : Prop :=
  Quotient.liftOn₂ x y (fun a b => NameBound a b R)
    (fun _ _ _ _ ha hb => propext (nameBound_congr ha hb))

theorem within_realize (a b : EndpointCauchyName) (R : Fraction) :
    Within (realize a) (realize b) R ↔ NameBound a b R := Iff.rfl

theorem within_symm (x y : Value) (R : Fraction)
    (h : Within x y R) : Within y x R := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b => exact nameBound_symm h

private theorem two_quarters_lt (R S eps : Fraction)
    (heps : 0 < eps.num) :
    Fraction.lt
      (Fraction.add (Fraction.add R eps.half.half)
        (Fraction.add S eps.half.half))
      (Fraction.add (Fraction.add R S) eps) := by
  let q := eps.half.half
  have he₁ : Fraction.equiv
      (Fraction.add (Fraction.add R q) (Fraction.add S q))
      (Fraction.add (Fraction.add R S) (Fraction.add q q)) := by
    simp only [Fraction.equiv, Fraction.add]
    simp only [Int.add_mul, Int.mul_add]
    ac_nf
  have he₂ := Fraction.add_equiv (Fraction.equiv_refl (Fraction.add R S))
    (half_add_equiv eps.half)
  have hlt := add_lt_add_left (Fraction.half_lt eps heps)
    (Fraction.add R S)
  exact lt_equiv_left (Fraction.equiv_trans he₁ he₂) hlt

theorem nameBound_triangle {a b c : EndpointCauchyName} {R S : Fraction}
    (hab : NameBound a b R) (hbc : NameBound b c S) :
    NameBound a c (Fraction.add R S) := by
  intro eps heps
  let q := eps.half.half
  obtain ⟨N₁, h₁⟩ := hab q heps
  obtain ⟨N₂, h₂⟩ := hbc q heps
  refine ⟨N₁ + N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := by omega
  have hn₂ : N₂ ≤ n := by omega
  have htri := stateSub_triangle (a.approx n) (b.approx n) (c.approx n)
  have hsum := Fraction.add_le_add
    (Fraction.magnitudes.lt_implies_le (h₁ n hn₁))
    (Fraction.magnitudes.lt_implies_le (h₂ n hn₂))
  exact Fraction.magnitudes.lt_of_le_lt
    (Fraction.magnitudes.le_trans htri hsum)
    (two_quarters_lt R S eps heps)

theorem within_triangle (x y z : Value) (R S : Fraction)
    (hxy : Within x y R) (hyz : Within y z S) :
    Within x z (Fraction.add R S) := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      induction z using Quotient.inductionOn with
      | _ c => exact nameBound_triangle hxy hyz

private theorem lt_self_add_positive (R eps : Fraction)
    (heps : 0 < eps.num) : Fraction.lt R (Fraction.add R eps) := by
  have h := add_lt_add_left (zero_lt_positive eps heps) R
  have he : Fraction.equiv (Fraction.add R (Fraction.ofInt 0)) R := by
    simp only [Fraction.equiv, Fraction.add, Fraction.ofInt]
    simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
      Int.mul_one, Int.one_mul]
  exact lt_equiv_left (Fraction.equiv_symm he) h

theorem nameBound_of_eventual_le (a b : EndpointCauchyName) (R : Fraction)
    (N : Nat) (h : ∀ n : Nat, N ≤ n →
      Fraction.le (distance (a.approx n) (b.approx n)) R) :
    NameBound a b R := by
  intro eps heps
  refine ⟨N, ?_⟩
  intro n hn
  exact Fraction.magnitudes.lt_of_le_lt (h n hn)
    (lt_self_add_positive R eps heps)

theorem constant_approximants_converge (a : EndpointCauchyName)
    (eps : Fraction) (heps : 0 < eps.num) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m →
      Within (embed (a.approx m)) (realize a) eps := by
  obtain ⟨N, hN⟩ := a.cauchy eps.half heps
  refine ⟨N, ?_⟩
  intro m hm
  intro delta hdelta
  refine ⟨N, ?_⟩
  intro n hn
  have hsmall : Fraction.lt eps.half (Fraction.add eps delta) :=
    Fraction.magnitudes.lt_of_lt_le (Fraction.half_lt eps heps)
      (Fraction.magnitudes.lt_implies_le
        (lt_self_add_positive eps delta hdelta))
  exact Fraction.magnitudes.lt_of_lt_le (hN m n hm hn)
    (Fraction.magnitudes.lt_implies_le hsmall)

theorem nameBound_zero_iff (a b : EndpointCauchyName) :
    NameBound a b (Fraction.ofInt 0) ↔ NameEquiv a b := by
  constructor
  · intro h eps heps
    obtain ⟨N, hN⟩ := h eps heps
    refine ⟨N, ?_⟩
    intro n hn
    have he : Fraction.equiv (Fraction.add (Fraction.ofInt 0) eps) eps := by
      simp only [Fraction.equiv, Fraction.add, Fraction.ofInt]
      simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
        Int.mul_one, Int.one_mul, Int.zero_add]
    exact lt_equiv_right (hN n hn) he
  · intro h eps heps
    obtain ⟨N, hN⟩ := h eps heps
    refine ⟨N, ?_⟩
    intro n hn
    have he : Fraction.equiv eps (Fraction.add (Fraction.ofInt 0) eps) := by
      simp only [Fraction.equiv, Fraction.add, Fraction.ofInt]
      simp only [Int.zero_mul, Int.mul_zero, Int.add_zero,
        Int.mul_one, Int.one_mul, Int.zero_add]
    exact lt_equiv_right (hN n hn) he

theorem within_zero_iff (x y : Value) :
    Within x y (Fraction.ofInt 0) ↔ x = y := by
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      exact Iff.trans (nameBound_zero_iff a b)
        ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

theorem le_add_cancel_left (z a b : Fraction)
    (h : Fraction.le (Fraction.add z a) (Fraction.add z b)) :
    Fraction.le a b := Fraction.le_add_cancel_left z a b h

end NewtonLimitDynamics.Polygon.CauchyValues
