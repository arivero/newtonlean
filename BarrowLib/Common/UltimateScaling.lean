import BarrowLib.Common.RationalMagnitudes

/-! Ultimate ratios under three elementary operations: replacing the ultimate
value by an equal magnitude, multiplying the varying ratio by a fixed positive
magnitude, and reading the vanishing time in a fixed positive proportion.
Division by a positive magnitude is multiplication by its reciprocal, which
swaps numerator and denominator.

Source of these statements and derivations: the original English statements
and Lean proofs below, using the named finite library results. This records
project formalization authorship, not discovery or priority. No post-Principia
theorem or completion is used.

Temporary migration boundary: RatUltimateScaling proves the corresponding
Rat API directly. Retain this legacy API until its historical callers migrate
together. Arbitrary Fraction → Fraction functions may distinguish equivalent
representatives; normalized sampling is not a bidirectional Ultimate bridge.
-/
namespace NewtonLimitDynamics.Fraction

/-- The reciprocal of a positive magnitude. -/
def recip (m : Fraction) (hm : positive m) : Fraction := ⟨m.den, m.num, hm⟩

theorem positive_recip (m : Fraction) (hm : positive m) : positive (recip m hm) := m.den_pos

theorem quotient_equiv_recip (a m : Fraction) (hm : positive m) :
    equiv (quotient a m hm) (mul (recip m hm) a) := by
  unfold equiv quotient mul recip
  dsimp only
  ac_rfl

/-- A lower bound for a positive multiple is the divided bound. -/
theorem lt_mul_iff (m : Fraction) (hm : positive m) (a x : Fraction) :
    lt a (mul m x) ↔ lt (mul (recip m hm) a) x := by
  unfold lt mul recip
  dsimp only
  rw [show a.num * (m.den * x.den) = m.den * a.num * x.den by ac_rfl,
    show m.num * x.num * a.den = x.num * (m.num * a.den) by ac_rfl]

/-- An upper bound for a positive multiple is the divided bound. -/
theorem mul_lt_iff (m : Fraction) (hm : positive m) (x b : Fraction) :
    lt (mul m x) b ↔ lt x (mul (recip m hm) b) := by
  unfold lt mul recip
  dsimp only
  rw [show m.num * x.num * b.den = x.num * (m.num * b.den) by ac_rfl,
    show b.num * (m.den * x.den) = m.den * b.num * x.den by ac_rfl]

/-- The ultimate value may be replaced by an equal magnitude. -/
theorem ultimate_target_congr {r : Fraction → Fraction} {c c' : Fraction}
    (hr : Ultimate magnitudes r c) (hc : equiv c c') : Ultimate magnitudes r c' := by
  intro a b hac hcb
  have hcc := (equiv_iff_mutual_le c c').mp hc
  exact hr a b (magnitudes.lt_of_lt_le hac hcc.2) (magnitudes.lt_of_le_lt hcc.1 hcb)

/-- A fixed positive multiple of a varying ratio has that multiple of its
ultimate value. -/
theorem ultimate_scale {r : Fraction → Fraction} {c : Fraction} (m : Fraction)
    (hm : positive m) (hr : Ultimate magnitudes r c) :
    Ultimate magnitudes (fun t => mul m (r t)) (mul m c) := by
  intro a b hac hcb
  obtain ⟨d, hd, hp⟩ := hr (mul (recip m hm) a) (mul (recip m hm) b)
    ((lt_mul_iff m hm a c).mp hac) ((mul_lt_iff m hm c b).mp hcb)
  exact ⟨d, hd, fun t ht htd => ⟨(lt_mul_iff m hm a (r t)).mpr (hp t ht htd).1,
    (mul_lt_iff m hm (r t) b).mpr (hp t ht htd).2⟩⟩

/-- Division of a varying ratio by a fixed positive magnitude. -/
theorem ultimate_quotient {r : Fraction → Fraction} {c : Fraction} (m : Fraction)
    (hm : positive m) (hr : Ultimate magnitudes r c) :
    Ultimate magnitudes (fun t => quotient (r t) m hm) (quotient c m hm) :=
  ultimate_target_congr
    (ultimate_congr _ (fun t => mul (recip m hm) (r t)) _
      (fun t _ => quotient_equiv_recip (r t) m hm) (ultimate_scale (recip m hm)
        (positive_recip m hm) hr))
    (equiv_symm (quotient_equiv_recip c m hm))

/-- Reading the vanishing time in a fixed positive proportion `q` keeps the
ultimate value: times below `d / q` give scaled times below `d`. -/
theorem ultimate_time_scale {r : Fraction → Fraction} {c : Fraction} (q : Fraction)
    (hq : positive q) (hr : Ultimate magnitudes r c) :
    Ultimate magnitudes (fun t => r (mul q t)) c := by
  intro a b hac hcb
  obtain ⟨d, hd, hp⟩ := hr a b hac hcb
  refine ⟨mul (recip q hq) d, positive_mul _ _ (positive_recip q hq) hd, ?_⟩
  intro t ht htd
  exact hp (mul q t) (positive_mul q t hq ht) ((mul_lt_iff q hq t d).mpr htd)

end NewtonLimitDynamics.Fraction
