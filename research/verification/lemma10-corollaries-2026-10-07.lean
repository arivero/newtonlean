import NewtonLimitDynamics

/-! Controls for Lemma X Corollaries 1–5, 7 October 2026. The supplied Lemma X
premises are satisfiable for the exact quadratic space `c t²` and for the space
`c t² + t³`, whose normalized ratio `c + t` only tends to `c`. Corollaries 1–2
of both editions and 1713 Corollaries 3–5 are instantiated on them. A negative
control takes a space with coefficient `2`, which differs from `k * f = 1` for
`k = 1` and `f = 1`: divided by the force it is ultimately `2`, so the value
`k = 1` fails, and Corollary 2's conclusion depends on the coefficient premise. -/

namespace NewtonLimitDynamics.LemmaXControls
open NewtonLimitDynamics NewtonLimitDynamics.Fraction

theorem ultimate_const (c : Fraction) : Ultimate magnitudes (fun _ => c) c :=
  fun _ _ hac hcb => ⟨ofInt 1, (show (0 : Int) < 1 by decide), fun _ _ _ => ⟨hac, hcb⟩⟩

def quadratic (c : Fraction) : Fraction → Fraction := fun t => mul c (mul t t)
def cubic (c : Fraction) : Fraction → Fraction :=
  fun t => add (mul c (mul t t)) (mul t (mul t t))

theorem cubic_ratio (c t : Fraction) (ht : positive t) :
    equiv (ratio (cubic c) t) (add c t) := by
  simp only [ratio, dif_pos ht, cubic, deflectionRatio, add, mul, equiv,
    Int.add_mul, Int.mul_add] <;> ac_nf <;> omega

theorem cubic_upper (c : Fraction) : Ultimate magnitudes (fun t => add c t) c := by
  intro a b hac hcb
  refine ⟨add b ⟨-c.num, c.den, c.den_pos⟩, ?_, ?_⟩
  · change lt c b at hcb
    change 0 < b.num * c.den + -c.num * b.den
    unfold lt at hcb
    rw [Int.neg_mul]
    omega
  · intro h hh hhd
    refine ⟨magnitudes.lt_of_lt_le hac (le_add_nonnegative c h (Int.le_of_lt hh)), ?_⟩
    change lt h (add b ⟨-c.num, c.den, c.den_pos⟩) at hhd
    change lt (add c h) b
    unfold lt add at *
    dsimp only at *
    simp only [Int.add_mul, Int.mul_add, Int.neg_mul] at *
    ac_nf at *
    omega

/-- Lemma X premises for the exact quadratic space. -/
def quadraticPremises (c : Fraction) :
    Principia1687.LemmaXPremises magnitudes (ratio (quadratic c)) c where
  areaRatio := ratio (quadratic c)
  lowerTriangle := fun _ => c
  upperTriangle := fun _ => c
  velocity_area := fun _ => rfl
  lower_limit := ultimate_const c
  upper_limit := ultimate_const c
  enclosure := ⟨ofInt 1, (show (0 : Int) < 1 by decide), fun h hh _ => by
    have hh' : positive h := hh
    have he : equiv (ratio (quadratic c) h) c := by
      simp only [ratio, dif_pos hh', quadratic]; exact square_ratio c h hh'
    exact ⟨le_of_equiv (equiv_symm he), le_of_equiv he⟩⟩

/-- Lemma X premises for the perturbed space, with triangles `c` and `c + t`. -/
def cubicPremises (c : Fraction) :
    Principia1687.LemmaXPremises magnitudes (ratio (cubic c)) c where
  areaRatio := ratio (cubic c)
  lowerTriangle := fun _ => c
  upperTriangle := fun t => add c t
  velocity_area := fun _ => rfl
  lower_limit := ultimate_const c
  upper_limit := cubic_upper c
  enclosure := ⟨ofInt 1, (show (0 : Int) < 1 by decide), fun h hh _ =>
    ⟨le_equiv_right (le_add_nonnegative c h (Int.le_of_lt hh))
        (equiv_symm (cubic_ratio c h hh)),
      le_of_equiv (cubic_ratio c h hh)⟩⟩

private def k : Fraction := ⟨1, 2, by decide⟩
private def f₁ : Fraction := ofInt 2
private def f₂ : Fraction := ofInt 3
private def r : Fraction := ofInt 2
private theorem hf₁ : positive f₁ := by decide
private theorem hf₂ : positive f₂ := by decide
private theorem hk : positive k := by decide
private theorem hr : positive r := by decide

-- Corollary 1: an exact and a perturbed error under equal forces.
example := Principia1687.LemmaX.corollary1_errors_as_squares_of_times
  (cubic (ofInt 3)) (quadratic (ofInt 3)) (ofInt 3) r (by decide) hr
  (cubicPremises (ofInt 3)) (quadraticPremises (ofInt 3))
example := Principia1713.LemmaX.corollary1_errors_as_squares_of_times
  (quadratic (ofInt 3)) (cubic (ofInt 3)) (ofInt 3) r (by decide) hr
  ⟨quadraticPremises (ofInt 3)⟩ ⟨cubicPremises (ofInt 3)⟩

-- Corollary 2: proportional forces 2 and 3 with calibration 1/2.
example := Principia1687.LemmaX.corollary2_errors_jointly
  (cubic (mul k f₁)) (quadratic (mul k f₂)) k f₁ f₂ r hk hf₁ hf₂ hr
  (cubicPremises (mul k f₁)) (quadraticPremises (mul k f₂))
example := Principia1713.LemmaX.corollary2_errors_jointly
  (cubic (mul k f₁)) (cubic (mul k f₂)) k f₁ f₂ r hk hf₁ hf₂ hr
  ⟨cubicPremises (mul k f₁)⟩ ⟨cubicPremises (mul k f₂)⟩

-- 1713 Corollaries 3 and 4 on the perturbed space.
example := Principia1713.LemmaX.corollary3_spaces_jointly
  (cubic (mul k f₂)) k f₂ hk hf₂ ⟨cubicPremises (mul k f₂)⟩
example := Principia1713.LemmaX.corollary4_from_corollary3
  (cubic (mul k f₂)) k f₂ hk hf₂ ⟨cubicPremises (mul k f₂)⟩
example := Principia1713.LemmaX.corollary5_from_corollary3
  (cubic (mul k f₂)) k f₂ hk hf₂ ⟨cubicPremises (mul k f₂)⟩

-- Coefficient 2 against k * f = 1: divided by the force 1 it is not ultimately 1.
example : ¬ Ultimate magnitudes
    (fun t => quotient (ratio (quadratic (mul (ofInt 1) (ofInt 2))) t) (ofInt 1)
      (show (0 : Int) < 1 by decide)) (ofInt 1) := by
  intro hU
  obtain ⟨d, hd, hp⟩ := hU (ofInt 0) ⟨3, 2, by decide⟩
    (by change lt _ _; unfold lt; decide) (by change lt _ _; unfold lt; decide)
  obtain ⟨h, hh, hhd⟩ := magnitudes.shrink d hd
  have hh' : positive h := hh
  have hx : equiv (quotient (ratio (quadratic (mul (ofInt 1) (ofInt 2))) h) (ofInt 1)
      (show (0 : Int) < 1 by decide)) (ofInt 2) := by
    simp only [ratio, dif_pos hh', quadratic, deflectionRatio, quotient, mul, ofInt, equiv] <;>
      ac_nf <;> omega
  have hlt := magnitudes.lt_of_le_lt (le_of_equiv (equiv_symm hx)) (hp h hh hhd).2
  exact absurd hlt (by change ¬ lt _ _; unfold lt; decide)

end NewtonLimitDynamics.LemmaXControls
