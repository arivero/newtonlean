import NewtonLimitDynamics

namespace NewtonLimitDynamics.Polygon.IntervalControls
open NewtonLimitDynamics TimeSubdivision PolygonFanArea

private def p (x y : Int) : Point := (Fraction.ofInt x, Fraction.ofInt y)
private def cyclic : Nat → Point
  | 0 => p 1 0 | 1 => p 0 1 | 2 => p (-1) 0
  | 3 => p 0 (-1) | _ => p 1 0
private def backtrack : Nat → Point
  | 0 => p 1 0 | 1 => p 0 1 | _ => p 1 0

example : (unsignedFan cyclic 4).num = 4 := by decide
example : (unsignedFan (fun i => cyclic (i+1)) 2).num = 2 := by decide
example : (fan backtrack 2).num = 0 := by decide
example : (unsignedFan backtrack 2).num = 2 := by decide
example : ¬ Fraction.equiv (fan backtrack 2) (unsignedFan backtrack 2) := by decide
example : (unsignedFan cyclic 0).num = 0 := by decide

open CauchyValues BinaryTime HarmonicTimeRealization GeneralForceArea SweptArea

example (unsigned : Bool) (nodes : Nat → Value) (lo n k : Nat) :
    FanValues.intervalValue unsigned nodes lo (n+k) =
      FanValues.sumValue (FanValues.intervalValue unsigned nodes lo n)
        (FanValues.intervalValue unsigned nodes (lo+n) k) :=
  FanValues.intervalValue_compose unsigned nodes lo n k

variable (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
  (s : Point × Point) (hE : 0 < E0.num)
  (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)

example (b c : Nat → Bool) (m : Nat) :
    (GeneralForceArea.intervalName b c o E0 T tau L B s hE d).approx m =
      FanValues.halfState
        ((curveIntervalName o E0 T tau L B s hE d b c m).approx m) := rfl

example (t₀ t₁ : BinaryTime T d.time_nonnegative) :
    AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁
      (intervalAreaValue o E0 T tau L B s hE d t₀ t₁) :=
  interval_area_is_swept o E0 T tau L B s hE d t₀ t₁

example (t₀ t₁ : BinaryTime T d.time_nonnegative) (a : Value)
    (ha : AreaBetween T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t₀ t₁ a) :
    a = intervalAreaValue o E0 T tau L B s hE d t₀ t₁ :=
  areaBetween_unique _ _ _ _ _ _ _ ha
    (interval_area_is_swept o E0 T tau L B s hE d t₀ t₁)

example : intervalAreaValue o E0 T tau L B s hE d
    (Quotient.mk _ firstAlias) (Quotient.mk _ secondAlias) =
      embed FanValues.zeroState := by
  rw [alias_time_eq T d.time_nonnegative]
  exact interval_area_zero o E0 T tau L B s hE d _

example (hzero : T.num=0) (t₀ t₁ : BinaryTime T d.time_nonnegative) :
    intervalAreaValue o E0 T tau L B s hE d t₀ t₁ = embed FanValues.zeroState := by
  have ht : t₀=t₁ := by
    induction t₀ using Quotient.inductionOn with
    | _ b =>
      induction t₁ using Quotient.inductionOn with
      | _ c =>
        apply Quotient.sound
        apply nameEquiv_of_levelwise_stateEquiv
        intro j
        constructor
        · constructor
          · simp only [BinaryTime.timeName,timeState,timeApprox,scalarState,
              HarmonicDyadic.duration,Fraction.equiv,Fraction.mul,Fraction.ofInt,hzero,
              Int.mul_zero,Int.zero_mul]
          · exact Fraction.equiv_refl _
        · exact ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩
  rw [ht]
  exact interval_area_zero o E0 T tau L B s hE d _

#check constructed_interval_area_law
#check interval_area_time_formula
#check interval_areas_equal_of_equal_elapsed
#check interval_area_reverse
#check Principia1687.PropositionI.constructed_central_interval_area_law
#check Principia1713.PropositionI.constructed_central_interval_area_law
#check DeMotu1684.AreaLaw.natp00089_constructed_central_interval_area_law
#check DeMotu1684.AreaLaw.natp00090_constructed_central_interval_area_law
#print axioms constructed_interval_area_law
#print axioms interval_area_zero

end NewtonLimitDynamics.Polygon.IntervalControls
