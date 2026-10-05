import NewtonLimitDynamics

/-! Scope and compatibility checks for the constructed general curve area.
No new force instance is used; all central-force statements are quantified
over the existing regional construction data. -/
namespace ConstructedCentralAreaControls
open NewtonLimitDynamics Polygon
open TimeSubdivision CauchyValues HarmonicDyadic PositionValues

example (op : BinaryLift.Operation) (a b : EndpointCauchyName) (j : Nat) :
    (BinaryLift.name op a b).approx j = op.apply (a.approx j) (b.approx j) := rfl

example (q : Fraction) (a b : EndpointCauchyName) (j : Nat) :
    (SecantValues.secantName q a b).approx j =
      SecantValues.secantState q (a.approx j) (b.approx j) := rfl

example (f : PairingValues.Form) (a b : EndpointCauchyName) (j : Nat) :
    (PairingValues.pairingName f a b).approx j =
      PairingValues.pairingState f (a.approx j) (b.approx j) := rfl

example (gap budget : Fraction → Fraction) (hb : Vanishes budget)
    (hg : PathDefect.PolygonTrajectoryEnclosure gap budget) : Vanishes gap :=
  PathDefect.polygon_trajectory_defect_vanishes gap budget hb hg

private def z : Fraction := Fraction.ofInt 0
private def one : Fraction := Fraction.ofInt 1
private def alternating (n : Nat) : Point :=
  if n=1 then (z,one) else (one,z)

/-- Opposite triangle orientations cancel in signed area and remain in the
unsigned fan. This checks the distinction used by the geometric conclusion. -/
example : Fraction.equiv (PolygonFanArea.fan alternating 2) z ∧
    Fraction.equiv (PolygonFanArea.unsignedFan alternating 2) (Fraction.ofInt 2) := by
  constructor <;> unfold Fraction.equiv <;> decide

variable (o : ForceClasses.CentralOracle) (E0 T tau L B : Fraction)
  (s : Point × Point) (hE : 0 < E0.num)
  (d : GeneralForcePrefix.Conditions o E0 T tau L B s hE)

example : Vanishes (fun mesh => GeneralForcePathContent.D_meshValue o E0 T tau L B s hE d
    (RationalEnclosure.level mesh)) :=
  GeneralForcePathContent.polygon_trajectory_defect_vanishes o E0 T tau L B s hE d

example (t : BinaryTime.BinaryTime T d.time_nonnegative) (a : Value)
    (ha : SweptArea.AreaAt true T d.time_nonnegative
      (GeneralForceTime.gammaPosition o E0 T tau L B s hE d) t a) :
    a = GeneralForceArea.sectorAreaValue true o E0 T tau L B s hE d t :=
  SweptArea.area_unique _ _ _ _ _ _ _ ha
    (GeneralForceArea.sector_area_is_swept true o E0 T tau L B s hE d t)

#check GeneralForceArea.constructed_area_law
#check GeneralForceArea.sector_area_time_formula
#check GeneralForcePathContent.polygon_trajectory_enclosure
#check HarmonicPathContent.polygon_trajectory_enclosure
#check DeMotu1684.AreaLaw.natp00089_constructed_central_area_law
#check DeMotu1684.AreaLaw.natp00090_constructed_central_area_law
#check Principia1687.PropositionI.constructed_central_area_law
#check Principia1713.PropositionI.constructed_central_area_law
#print axioms GeneralForceArea.constructed_area_law
#print axioms SweptArea.area_unique

end ConstructedCentralAreaControls
