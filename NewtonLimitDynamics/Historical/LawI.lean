import BarrowLib.Polygon.ZeroForce

/-! Historical result: law_i.
Diplomatic TEI rendering follows orig spelling; whitespace is collapsed; additions, deletions, notes and unclear readings are retained; fw forme-work is omitted.
-/

/-! 1687. Inertia as an explicit mechanical premise. -/
/-! Witness: 1687.
Source: docs/m1/NATP00076.xml
SHA-256: fc2984820b61f64fdbf5efe1142ea8cf5458b75dd54fc6525f73ee705a8a9b1c
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par1
Anchor URLs: NATP00076.par1 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par1
Proof-step correspondence: `InertialMotion` represents uniform motion after the initial impulse with no further impressed force. It is supplied, not proved from geometry; rational elapsed time and a fixed body's calibrated velocity are an editorial interpretation (confidence high).
-/
/- LATIN BEGIN NATP00076.par1
Corpus omne perseverare in statu suo quiescendi vel movendi uniformiter in directum, nisi quatenus a viribus impressis cogitur statum illum mutare.
LATIN END NATP00076.par1 -/

namespace Principia1687.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision

/-- Law I's uniform rectilinear motion, supplied for an interval without
further impressed forces. This does not assert inertia during forcing. -/
def InertialMotion (motion : Point → Point → Fraction → Point) : Prop :=
  ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t)

end Principia1687.Laws

/-! 1713. Inertia as its own explicit mechanical premise. -/
/-! Witness: 1713.
Source: docs/m1/NATP00081.xml
SHA-256: 5c72c73d9f396d3b34475543fa7cd158ab29006fb43fa35bc63df9b7e4be6bfe
URL: https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par1
Anchor URLs: NATP00081.par1 = https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par1
Proof-step correspondence: `InertialMotion` represents uniform motion after the initial impulse with no further impressed force. It is supplied, not proved from geometry; rational elapsed time and a fixed body's calibrated velocity are an editorial interpretation (confidence high).
-/
/- LATIN BEGIN NATP00081.par1
Corpus omne perseverare in statu suo quiescendi vel movendi uniformiter in directum, nisi quatenus a viribus impressis cogitur statum illum mutare.
LATIN END NATP00081.par1 -/

namespace Principia1713.Laws
open NewtonLimitDynamics NewtonLimitDynamics.Polygon TimeSubdivision

/-- Edition-local premise for motion without further impressed force. -/
def InertialMotion (motion : Point → Point → Fraction → Point) : Prop :=
  ∀ p v t, pointEquiv (motion p v t) (ZeroForce.inertialAt p v t)

end Principia1713.Laws
