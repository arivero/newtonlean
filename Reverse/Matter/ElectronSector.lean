import Reverse.KK.WeakSector

/-!
PHYSICAL STAGE:
  Charged leptons. Electromagnetic binding into atoms needs a stable,
  negatively charged, massive particle in addition to the nucleons; without
  it no neutral composite containing protons can form.
MATHEMATICAL CONTENT:
  The interface for one stable electron-like state of the electromagnetic
  sector: asymptotic, non-vacuum, positive mass, negative charge.
INPUT PARAMETERS:
  Electromagnetic coupling (nonzero), the electron mass.
OUTPUT PARAMETERS:
  The electron charge, consumed by the neutrality computation of composite
  bodies.
PROVED HERE:
  Nothing.
ASSUMED HERE:
  Existence and stability of the state. Equality of the charge magnitudes
  |q_e| = q_p is a separate statement and is not imposed. The electron mass
  originates in Yukawa data that must survive long enough before the weak
  interaction is removed; which data survive is a question for a later pass.
OPEN PROBLEMS USED:
  None.
NEXT REDUCTION:
  `Reverse/Matter/NeutralMatter.lean`.

STATUS: physical hypothesis.
-/

namespace Reverse.Matter
open Reverse.Parent Reverse.KK NewtonLimitDynamics

/-- A stable electron-like state of the electromagnetic sector. The sign
convention is the proton's: the electron charge is negative. -/
structure HasStableElectronLikeState (em : GaugeSector) where
  electron : em.Spectrum
  asymptotic : em.asymptotic electron
  nonvacuum : electron ≠ em.vacuum
  mass_positive : Fraction.positive (em.mass electron)
  charge : Scalar
  charge_negative : charge.num < 0

end Reverse.Matter
