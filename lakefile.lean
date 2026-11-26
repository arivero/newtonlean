import Lake
open Lake DSL

package NewtonLimitDynamics where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib NewtonLimitDynamics

lean_lib BarrowLib

lean_lib ClassicsLib

lean_lib ModernLib

/- Modern reverse programme (Reverse/README.md). Historical libraries never
import it; it meets them at the shared Newton interface. -/
@[default_target]
lean_lib Reverse

/- Verification modules (research/VERIFICATION.md, issue 6): frozen headline
statements and the rational-time certificate. They import the libraries and
no library imports them; they earn no completion credit. -/
@[default_target]
lean_lib Verification where
  roots := #[`research.FrozenStatements, `research.RationalTimeSlope]
