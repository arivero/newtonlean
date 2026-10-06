import Lake
open Lake DSL

package NewtonLimitDynamics where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib NewtonLimitDynamics

lean_lib BarrowLib

lean_lib ClassicsLib

lean_lib ModernLib
