import NewtonLimitDynamics
import Lean

/- Direct verification of the compiled libraries; run from the repository root
   with `lake env lean research/CheckReferences.lean`.
   No external catalog or generated reference list is used. Historical sections
   are classified by their actual source positions relative to the five-line
   ANACHRONICAL PROOFS header. This checks provenance, not Newton's unproved
   geometric or mechanical premises. -/
open Lean Elab Command Term

namespace Verification

private def projectModule (module : Name) : Bool :=
  #["BarrowLib", "ClassicsLib", "ModernLib", "NewtonLimitDynamics"].any fun library =>
    module.toString == library || module.toString.startsWith (library ++ ".")

private def dependencies (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++
    ((info.value? true).map Expr.getUsedConstants |>.getD #[])

private def propagate (rows : Array (Name × Array Name)) (seeds : NameSet) :
    NameMap (Array Name) := Id.run do
  let mut paths : NameMap (Array Name) := {}
  for name in seeds do paths := paths.insert name #[name]
  let mut changed := true
  while changed do
    changed := false
    for (name, uses) in rows do
      unless paths.contains name do
        for dependency in uses do
          if let some path := paths.find? dependency then
            paths := paths.insert name (#[name] ++ path)
            changed := true
            break
  return paths

private partial def sourceLine? (name : Name) : TermElabM (Option Nat) := do
  if let some ranges ← findDeclarationRanges? name then
    return some ranges.range.pos.line
  if name.isAnonymous then return none
  sourceLine? name.getPrefix

end Verification

run_elab do
  -- Known controls: transitive/private bridge, type-only use, a dependency
  -- cycle, and an elementary declaration that must remain untainted.
  let modern := `Control.modern
  let tagged := `Control.tagged
  let controlSeeds : NameSet := ({} : NameSet).insert modern |>.insert tagged
  let control := Verification.propagate
    #[(`Control.bridge, #[tagged]), (`Control.downstream, #[`Control.bridge]),
      (`Control.typeOnly, #[modern]), (`Control.cycleA, #[`Control.cycleB]),
      (`Control.cycleB, #[`Control.cycleA, modern]), (`Control.elementary, #[])]
    controlSeeds
  unless (control.find? `Control.downstream) == some #[`Control.downstream, `Control.bridge, tagged]
      && control.contains `Control.typeOnly && control.contains `Control.cycleA
      && !control.contains `Control.elementary do
    throwError "dependency verification controls failed"

  let env ← getEnv
  let mut rows : Array (Name × Array Name) := #[]
  let mut seeds : NameSet := {}
  let mut primary : Array Name := #[]
  let mut headers : NameMap (Option Nat) := {}
  let mut inspected := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := env.header.moduleNames[idx]!
      if Verification.projectModule module then
        inspected := inspected + 1
        rows := rows.push (name, Verification.dependencies info)
        -- Compiler-generated unsafe implementations may carry local proof
        -- placeholders. They cannot be used by safe mathematical proofs.
        unless info.isUnsafe do
          for axiomName in ← collectAxioms name do
            unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
              throwError "{name} uses forbidden axiom {axiomName}"
        if module.toString.startsWith "ModernLib." then
          seeds := seeds.insert name
        if module.toString.startsWith "NewtonLimitDynamics.Historical." then
          let header ← match headers.find? module with
            | some value => pure value
            | none => do
              let path := module.toString.replace "." "/" ++ ".lean"
              let text ← liftM (IO.FS.readFile path)
              let lines := text.splitOn "\n" |>.toArray
              let mut found : Option Nat := none
              for i in [:lines.size] do
                if lines[i]!.trim == "ANACHRONICAL PROOFS" then
                  if found.isSome || i < 5 then throwError "invalid anachronical header in {path}"
                  for j in [i-5:i] do
                    let line := lines[j]!
                    unless line.length >= 20 && line.toList.all (· == '=') do
                      throwError "expected five full '=' lines in {path}"
                  found := some (i + 1)
              headers := headers.insert module found
              pure found
          let some line ← Verification.sourceLine? name
            | throwError "cannot classify historical declaration {name} from its source"
          if header.any (line > ·) then
            seeds := seeds.insert name
          else
            primary := primary.push name
  let paths := Verification.propagate rows seeds
  for name in primary do
    if let some path := paths.find? name then
      throwError "anachronical dependency in primary declaration {name}: {path}"
  logInfo m!"Checked {inspected} compiled project constants: safe declarations use only standard Lean axioms; primary historical declarations have no anachronical dependency."
