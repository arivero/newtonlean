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

/- Compiler-generated auxiliaries (matchers, lazily realized equation lemmas,
their private realizations) carry the parent declaration's name as a prefix
and depend only on that declaration and Lean core, so they are classified by
the parent's source position. A realized lemma is private-mangled even when
its parent is public, so both spellings are tried at every prefix. -/
private partial def sourceLine? (name : Name) : TermElabM (Option Nat) := do
  if let some ranges ← findDeclarationRanges? name then
    return some ranges.range.pos.line
  if let some userName := privateToUserName? name then
    if let some ranges ← findDeclarationRanges? userName then
      return some ranges.range.pos.line
  if name.isAnonymous then return none
  sourceLine? name.getPrefix

/- Definitions are traversed but not counted. Distinct source-declared project
theorems/axioms count once; the root proof and compiler-generated auxiliaries
do not count. Standard Lean infrastructure is outside the project score. -/
private partial def closure (rows : NameMap (Array Name))
    (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closure rows rest seen
    else match rows.find? name with
      | none => closure rows rest seen
      | some uses => closure rows (uses.toList ++ rest) (seen.insert name)

private def score (rows : NameMap (Array Name)) (proofs modern : NameSet)
    (name : Name) : Nat × Nat := Id.run do
  let used := closure rows ((rows.find? name).getD #[]).toList
  let mut m := 0
  let mut h := 0
  for dependency in used do
    if dependency != name && proofs.contains dependency then
      if modern.contains dependency then m := m + 1 else h := h + 1
  return (m, h)

private def scoreComment (m h : Nat) : String :=
  let value := if m+h == 0 then "0" else s!"{m}/{m+h}"
  s!"-- Modern dependency score: {value} (M={m}, H={h}; transitive project theorems/axioms)."

private def declaredProof (name : Name) (line : String) : Bool :=
  let userName := (privateToUserName? name).getD name |>.toString
  let words := line.splitOn " " |>.filter (! ·.isEmpty)
  let rec find : List String → Bool
    | kind :: token :: rest =>
      if kind == "theorem" || kind == "axiom" then
        userName == token || userName.endsWith ("." ++ token)
      else find (token :: rest)
    | _ => false
  find words

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

  let scoreRows : NameMap (Array Name) := ({} : NameMap (Array Name))
    |>.insert `Control.root #[`Control.bridge, `Control.old, `Control.old]
    |>.insert `Control.bridge #[modern, `Control.old]
    |>.insert modern #[] |>.insert `Control.old #[]
  let scoreProofs := ({} : NameSet).insert modern |>.insert `Control.old
  unless Verification.score scoreRows scoreProofs (({} : NameSet).insert modern)
      `Control.root == (1, 1) &&
      Verification.score scoreRows scoreProofs (({} : NameSet).insert modern)
        `Control.old == (0, 0) do
    throwError "proof-score controls failed: transitive modern use, duplicate use or empty proof"

  let env ← getEnv
  -- Known control: a private-mangled matcher equation lemma, as `simp`
  -- realizes it, classifies at its parent definition's source line.
  let parent := `Principia1687.PropositionI.polygonState
  let realized := mkPrivateName env (parent ++ `match_1 ++ `eq_2)
  let parentLine ← Verification.sourceLine? parent
  unless parentLine.isSome && (← Verification.sourceLine? realized) == parentLine do
    throwError "auxiliary-declaration classification control failed"
  let mut rows : Array (Name × Array Name) := #[]
  let mut seeds : NameSet := {}
  let mut primary : Array Name := #[]
  let mut headers : NameMap (Option Nat) := {}
  let mut inspected := 0
  let mut sources : NameMap (Array String) := {}
  let mut proofLocations : Array (Name × Name × Nat) := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let module := env.header.moduleNames[idx]!
      if Verification.projectModule module then
        inspected := inspected + 1
        rows := rows.push (name, Verification.dependencies info)
        if info matches .thmInfo _ | .axiomInfo _ then
          if let some ranges ← findDeclarationRangesCore? name then
            let lines ← match sources.find? module with
              | some lines => pure lines
              | none => do
                let lines := (← liftM (IO.FS.readFile
                  (module.toString.replace "." "/" ++ ".lean"))).splitOn "\n" |>.toArray
                sources := sources.insert module lines
                pure lines
            let line := ranges.selectionRange.pos.line
            if line > 0 && Verification.declaredProof name (lines[line-1]!.trim) then
              proofLocations := proofLocations.push (name, module, line-1)
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

  let mut graph : NameMap (Array Name) := {}
  for (name, uses) in rows do graph := graph.insert name uses
  let mut proofs : NameSet := {}
  let mut modernProofs : NameSet := {}
  for (name, _, _) in proofLocations do
    proofs := proofs.insert name
    if paths.contains name then modernProofs := modernProofs.insert name
  unless proofs.contains `NewtonLimitDynamics.Polygon.CauchyValues.position_bounded_tail &&
      proofs.contains `NewtonLimitDynamics.Polygon.CauchyValues.distance_self_lt &&
      proofLocations.any (fun (name, _, _) =>
        name.toString.endsWith ".equiv_zero_num" && (privateToUserName? name).isSome) do
    throwError "proof-score source controls failed: documented, ordinary or private theorem omitted"
  let writeScores := (← liftM (IO.getEnv "NEWTON_WRITE_PROOF_SCORES")) == some "1"
  let mut edits : NameMap (Array (Nat × String)) := {}
  let mut scored := 0
  for (name, module, line) in proofLocations do
    if modernProofs.contains name then
      scored := scored + 1
      let (m, h) := Verification.score graph proofs modernProofs name
      let expected := Verification.scoreComment m h
      let lines := (sources.find? module).getD #[]
      let current := if line > 0 then lines[line-1]! else ""
      if current != expected then
        if writeScores then
          edits := edits.insert module (((edits.find? module).getD #[]).push (line, expected))
        else
          throwError "missing/stale proof score for {name} at {module}:{line+1}; expected {expected}"
  for (module, changes) in edits.toList do
    let original := (sources.find? module).getD #[]
    let mut updated : Array String := #[]
    for i in [:original.size] do
      if let some (_, replacement) := changes.find? (fun (line, _) => line == i) then
        if i > 0 && original[i-1]!.startsWith "-- Modern dependency score:" then
          updated := updated.pop
        updated := updated.push replacement
      updated := updated.push original[i]!
    liftM (IO.FS.writeFile (module.toString.replace "." "/" ++ ".lean")
      (String.intercalate "\n" updated.toList))
  logInfo m!"{if writeScores then "Refreshed" else "Checked"} {scored} inline modern dependency scores. Prefer smaller M/(M+H); an empty dependency set scores 0. Scores describe repository classification, not verified historical source coverage."
  logInfo m!"Checked {inspected} compiled project constants: safe declarations use only standard Lean axioms; primary historical declarations have no anachronical dependency."
