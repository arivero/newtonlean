import NewtonLimitDynamics
import Lean

/- Direct verification of the compiled libraries; run from the repository root
   with `lake env lean research/CheckReferences.lean`.
   No external catalog or generated reference list is used. Historical sections
   are classified by their actual source positions relative to the five-line
   ANACHRONICAL PROOFS header. This checks provenance, not Newton's unproved
   geometric or mechanical premises.
   NEWTON_PRINT_THEOREM_COUNTS=1 also prints README rows for source lines,
   declared theorems, actual theorem dependencies and the import closure.
   NEWTON_CHECK_README_COUNTS=1 checks those rows against README.md.
   Both modes reuse the compiled graph and source-declaration classification;
   neither writes a catalogue, ledger or generated data file. -/
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

/- Traverse all reachable project constants, including definitions and helpers.
The score below counts distinct source-declared theorems/axioms, excluding the
root proof and compiler auxiliaries. Lean infrastructure is outside the graph. -/
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

/-- Count distinct source-declared theorems in the selected set and scope.
Definitions and compiler auxiliaries are traversed but never counted. -/
private def theoremCount (owners : NameMap Name) (used : NameSet)
    (scope : Name → Bool) : Nat := Id.run do
  let mut count := 0
  for (name, module) in owners.toList do
    if used.contains name && scope module then count := count + 1
  return count

private def physicalLines (text : String) : Nat :=
  if text.isEmpty then 0
  else (text.splitOn "\n").length - (if text.endsWith "\n" then 1 else 0)

private def uniqueRow (lines : List String) (row : String) : Bool :=
  (lines.filter (· == row)).length == 1

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

  -- Count a shared transitive dependency once, exclude same-scope roots,
  -- and omit definition nodes and unreachable source theorems.
  let countOwners : NameMap Name := ({} : NameMap Name)
    |>.insert `Control.root `Control.Host |>.insert `Control.old `Control.Host
    |>.insert modern `Control.Foreign |>.insert `Control.unused `Control.Foreign
  let countUsed := Verification.closure scoreRows [`Control.root]
  unless Verification.theoremCount countOwners countUsed (· == `Control.Host) == 2 &&
      Verification.theoremCount countOwners countUsed (· != `Control.Host) == 1 &&
      Verification.theoremCount countOwners
        (Verification.closure scoreRows [`Control.bridge]) (· != `Control.Host) == 1 &&
      Verification.theoremCount countOwners {} (fun _ => true) == 0 &&
      Verification.physicalLines "" == 0 &&
      Verification.physicalLines "one\ntwo\n" == 2 &&
      Verification.physicalLines "one\ntwo" == 2 &&
      Verification.uniqueRow ["| file | 2 | 1 | 3 | 4 |"] "| file | 2 | 1 | 3 | 4 |" &&
      !Verification.uniqueRow ["| file | 2 | 1 | 3 | 4 |"] "| file | 2 | 1 | 3 | 5 |" &&
      !Verification.uniqueRow ["row", "row"] "row" do
    throwError "README count controls failed: shared dependencies, scope, empty set or physical lines"

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

  let printCounts := (← liftM (IO.getEnv "NEWTON_PRINT_THEOREM_COUNTS")) == some "1"
  let checkCounts := (← liftM (IO.getEnv "NEWTON_CHECK_README_COUNTS")) == some "1"
  if printCounts || checkCounts then
    let mut owners : NameMap Name := {}
    let mut theoremNames : NameSet := {}
    for (name, module, _) in proofLocations do
      if let some (.thmInfo _) := env.find? name then
        owners := owners.insert name module
        theoremNames := theoremNames.insert name
    let mut moduleConstants : NameMap (Array Name) := {}
    for (name, _) in rows do
      if let some idx := env.getModuleIdxFor? name then
        let module := env.header.moduleNames[idx]!
        moduleConstants := moduleConstants.insert module
          (((moduleConstants.find? module).getD #[]).push name)
    let mut moduleImports : NameMap (Array Name) := {}
    for i in [:env.header.moduleNames.size] do
      let module := env.header.moduleNames[i]!
      if Verification.projectModule module then
        moduleImports := moduleImports.insert module
          (env.header.moduleData[i]!.imports.map (·.module)
            |>.filter Verification.projectModule)
    unless owners.find? `Principia1687.LemmaI.given_time_exhaustion ==
          some `NewtonLimitDynamics.Historical.LemmaI &&
        owners.find? `Principia1713.LemmaI.finite_time_before_end_exhaustion ==
          some `NewtonLimitDynamics.Historical.LemmaI do
      throwError "README source controls failed: known declarations not classified"
    let mut report : Array String := #[]
    let historical := env.header.moduleNames.filter
      (fun module => module.toString.startsWith "NewtonLimitDynamics.Historical.")
      |>.qsort (fun a b => a.toString < b.toString)
    for module in historical do
      let path := module.toString.replace "." "/" ++ ".lean"
      let label := (module.toString.replace "NewtonLimitDynamics.Historical." ""
        |>.replace "." "/") ++ ".lean"
      let lines := Verification.physicalLines (← liftM (IO.FS.readFile path))
      let own := Verification.theoremCount owners theoremNames (· == module)
      let used := Verification.closure graph ((moduleConstants.find? module).getD #[]).toList
      let dependencies := Verification.theoremCount owners used (· != module)
      let imported := Verification.closure moduleImports [module]
      let importCount := Verification.theoremCount owners theoremNames
        (fun owner => owner != module && imported.contains owner)
      report := report.push s!"| [{label}]({path}) | {lines} | {own} | {own + dependencies} | {own + importCount} |"
    for library in #["ClassicsLib", "BarrowLib", "ModernLib"] do
      let scope := fun module : Name => module.toString == library ||
        module.toString.startsWith (library ++ ".")
      let modules := env.header.moduleNames.filter scope
      let mut roots : Array Name := #[]
      let mut lines := 0
      for module in modules do
        roots := roots ++ (moduleConstants.find? module).getD #[]
        lines := lines + Verification.physicalLines
          (← liftM (IO.FS.readFile (module.toString.replace "." "/" ++ ".lean")))
      let own := Verification.theoremCount owners theoremNames scope
      let dependencies := Verification.theoremCount owners
        (Verification.closure graph roots.toList) (fun module => !scope module)
      let imported := Verification.closure moduleImports modules.toList
      let importCount := Verification.theoremCount owners theoremNames
        (fun module => !scope module && imported.contains module)
      report := report.push s!"| [{library}]({library}.lean) | {lines} | {own} | {own + dependencies} | {own + importCount} |"
    if checkCounts then
      let readme := (← liftM (IO.FS.readFile "README.md")).splitOn "\n"
      for row in report do
        unless Verification.uniqueRow readme row do
          throwError "README count row missing/stale/duplicated; expected exactly once:\n{row}"
      logInfo m!"Checked README measurements for {historical.size} historical files and 3 supporting libraries."
    if printCounts then
      logInfo m!"{String.intercalate "\n" report.toList}"
