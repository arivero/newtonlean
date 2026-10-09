import NewtonLimitDynamics
import Lean

/- Run with `lake env lean scripts/inspect_graphs.lean` from the repository root.
   The figures are views of current source comments and compiled declarations,
   not a source catalogue or a certificate of Newton's limiting arguments. -/
open Lean Elab Command Term

namespace InspectGraphs

private def projectModule (m : Name) : Bool :=
  #["BarrowLib", "ClassicsLib", "ModernLib", "NewtonLimitDynamics"].any fun root =>
    m.toString == root || m.toString.startsWith (root ++ ".")

private def historical (m : Name) : Bool :=
  m.toString.startsWith "NewtonLimitDynamics.Historical."

private def root (s : String) : String :=
  (s.splitOn ".").head!

private def path (m : Name) : String :=
  m.toString.replace "." "/" ++ ".lean"

private def short (m : Name) : String :=
  m.toString.replace "NewtonLimitDynamics.Historical." ""

private def ident (s : String) : String :=
  s.replace "." "_" |>.replace "-" "_" |>.replace "/" "_"

private structure Edge where
  source : String
  to : String
  passage : String
  witness : String
  url : String
  status : String
  confidence : String
  file : String
  line : Nat

private def field (s label : String) : Option String :=
  if s.startsWith label then some (s.drop label.length).toString else none

private def parseEdge (s file : String) (line : Nat) : Option Edge := do
  let parts := s.splitOn "; "
  if parts.length != 6 then none else do
    let ends ← field parts[0]! "- "
    let nodes := ends.splitOn " → "
    if nodes.length != 2 then none else do
      let status ← field parts[4]! "status "
      if !(#["explicit_dependency", "implicit_dependency", "modern_reconstruction",
             "editorial_interpretation"] : Array String).contains status then none else do
      return {
        source := nodes[0]!, to := nodes[1]!,
        passage := ← field parts[1]! "passage ",
        witness := ← field parts[2]! "witness ",
        url := ← field parts[3]! "URL ",
        status,
        confidence := (← field parts[5]! "confidence ").replace "." "",
        file, line
      }

private def stage (s : String) : String :=
  if s.startsWith "P1687." then "1687"
  else if s.startsWith "P1713." then "1713"
  else if s.startsWith "NATP00089." then "NATP00089"
  else if s.startsWith "NATP00090." then "NATP00090"
  else "other"

private def edgeGroup (e : Edge) : String :=
  if e.status == "editorial_interpretation" || stage e.source != stage e.to then
    "Editorial and cross-witness comparisons"
  else stage e.to

private def statusLabel (s : String) : String :=
  if s == "explicit_dependency" then "explicit"
  else if s == "implicit_dependency" then "implicit"
  else if s == "modern_reconstruction" then "modern"
  else "editorial"

private def addUnique {α : Type} [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

private def diagram (title : String) (edges : Array Edge) : String := Id.run do
  let mut out := s!"### {title}\n\n```mermaid\nflowchart LR\n"
  if edges.isEmpty then out := out ++ "  empty[No recorded edges]\n"
  for e in edges do
    out := out ++ s!"  {ident e.source}[\"{e.source}\"] -->|{statusLabel e.status}| {ident e.to}[\"{e.to}\"]\n"
  out := out ++ "```\n\n"
  for e in edges do
    out := out ++ s!"- {e.source} → {e.to}: [{e.passage}]({e.url}); " ++
      s!"{e.status}, confidence {e.confidence}; witness {e.witness}; " ++
      s!"[source](/home/codexssh/newtonlean/{e.file}:{e.line}).\n"
  return out ++ "\n"

private def moduleDiagram (title : String) (pairs : Array (String × String)) : String := Id.run do
  let mut out := s!"### {title}\n\n```mermaid\nflowchart LR\n"
  if pairs.isEmpty then out := out ++ "  empty[No cross-module uses]\n"
  for (a, b) in pairs do
    out := out ++ s!"  {ident a}[\"{a}\"] --> {ident b}[\"{b}\"]\n"
  return out ++ "```\n\n"

end InspectGraphs

run_elab do
  unless InspectGraphs.root "BarrowLib.Polygon.Finite" == "BarrowLib" &&
      InspectGraphs.root "ClassicsLib.Euclid.FiniteLattice" == "ClassicsLib" do
    throwError "dotted import-name control failed"
  let env ← getEnv
  let modules := env.header.moduleNames.filter InspectGraphs.projectModule
  let historical := modules.filter InspectGraphs.historical
  let mut edges : Array InspectGraphs.Edge := #[]
  let mut importPairs : Array (String × String) := #[]
  for m in modules do
    let file := InspectGraphs.path m
    let lines := (← liftM (IO.FS.readFile file)).splitOn "\n" |>.toArray
    for i in [:lines.size] do
      let s := lines[i]!.trim
      if InspectGraphs.historical m && s.startsWith "- " && (s.splitOn " → ").length == 2 then
        let some e := InspectGraphs.parseEdge s file (i + 1)
          | throwError "Malformed historical edge at {file}:{i + 1}"
        if InspectGraphs.stage e.source == "other" || InspectGraphs.stage e.to == "other" then
          throwError "Unclassified historical witness at {file}:{i + 1}"
        edges := edges.push e
      if s.startsWith "import " then
        let imported := (s.drop 7).trim.toString
        let importedRoot := InspectGraphs.root imported
        if #["BarrowLib", "ClassicsLib", "ModernLib", "NewtonLimitDynamics"].contains importedRoot &&
            InspectGraphs.root m.toString != importedRoot then
          importPairs := InspectGraphs.addUnique importPairs (InspectGraphs.root m.toString, importedRoot)
  let mut formalPairs : Array (String × String) := #[]
  let mut inspected := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      if InspectGraphs.historical owner then
        inspected := inspected + 1
        let uses := info.type.getUsedConstants ++
          ((info.value? true).map Expr.getUsedConstants |>.getD #[])
        for used in uses do
          if let some usedIdx := env.getModuleIdxFor? used then
            let dependency := env.header.moduleNames[usedIdx]!
            if InspectGraphs.historical dependency && owner != dependency then
              formalPairs := InspectGraphs.addUnique formalPairs
                (InspectGraphs.short dependency, InspectGraphs.short owner)
  let mut out := "# Current source and Lean dependency figures\n\n"
  out := out ++ "Generated by `lake env lean scripts/inspect_graphs.lean` from current historical Lean comments and the compiled environment. Arrows in the source diagrams point from a cited result to the result citing it. Edge status comes from the cited comment; it does not assert a completed formal proof.\n\n"
  out := out ++ "The current historical files record no dependency edges for NATP00089 itself, proposed 1694, or 1726. Those omissions are source-comment coverage limits, not claims about the witnesses.\n\n"
  for group in #["NATP00089", "NATP00090", "1687", "1713", "Editorial and cross-witness comparisons"] do
    out := out ++ InspectGraphs.diagram group (edges.filter fun e => InspectGraphs.edgeGroup e == group)
  out := out ++ "## Lean code relationships\n\n"
  out := out ++ "The following arrows are current file imports between project libraries (importer → imported library). They classify compilation reachability only.\n\n"
  out := out ++ InspectGraphs.moduleDiagram "Library imports" importPairs
  out := out ++ s!"The next arrows mean at least one compiled declaration in the target historical file **directly** uses a constant from the source historical file in its type or body. Private helpers are included. {inspected} compiled historical declarations were inspected; same-file and supporting-library uses are suppressed for readability. These direct formal uses are distinct from source-comment edges and from file imports.\n\n"
  out := out ++ InspectGraphs.moduleDiagram "Direct cross-file formal uses" formalPairs
  out := out ++ "No diagram certifies the full Proposition I–IV chain, the polygon-to-curve step, or a historical premise merely because a file or declaration is reachable. Read the named Lean statements and their supplied hypotheses for scope.\n"
  liftM (IO.FS.writeFile "research/figures.md" out)
  logInfo m!"Generated research/figures.md from {edges.size} source edges, {historical.size} historical files, {formalPairs.size} formal cross-file uses."
