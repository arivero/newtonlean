import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
import Lean

/-! Controls for area-independent whole-figure coincidence. Generic tests
use the entire supplied ordered field. Concrete tests cover degenerate cells,
zero heights, falling joins and interior ordinate contacts; a nonclosed
predicate falsifies exact ultimate equality without the separation premise.
Compiled traversal checks the two edition-local chains and rejects modern
or foreign-witness dependencies. These controls share the Lean kernel and
core arithmetic; they do not establish the remaining affine/source scope. -/

namespace CorollaryWholeFigureControls
open NewtonLimitDynamics.Polygon.CurvilinearCoincidence Lean Elab Command

section Generic
open Lean.Grind Std
variable {K : Type} [Field K] [LE K] [LT K] [IsLinearOrder K]
  [LawfulOrderLT K] [OrderedRing K]

-- An actual zero-width family over ANY coordinate field, with arbitrary
-- supplied height. The whole vertical figure, including its sides, survives.
private def collapsed (a : K) : Partition a a where
  count := 1
  positive_count := by decide
  nodes := fun _ => a
  first := rfl
  last := rfl
  ordered := fun _ _ => Std.le_refl _

example (a H : K) (hH : 0≤H) :
    WholeCoincidence (fun _ => H) a a (fun _ => collapsed a) (fun _ _ => H) := by
  apply Principia1687.LemmaIII.corollary1_whole_figure_coincidence
    (fun _ => H) a a (fun _ => collapsed a) (fun _ _ => H) (fun _ => 0)
  · exact fun _ _ _ => hH
  · intro eps heps
    exact ⟨eps,heps,fun _ _ _ _ _ _ _ _ => by grind only⟩
  · intro eps heps
    exact ⟨0,fun _ _ => heps⟩
  · intro k i hi
    change a-a≤0
    grind only
  · intro k i hi
    exact ⟨a,a,Std.le_refl _,Std.le_refl _,Std.le_refl _,Std.le_refl _,
      Or.inl ⟨Std.le_refl _,Std.le_refl _⟩⟩

example (a : K) :
    WholeCoincidence (fun _ => 0) a a (fun _ => collapsed a) (fun _ _ => 0) := by
  apply Principia1713.LemmaIII.corollary1_whole_figure_coincidence
    (fun _ => 0) a a (fun _ => collapsed a) (fun _ _ => 0) (fun _ => 0)
  · intro t ha hb
    exact Std.le_refl _
  · intro eps heps
    exact ⟨eps,heps,fun _ _ _ _ _ _ _ _ => by grind only⟩
  · intro eps heps
    exact ⟨0,fun _ _ => heps⟩
  · intro k i hi
    change a-a≤0
    grind only
  · intro k i hi
    exact ⟨a,a,Std.le_refl _,Std.le_refl _,Std.le_refl _,Std.le_refl _,
      Or.inl ⟨Std.le_refl _,Std.le_refl _⟩⟩
end Generic

private def repeated : Partition (0 : Rat) 1 where
  count := 3
  positive_count := by decide
  nodes := fun i => if i=0 then 0 else if i≤2 then 1/2 else 1
  first := rfl
  last := by decide +kernel
  ordered := by
    intro i hi
    by_cases h0 : i=0
    · subst i; decide +kernel
    · by_cases h1 : i=1
      · subst i; decide +kernel
      · have : i=2 := by omega
        subst i
        decide +kernel

private def heights (i : Nat) : Rat := if i=1 then 2 else 1

example : Perimeter repeated heights (0,0) := Or.inl ⟨by decide,by decide,rfl⟩
example : Perimeter repeated heights (1,1/2) :=
  Or.inr (Or.inr (Or.inl ⟨rfl,by decide +kernel,by decide +kernel⟩))
example : Perimeter repeated heights (1/2,3/2) := by
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨1,by decide,by decide +kernel,?_⟩)))
  exact Or.inr ⟨by decide +kernel,by decide +kernel⟩
example : Rectangles repeated heights (1/2,3/2) :=
  perimeter_in_rectangles repeated heights
    (by intro i hi; dsimp only [heights]; split <;> decide) _
    (by exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨1,by decide,by decide +kernel,Or.inr ⟨by decide +kernel,by decide +kernel⟩⟩))))

-- At a valley minimum an inscribed height need not lie between endpoint
-- ordinates. CellHeight admits contact anywhere inside its own cell.
private def coarse : Partition (0 : Rat) 1 where
  count := 1
  positive_count := by decide
  nodes := fun i => if i=0 then 0 else 1
  first := rfl
  last := rfl
  ordered := by
    intro i hi
    have : i=0 := by omega
    subst i
    decide +kernel
private def valley (t : Rat) : Rat := (t-1/2).abs
example : CellHeight valley coarse 0 0 :=
  ⟨1/2,1/2,by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    Or.inl ⟨by decide +kernel,by decide +kernel⟩⟩
example : ¬ Between (valley (coarse.nodes 0)) 0 (valley (coarse.nodes 1)) := by
  unfold Between
  decide +kernel

-- Positive fixed width is not a shrinking mesh.
example : ¬ Shrinks (fun _ : Nat => (1 : Rat)) := by
  intro h
  obtain ⟨N,hN⟩ := h 1 (by decide)
  exact Rat.lt_irrefl (hN N (Nat.le_refl _))

private def openLine (x : Rat × Rat) : Prop := 0<x.1 ∧ x.1≤1 ∧ x.2=0
example : Approaches (fun _ => openLine) openLine := by
  intro eps heps
  exact ⟨0,fun _ _ => ⟨fun x hx => ⟨x,hx,by dsimp only [Near]; grind only⟩,
    fun x hx => ⟨x,hx,by dsimp only [Near]; grind only⟩⟩⟩
example : Ultimate (fun _ => openLine) (0,0) ∧ ¬ openLine (0,0) := by
  constructor
  · intro eps heps
    let t : Rat := if eps≤1 then eps/2 else 1/2
    have ht : 0<t ∧ t≤1 ∧ t<eps := by dsimp only [t]; split <;> grind
    exact ⟨0,fun _ _ => ⟨(t,0),⟨ht.1,ht.2.1,rfl⟩,by dsimp only [Near]; grind only⟩⟩
  · intro h
    exact Rat.lt_irrefl h.1

run_elab do
  let env ← getEnv
  for (edition,foreign) in #[(`Principia1687,"Principia1713."),(`Principia1713,"Principia1687.")] do
    let root := edition ++ `LemmaIII.corollary1_whole_figure_coincidence
    let mut todo := #[root]
    let mut used : NameSet := {}
    while !todo.isEmpty do
      let name := todo.back!
      todo := todo.pop
      unless used.contains name do
        used := used.insert name
        if let some info := env.find? name then
          todo := todo ++ info.type.getUsedConstants ++
            ((info.value? true).map Expr.getUsedConstants |>.getD #[])
    for dependency in #[edition ++ `LemmaIII.unequal_width_ordinate_control,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.partition_cover,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.heights_near,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.rectangles_approach_of_ordinate_control,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.figure_separated,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.perimeters_approach,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.boundary_separated,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.ultimate_eq_of_approaches,
        `NewtonLimitDynamics.Polygon.CurvilinearCoincidence.perimeter_in_rectangles] do
      unless used.contains dependency do throwError "{root} omits {dependency}"
    for dependency in used do
      let name := ((privateToUserName? dependency).getD dependency).toString
      if #[foreign,"DeMotu1684."].any (fun libraryPrefix => name.startsWith libraryPrefix) then
        throwError "{root} uses foreign witness {dependency}"
      if let some idx := env.getModuleIdxFor? dependency then
        if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
          throwError "{root} uses modern module through {dependency}"
  logInfo "Checked both whole-figure clients: own Lemma III ordinate control, complete finite edges, separation and exact ultimate membership; no foreign witness or modern module."

end CorollaryWholeFigureControls
