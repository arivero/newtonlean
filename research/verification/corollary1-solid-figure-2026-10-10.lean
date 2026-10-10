import NewtonLimitDynamics.Historical.LemmaIII.CorollaryI
import Lean

/-! Graph-free filled-sum controls. A two-component figure has a vertical
gap and therefore is no global subgraph. Its actual finite inner and outer
unions, content assignments and gap dissections are constructed below.
Positive rectangles, outside separation and shrinking widths are proved.
An isolated point and a persistent outer spike falsify stronger conclusions.
These tests share Lean's kernel and core arithmetic with the implementation;
they do not turn the editorial solid-figure domain into a Newton quotation. -/

namespace CorollarySolidFigureControls
open NewtonLimitDynamics.Polygon.SolidFigureExhaustion
open NewtonLimitDynamics.Polygon.CurvilinearCoincidence
open Lean Elab Command

local instance (B : Box Rat) (x : Rat × Rat) : Decidable (B.region x) :=
  inferInstanceAs (Decidable (B.left≤x.1 ∧ x.1≤B.right ∧ B.bottom≤x.2 ∧ x.2≤B.top))
local instance (B : Box Rat) : Decidable B.positive :=
  inferInstanceAs (Decidable (B.left<B.right ∧ B.bottom<B.top))
local instance (B : Box Rat) : Decidable B.ordered :=
  inferInstanceAs (Decidable (B.left≤B.right ∧ B.bottom≤B.top))

private def lower : Box Rat := ⟨0,1,0,1⟩
private def upper : Box Rat := ⟨0,1,2,3⟩
private def figure (x : Rat × Rat) := lower.region x ∨ upper.region x
private def inner (m : Rat) (x : Rat × Rat) :=
  (Box.mk m 1 0 1).region x ∨ (Box.mk m 1 2 3).region x
private def lowerGap (m : Rat) : Box Rat := ⟨0,m,0,1⟩
private def upperGap (m : Rat) : Box Rat := ⟨0,m,2,3⟩

-- A fully concrete, positive shrinking width sequence over core Rat.
private def mesh (k : Nat) : Rat := 1/((k : Rat)+2)

private theorem mesh_bounds (k : Nat) : 0<mesh k ∧ mesh k<1 := by
  have hk := Rat.natCast_nonneg (a := k)
  have hd : 0<(k : Rat)+2 := by grind only
  dsimp only [mesh]
  constructor
  · simpa only [Rat.div_def,Rat.one_mul] using Rat.inv_pos.mpr hd
  · exact (Rat.div_lt_iff hd).mpr (by grind)

private theorem mesh_shrinks : Shrinks mesh := by
  intro eps heps
  let N := (1/eps).floor.toNat+1
  refine ⟨N,fun k hk => ?_⟩
  have hf := Rat.lt_floor_add_one (1/eps)
  have hn := Int.self_le_toNat (1/eps).floor
  have hi : (1/eps).floor+1≤(k : Int)+2 := by dsimp only [N] at hk; omega
  have hc := Rat.intCast_le_intCast.mpr hi
  have hk0 := Rat.natCast_nonneg (a := k)
  rw [Rat.intCast_add,Rat.intCast_add] at hc
  rw [Rat.intCast_add] at hf
  change (1/eps).floor+1≤(k : Rat)+2 at hc
  dsimp only [mesh]
  have hlarge : 1/eps<(k : Rat)+2 := Std.lt_of_lt_of_le hf hc
  have hmul := (Rat.div_lt_iff heps).mp hlarge
  exact (Rat.div_lt_iff (show 0<(k : Rat)+2 by grind only)).mpr (by grind only)

private theorem figure_solid : Solid figure :=
  solid_union lower.region upper.region (box_solid lower (by decide +kernel))
    (box_solid upper (by decide +kernel))

private theorem figure_separated : Separated figure :=
  separated_union lower.region upper.region (box_separated lower) (box_separated upper)

-- This figure has two filled bands with a gap in each vertical slice.
example : ¬ ∃ g : Rat → Rat, ∀ x, figure x ↔ Figure g 0 1 x := by
  rintro ⟨g,hg⟩
  have ht : figure (1/2,5/2) := Or.inr (by decide +kernel)
  have hm : ¬figure (1/2,3/2) := by unfold figure; decide +kernel
  have htop := (hg (1/2,5/2)).mp ht
  apply hm
  apply (hg (1/2,3/2)).mpr
  obtain ⟨ha,hb,hc,hd⟩ := htop
  exact ⟨ha,hb,by decide +kernel,by grind only⟩

private def dissection (m : Rat) (hm : 0≤m) (hm1 : m≤1) :
    GapDissection (inner m) figure m 2 where
  boxes := [lowerGap m,upperGap m]
  ordered := by
    intro B hB
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hB
    rcases hB with rfl | rfl <;> dsimp only [Box.ordered,lowerGap,upperGap] <;> grind only
  dissects := by
    refine ⟨⟨[m],[],?_⟩,⟨⟨[m],[],?_⟩,True.intro⟩⟩
    · intro x hx
      have he : x.1=m := by
        dsimp only [inner,lowerGap,Box.region] at hx
        grind only
      exact Or.inl (by simp only [List.mem_cons,List.not_mem_nil,or_false]; exact he)
    · intro x hx
      have he : x.1=m := by
        dsimp only [inner,lowerGap,upperGap,Box.region] at hx
        grind only
      exact Or.inl (by simp only [List.mem_cons,List.not_mem_nil,or_false]; exact he)
  union_eq := by
    intro x
    simp only [cover,List.mem_cons,List.not_mem_nil,or_false,
      or_and_right,exists_or,exists_eq_left]
    dsimp only [figure,inner,lower,upper,lowerGap,upperGap,Box.region]
    grind only
  mesh_nonnegative := hm
  width_bound := by
    intro B hB
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hB
    rcases hB with rfl | rfl <;> dsimp only [lowerGap,upperGap] <;> grind only
  height_bound := by
    change (1-0 : Rat)+(3-2+0)≤2
    decide +kernel

private theorem inner_content (area : ContentRules Rat) (m : Rat) (hm : m≤1) :
    area.HasContent (inner m) (2*(1-m)) := by
  have hl := area.rectangle (Box.mk m 1 0 1) ⟨hm,show (0 : Rat)≤1 from by decide⟩
  have hu := area.rectangle (Box.mk m 1 2 3) ⟨hm,show (2 : Rat)≤3 from by decide⟩
  have ht : Thin (fun x => (Box.mk m 1 0 1).region x ∧ (Box.mk m 1 2 3).region x) :=
    ⟨[],[],by intro x hx; dsimp only [Box.region] at hx; grind only⟩
  have h := area.union _ _ _ _ ht hl hu
  have he : (Box.mk m 1 0 1).value+(Box.mk m 1 2 3).value=2*(1-m) := by
    dsimp only [Box.value]; grind
  rw [he] at h
  exact h

-- Both historical clients apply to the original concrete family, using
-- finite geometry and source III's width estimate, with no graph premise.
example (area : ContentRules Rat) (x : Rat × Rat) :
    Ultimate (fun k => inner (mesh k)) x ↔ figure x := by
  apply Principia1687.LemmaIII.corollary1_solid_figure_coincidence area
    (fun k => inner (mesh k)) (fun _ => figure) figure
    (fun k => 2*(1-mesh k)) mesh 2 (by decide)
    (fun k => inner_content area (mesh k) (by have := mesh_bounds k; grind only))
    (fun k y hy => ?_) (fun _ _ h => h) figure_solid figure_separated
    (fun k => dissection (mesh k) (by have := mesh_bounds k; grind only)
      (by have := mesh_bounds k; grind only)) mesh_shrinks x
  have hm := mesh_bounds k
  dsimp only [inner,figure,lower,upper,Box.region] at hy ⊢
  grind only

example (area : ContentRules Rat) (x : Rat × Rat) :
    Ultimate (fun k => inner (mesh k)) x ↔ figure x := by
  apply Principia1713.LemmaIII.corollary1_solid_figure_coincidence area
    (fun k => inner (mesh k)) (fun _ => figure) figure
    (fun k => 2*(1-mesh k)) mesh 2 (by decide)
    (fun k => inner_content area (mesh k) (by have := mesh_bounds k; grind only))
    (fun k y hy => ?_) (fun _ _ h => h) figure_solid figure_separated
    (fun k => dissection (mesh k) (by have := mesh_bounds k; grind only)
      (by have := mesh_bounds k; grind only)) mesh_shrinks x
  have hm := mesh_bounds k
  dsimp only [inner,figure,lower,upper,Box.region] at hy ⊢
  grind only

-- A zero-area isolated point defeats exact inner coincidence if Solid is
-- omitted, despite enclosure, separation and a zero dissection gap.
private def pointBox : Box Rat := ⟨2,2,2,2⟩
private def hairFigure (x : Rat × Rat) := lower.region x ∨ pointBox.region x
private def hairDissection : GapDissection lower.region hairFigure 0 0 where
  boxes := [pointBox]
  ordered := by
    intro B hB
    obtain rfl := List.mem_singleton.mp hB
    decide +kernel
  dissects := by
    refine ⟨⟨[],[],?_⟩,True.intro⟩
    intro x hx
    dsimp only [lower,pointBox,Box.region] at hx
    grind only
  union_eq := by intro x; simp only [hairFigure,cover,List.mem_singleton,exists_eq_left]
  mesh_nonnegative := by decide
  width_bound := by
    intro B hB
    obtain rfl := List.mem_singleton.mp hB
    decide +kernel
  height_bound := by decide +kernel

example : Separated hairFigure := separated_union _ _ (box_separated lower) (box_separated pointBox)
example : (hairDissection.boxes.map Box.value).sum=0 := by decide +kernel
example : hairFigure (2,2) ∧ ¬Ultimate (fun _ => lower.region) (2,2) := by
  refine ⟨Or.inr (by decide +kernel),?_⟩
  intro h
  obtain ⟨N,hN⟩ := h (1/2) (by decide +kernel)
  obtain ⟨y,hy,hn⟩ := hN N (Nat.le_refl _)
  have hright := hy.2.1
  have hnear := hn.2.1
  change y.1≤1 at hright
  change 2-y.1<1/2 at hnear
  grind only

-- A vertical spike with width mesh k and height 1 has vanishing content,
-- but its fixed tip survives in the ultimate OUTER figure.
private def spike (m : Rat) : Box Rat := ⟨0,m,1,2⟩
private def spiked (m : Rat) (x : Rat × Rat) := lower.region x ∨ (spike m).region x
private def spikeDissection (k : Nat) : GapDissection lower.region (spiked (mesh k)) (mesh k) 1 where
  boxes := [spike (mesh k)]
  ordered := by
    intro B hB
    have : B=spike (mesh k) := by simpa only [List.mem_singleton] using hB
    subst B
    have hm := mesh_bounds k
    dsimp only [spike,Box.ordered]
    exact ⟨by grind only,by decide⟩
  dissects := by
    refine ⟨⟨[],[1],?_⟩,True.intro⟩
    intro x hx
    have he : x.2=1 := by dsimp only [lower,spike,Box.region] at hx; grind only
    exact Or.inr (by simpa only [List.mem_singleton] using he)
  union_eq := by intro x; simp only [spiked,cover,List.mem_singleton,exists_eq_left]
  mesh_nonnegative := by have := mesh_bounds k; grind only
  width_bound := by
    intro B hB
    have : B=spike (mesh k) := by simpa only [List.mem_singleton] using hB
    subst B
    dsimp only [spike]
    grind only
  height_bound := by
    change (2 : Rat)-1+0≤1
    decide +kernel

example : Shrinks (fun k => ((spikeDissection k).boxes.map Box.value).sum) :=
  dissection_gap_shrinks (fun _ => lower.region) (fun k => spiked (mesh k)) mesh 1
    (by decide) spikeDissection mesh_shrinks

example : Ultimate (fun k => spiked (mesh k)) (0,2) ∧ ¬lower.region (0,2) := by
  constructor
  · intro eps heps
    refine ⟨0,fun k _ => ⟨(0,2),Or.inr ?_,?_⟩⟩
    · have hm := mesh_bounds k
      dsimp only [spike,Box.region]
      grind only
    · dsimp only [Near]; grind only
  · decide +kernel

-- A shrinking central hole gives genuine finite boundaries with an
-- interior ultimate point. Filled-sum coincidence implies no boundary claim.
private def holeBox (k : Nat) : Box Rat :=
  ⟨1/2-mesh k/4,1/2+mesh k/4,1/2-mesh k/4,1/2+mesh k/4⟩
private def holed (k : Nat) (x : Rat × Rat) : Prop :=
  lower.region x ∧ (x.1≤1/2-mesh k/4 ∨ 1/2+mesh k/4≤x.1 ∨
    x.2≤1/2-mesh k/4 ∨ 1/2+mesh k/4≤x.2)
private def holeDissection (k : Nat) : GapDissection (holed k) lower.region (mesh k) 1 where
  boxes := [holeBox k]
  ordered := by
    intro B hB
    obtain rfl := List.mem_singleton.mp hB
    have hm := mesh_bounds k
    dsimp only [holeBox,Box.ordered]
    grind
  dissects := by
    refine ⟨⟨[1/2-mesh k/4,1/2+mesh k/4],[1/2-mesh k/4,1/2+mesh k/4],?_⟩,True.intro⟩
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    dsimp only [holed,holeBox,Box.region] at hx
    grind only
  union_eq := by
    intro x
    simp only [cover,List.mem_singleton,exists_eq_left]
    have hm := mesh_bounds k
    dsimp only [holed,holeBox,lower,Box.region]
    grind
  mesh_nonnegative := by have := mesh_bounds k; grind only
  width_bound := by
    intro B hB
    obtain rfl := List.mem_singleton.mp hB
    have hm := mesh_bounds k
    dsimp only [holeBox]
    grind
  height_bound := by
    have hm := mesh_bounds k
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    dsimp only [holeBox]
    grind

private def boundary (U : (Rat × Rat) → Prop) (x : Rat × Rat) : Prop :=
  ∀ eps, 0<eps → ∃ y z, U y ∧ ¬U z ∧ Near eps x y ∧ Near eps x z

private theorem hole_edge (k : Nat) : boundary (holed k) (1/2+mesh k/4,1/2) := by
  intro eps heps
  let t := if eps≤mesh k/4 then eps/2 else mesh k/8
  have hm := mesh_bounds k
  have ht : 0<t ∧ t<eps ∧ t<mesh k/4 := by dsimp only [t]; split <;> grind
  refine ⟨(1/2+mesh k/4,1/2),(1/2+mesh k/4-t,1/2),?_,?_,?_,?_⟩
  · dsimp only [holed,lower,Box.region]; grind
  · dsimp only [holed,lower,Box.region]; grind
  · dsimp only [Near]; grind only
  · dsimp only [Near]; grind only

example : Shrinks (fun k => ((holeDissection k).boxes.map Box.value).sum) :=
  dissection_gap_shrinks holed (fun _ => lower.region) mesh 1
    (by decide) holeDissection mesh_shrinks

example : Ultimate (fun k => boundary (holed k)) (1/2,1/2) ∧
    (∃ eps : Rat, 0<eps ∧ ∀ y, Near eps (1/2,1/2) y → lower.region y) := by
  constructor
  · intro eps heps
    obtain ⟨N,hN⟩ := mesh_shrinks eps heps
    refine ⟨N,fun k hk => ⟨(1/2+mesh k/4,1/2),hole_edge k,?_⟩⟩
    have hm := mesh_bounds k
    have hs := hN k hk
    dsimp only [Near]
    grind
  · refine ⟨1/4,by decide +kernel,?_⟩
    intro y hn
    dsimp only [Near] at hn
    dsimp only [lower,Box.region]
    grind only

run_elab do
  let env ← getEnv
  for (edition,foreign) in #[(`Principia1687,"Principia1713."),(`Principia1713,"Principia1687.")] do
    let root := edition ++ `LemmaIII.corollary1_solid_figure_coincidence
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
    for dependency in #[edition ++ `LemmaIII.unequal_width_dissection_gap,
        `NewtonLimitDynamics.Polygon.SolidFigureExhaustion.dissection_content,
        `NewtonLimitDynamics.Polygon.SolidFigureExhaustion.dissection_gap_bound,
        `NewtonLimitDynamics.Polygon.SolidFigureExhaustion.dissection_gap_shrinks,
        `NewtonLimitDynamics.Polygon.SolidFigureExhaustion.enclosing_content,
        `NewtonLimitDynamics.Polygon.SolidFigureExhaustion.missed_rectangle_le_gap,
        `NewtonLimitDynamics.Polygon.SolidFigureExhaustion.ultimate_eq_of_content_gap] do
      unless used.contains dependency do throwError "{root} omits {dependency}"
    for dependency in used do
      let name := ((privateToUserName? dependency).getD dependency).toString
      if #[foreign,"DeMotu1684."].any (fun p => name.startsWith p) then
        throwError "{root} uses foreign witness {dependency}"
      if let some idx := env.getModuleIdxFor? dependency then
        if env.header.moduleNames[idx]!.toString.startsWith "ModernLib" then
          throwError "{root} uses modern module through {dependency}"
  logInfo "Checked both graph-free filled-sum clients: own III, finite dissection, derived content/gap and missed-rectangle comparison; no foreign witness or modern module."

end CorollarySolidFigureControls
