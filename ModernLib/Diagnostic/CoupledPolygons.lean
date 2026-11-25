/-!
Modern diagnostic layer (newtonlean issue 2).  Coupled impulse polygons for
bosonic `SU(2)` matrix mechanics: `n` colour vectors `xᵢ, pᵢ ∈ ℚ³` with common
mass `m`, coupling `κ = g²` and the quartic potential
`V = (κ/2) Σ_{i<j} |xᵢ × xⱼ|²`, whose force on `xᵢ` is the cubic polynomial
`Fᵢ = -κ Σⱼ (|xⱼ|² xᵢ - (xᵢ·xⱼ) xⱼ)`.  One cell drifts every vector for the
duration `h` with its momentum and then applies the impulse of the force at
the drifted configuration, as in the finite construction of Proposition I.
No limit is taken and no historical proof uses these theorems.

Checked here, for arbitrary rational data and arbitrary finite schedules of
unequal durations: pairwise torque cancellation; preservation of the Gauss-law
generator `G = Σᵢ xᵢ × pᵢ` by one cell and by every schedule; the vector
triangle sum `Σᵢ ½ xᵢ × yᵢ = (h/2m) G`; an exact two-vector example with
nonzero individual triangles that cancel; and the exact quartic scaling
`Φ_h ∘ D_s = D_s ∘ Φ_{sh}`, `G ∘ D_s = s³ G` for `D_s(x,p) = (s x, s² p)`.
The physical cases are `m > 0` and `s > 0`; the identities hold for all
rationals because core `Rat` sets `x / 0 = 0`.

Provenance.  The statements and their packaging follow the written derivation
"Newton polygons in Yang–Mills mechanics"
(https://alpoge-riemann-proof-seminar.al-rivero.chatgpt.site/comparisons),
recorded in issue 2; the Lean statements and proofs are new to this
repository and carry no priority claim.  The underlying facts are known:
torque cancellation is the rotation invariance of `V`; preservation of `G` by
the drift/impulse cell is the conservation of bilinear invariants of the form
`pᵀ D q` by the symplectic Euler method; the triangle sum is the many-vector form of the
equal-area polygon, whose planar one-centre case is
`NewtonLimitDynamics.Polygon.CentralSchedule`; and the scaling is mechanical
similarity for a potential homogeneous of degree four.  Exact sources for these
standard results remain to be supplied and verified.

Scope.  `gauss` is the Gauss-law generator of the matrix model, unrelated to
Gauss's theorem in research/GOALS.md.  `triangle` and `swept` are
configuration-space areas; phase-space action and any quantum action parameter
are separate quantities and are not formalized.  The finite identities give no
continuum identification; research/STATE.md records the remaining obligations.
-/

namespace NewtonLimitDynamics.Diagnostic.CoupledPolygons

/-- A rational vector in colour space `ℚ³`. -/
structure Vec3 where
  x : Rat
  y : Rat
  z : Rat
deriving DecidableEq

namespace Vec3

def zero : Vec3 := ⟨0, 0, 0⟩
def add (a b : Vec3) : Vec3 := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩
def smul (c : Rat) (a : Vec3) : Vec3 := ⟨c * a.x, c * a.y, c * a.z⟩
def dot (a b : Vec3) : Rat := a.x * b.x + a.y * b.y + a.z * b.z
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

end Vec3

open Vec3

/-- Unfold the vector operations and close the three component goals. -/
local macro "coupled_vec3_ring" : tactic =>
  `(tactic| (simp only [Vec3.add, Vec3.smul, Vec3.dot, Vec3.cross, Vec3.zero, Vec3.mk.injEq]; refine ⟨?_, ?_, ?_⟩ <;> grind))

/-- Sum of a list of vectors. -/
def vsum : List Vec3 → Vec3
  | [] => zero
  | a :: l => add a (vsum l)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem add_zero_right (a : Vec3) : add a zero = a := by
  cases a; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem smul_zero_vec (c : Rat) : smul c zero = zero := by
  coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem vsum_add {α : Type} (f g : α → Vec3) (l : List α) :
    vsum (l.map fun a => add (f a) (g a)) = add (vsum (l.map f)) (vsum (l.map g)) := by
  induction l with
  | nil => simp only [List.map_nil, vsum]; coupled_vec3_ring
  | cons a l ih =>
      simp only [List.map_cons, vsum, ih]
      generalize f a = u; generalize g a = v
      generalize vsum (l.map f) = U; generalize vsum (l.map g) = W
      cases u; cases v; cases U; cases W; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem vsum_smul {α : Type} (c : Rat) (f : α → Vec3) (l : List α) :
    vsum (l.map fun a => smul c (f a)) = smul c (vsum (l.map f)) := by
  induction l with
  | nil => simp only [List.map_nil, vsum]; coupled_vec3_ring
  | cons a l ih =>
      simp only [List.map_cons, vsum, ih]
      generalize f a = u; generalize vsum (l.map f) = U
      cases u; cases U; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem vsum_cross_left {α : Type} (b : Vec3) (f : α → Vec3) (l : List α) :
    vsum (l.map fun a => cross b (f a)) = cross b (vsum (l.map f)) := by
  induction l with
  | nil => simp only [List.map_nil, vsum]; coupled_vec3_ring
  | cons a l ih =>
      simp only [List.map_cons, vsum, ih]
      generalize f a = u; generalize vsum (l.map f) = U
      cases u; cases U; cases b; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem vsum_zero {α : Type} (l : List α) : vsum (l.map fun _ => zero) = zero := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, vsum, ih]; coupled_vec3_ring

/-- An antisymmetric double sum over a list vanishes. -/
-- Modern dependency score: 2/2 (M=2, H=0; transitive project theorems/axioms).
private theorem vsum_antisymm (f : Vec3 → Vec3 → Vec3)
    (h : ∀ a b, add (f a b) (f b a) = zero) (l : List Vec3) :
    vsum (l.map fun a => vsum (l.map (f a))) = zero := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have haa : f a a = zero := by
        have := h a a
        generalize f a a = u at this ⊢
        cases u
        simp only [Vec3.add, Vec3.zero, Vec3.mk.injEq] at this ⊢
        refine ⟨?_, ?_, ?_⟩ <;> grind
      have hcross : add (vsum (l.map (f a))) (vsum (l.map fun b => f b a)) = zero := by
        rw [← vsum_add]
        simp only [h]
        exact vsum_zero l
      have hsplit : vsum (l.map fun b => vsum ((a :: l).map (f b)))
          = add (vsum (l.map fun b => f b a)) (vsum (l.map fun b => vsum (l.map (f b)))) := by
        simp only [List.map_cons, vsum]
        exact vsum_add (fun b => f b a) (fun b => vsum (l.map (f b))) l
      simp only [List.map_cons, vsum] at hsplit ⊢
      rw [hsplit, ih, haa]
      generalize vsum (l.map (f a)) = P at hcross ⊢
      generalize vsum (l.map fun b => f b a) = R at hcross ⊢
      cases P; cases R
      simp only [Vec3.add, Vec3.zero, Vec3.mk.injEq] at hcross ⊢
      refine ⟨?_, ?_, ?_⟩ <;> grind

/-- The contribution of `xj` to the force on `xi`: `|xj|² xi - (xi·xj) xj`. -/
def pairTerm (xi xj : Vec3) : Vec3 := add (smul (dot xj xj) xi) (smul (-(dot xi xj)) xj)

/-- The quartic-potential force on `xi` in the configuration `xs`,
    `-κ Σⱼ pairTerm xi xj`.  The sum runs over the whole list because the
    self term vanishes (`pairTerm_self`). -/
def force (κ : Rat) (xs : List Vec3) (xi : Vec3) : Vec3 :=
  smul (-κ) (vsum (xs.map (pairTerm xi)))

/-- The self term of the force vanishes. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem pairTerm_self (a : Vec3) : pairTerm a a = Vec3.zero := by
  cases a; simp only [pairTerm]; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem cross_pairTerm_antisymm (a b : Vec3) :
    add (cross a (pairTerm a b)) (cross b (pairTerm b a)) = zero := by
  cases a; cases b; simp only [pairTerm]; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem cross_smul_right (c : Rat) (a b : Vec3) :
    cross a (smul c b) = smul c (cross a b) := by
  cases a; cases b; coupled_vec3_ring

/-- Pairwise torque cancellation: `Σᵢ xᵢ × Fᵢ(x) = 0`. -/
-- Modern dependency score: 8/8 (M=8, H=0; transitive project theorems/axioms).
theorem torque_zero (κ : Rat) (xs : List Vec3) :
    vsum (xs.map fun xi => Vec3.cross xi (force κ xs xi)) = Vec3.zero := by
  have h1 : (fun xi => cross xi (force κ xs xi))
      = fun xi => smul (-κ) (vsum (xs.map fun xj => cross xi (pairTerm xi xj))) := by
    funext xi
    simp only [force, cross_smul_right]
    rw [vsum_cross_left]
  rw [h1, vsum_smul,
    vsum_antisymm (fun a b => cross a (pairTerm a b)) cross_pairTerm_antisymm xs]
  exact smul_zero_vec _

/-- A configuration: one `(position, momentum)` pair per colour vector. -/
abbrev State := List (Vec3 × Vec3)

/-- The Gauss-law generator `G = Σᵢ xᵢ × pᵢ`. -/
def gauss (st : State) : Vec3 := vsum (st.map fun s => cross s.1 s.2)

/-- Inertial drift of one position for duration `h`: `x + (h/m) p`. -/
def driftPos (m h : Rat) (s : Vec3 × Vec3) : Vec3 := add s.1 (smul (h / m) s.2)

/-- One cell: drift every position, then apply the impulse of the force
    evaluated at the drifted configuration. -/
def cell (κ m h : Rat) (st : State) : State :=
  st.map fun s =>
    (driftPos m h s, add s.2 (smul h (force κ (st.map (driftPos m h)) (driftPos m h s))))

/-- A finite schedule of cells with the listed, possibly unequal, durations. -/
def schedule (κ m : Rat) : List Rat → State → State
  | [], st => st
  | h :: hs, st => schedule κ m hs (cell κ m h st)

/-- The drift preserves each `xᵢ × pᵢ`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem drift_cross (m h : Rat) (s : Vec3 × Vec3) :
    Vec3.cross (driftPos m h s) s.2 = Vec3.cross s.1 s.2 := by
  obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩ := s
  simp only [driftPos]; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem cross_add_smul (y p F : Vec3) (h : Rat) :
    cross y (add p (smul h F)) = add (cross y p) (smul h (cross y F)) := by
  cases y; cases p; cases F; coupled_vec3_ring

/-- One cell preserves the Gauss-law generator. -/
-- Modern dependency score: 12/12 (M=12, H=0; transitive project theorems/axioms).
theorem cell_gauss (κ m h : Rat) (st : State) : gauss (cell κ m h st) = gauss st := by
  simp only [gauss, cell, List.map_map, Function.comp_def, cross_add_smul]
  rw [vsum_add, vsum_smul]
  have ht := torque_zero κ (st.map (driftPos m h))
  simp only [List.map_map, Function.comp_def] at ht
  rw [ht, smul_zero_vec, add_zero_right]
  simp only [drift_cross]

/-- Every finite schedule preserves the Gauss-law generator. -/
-- Modern dependency score: 13/13 (M=13, H=0; transitive project theorems/axioms).
theorem schedule_gauss (κ m : Rat) : (hs : List Rat) → (st : State) →
    gauss (schedule κ m hs st) = gauss st
  | [], _ => rfl
  | h :: hs, st => (schedule_gauss κ m hs (cell κ m h st)).trans (cell_gauss κ m h st)

/-- The oriented configuration triangle `(0, xᵢ, yᵢ)` swept during the drift,
    as a vector area `½ xᵢ × yᵢ`. -/
def triangle (m h : Rat) (s : Vec3 × Vec3) : Vec3 := smul (1 / 2) (cross s.1 (driftPos m h s))

/-- The triangle sum: `Σᵢ ½ xᵢ × yᵢ = (h/2m) G`. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem triangle_sum (m h : Rat) (st : State) :
    vsum (st.map (triangle m h)) = Vec3.smul (h / (2 * m)) (gauss st) := by
  have : (triangle m h) = fun s => smul (h / (2 * m)) (cross s.1 s.2) := by
    funext s
    obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩ := s
    simp only [triangle, driftPos]; coupled_vec3_ring
  rw [this, vsum_smul]; rfl

/-- Total duration of a schedule. -/
def elapsed : List Rat → Rat
  | [] => 0
  | h :: hs => h + elapsed hs

/-- Total vector area of the drift triangles over a schedule. -/
def swept (κ m : Rat) : List Rat → State → Vec3
  | [], _ => zero
  | h :: hs, st => add (vsum (st.map (triangle m h))) (swept κ m hs (cell κ m h st))

/-- Swept vector area is proportional to elapsed time: `(T/2m) G`. -/
-- Modern dependency score: 14/14 (M=14, H=0; transitive project theorems/axioms).
theorem swept_eq (κ m : Rat) : (hs : List Rat) → (st : State) →
    swept κ m hs st = Vec3.smul (elapsed hs / (2 * m)) (gauss st)
  | [], st => by
      simp only [swept, elapsed]
      generalize gauss st = g; cases g; coupled_vec3_ring
  | h :: hs, st => by
      simp only [swept, elapsed, triangle_sum, swept_eq κ m hs (cell κ m h st), cell_gauss]
      generalize gauss st = g; generalize elapsed hs = T; cases g; coupled_vec3_ring

/-- The issue's example: `x₁ = e₁`, `x₂ = e₁ + e₂`, both momenta zero. -/
def exampleStart : State := [(⟨1, 0, 0⟩, zero), (⟨1, 1, 0⟩, zero)]

/-- After one cell the next drift has triangles `±(κh²/2m) e₃`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem example_areas (κ m h : Rat) :
    (cell κ m h exampleStart).map (triangle m h)
      = [⟨0, 0, κ * h * h / (2 * m)⟩, ⟨0, 0, -(κ * h * h / (2 * m))⟩] := by
  simp only [exampleStart, cell, triangle, driftPos, force, pairTerm, vsum, List.map_cons,
    List.map_nil, Vec3.add, Vec3.smul, Vec3.dot, Vec3.cross, Vec3.zero, List.cons.injEq,
    Vec3.mk.injEq, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> grind

/-- For `m = 3/2`, `κ = 9/4`, `h = 1/5` the triangles are `±(3/100) e₃`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem example_areas_numeric :
    (cell (9/4) (3/2) (1/5) exampleStart).map (triangle (3/2) (1/5))
      = [⟨0, 0, 3/100⟩, ⟨0, 0, -3/100⟩] := by
  simp only [exampleStart, cell, triangle, driftPos, force, pairTerm, vsum, List.map_cons,
    List.map_nil, Vec3.add, Vec3.smul, Vec3.dot, Vec3.cross, Vec3.zero, List.cons.injEq,
    Vec3.mk.injEq, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> grind

/-- The individual triangles are nonzero and cancel. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem example_nonzero_cancel :
    (⟨0, 0, 3/100⟩ : Vec3) ≠ Vec3.zero ∧
      Vec3.add ⟨0, 0, 3/100⟩ ⟨0, 0, -3/100⟩ = Vec3.zero := by
  refine ⟨?_, ?_⟩
  · simp only [Vec3.zero, ne_eq, Vec3.mk.injEq]; grind
  · coupled_vec3_ring

/-- The quartic dilation `D_s(x, p) = (s x, s² p)`. -/
def dilate (s : Rat) (st : State) : State := st.map fun z => (smul s z.1, smul (s * s) z.2)

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem pairTerm_scale (s : Rat) (a b : Vec3) :
    pairTerm (smul s a) (smul s b) = smul (s * s * s) (pairTerm a b) := by
  cases a; cases b; simp only [pairTerm]; coupled_vec3_ring

-- Modern dependency score: 2/2 (M=2, H=0; transitive project theorems/axioms).
private theorem force_scale (κ s : Rat) (xs : List Vec3) (xi : Vec3) :
    force κ (xs.map (smul s)) (smul s xi) = smul (s * s * s) (force κ xs xi) := by
  simp only [force, List.map_map, Function.comp_def, pairTerm_scale]
  rw [vsum_smul]
  generalize vsum (xs.map (pairTerm xi)) = U
  cases U; coupled_vec3_ring

-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
private theorem driftPos_scale (m h s : Rat) (z : Vec3 × Vec3) :
    driftPos m h (smul s z.1, smul (s * s) z.2) = smul s (driftPos m (s * h) z) := by
  obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩ := z
  simp only [driftPos]; coupled_vec3_ring

/-- Scaling conjugacy of one cell: `Φ_h ∘ D_s = D_s ∘ Φ_{sh}`. -/
-- Modern dependency score: 4/4 (M=4, H=0; transitive project theorems/axioms).
theorem cell_dilate (κ m h s : Rat) (st : State) :
    cell κ m h (dilate s st) = dilate s (cell κ m (s * h) st) := by
  simp only [cell, dilate, List.map_map, Function.comp_def, driftPos_scale]
  apply List.map_congr_left
  intro z _
  have hf := force_scale κ s (st.map (driftPos m (s * h))) (driftPos m (s * h) z)
  simp only [List.map_map, Function.comp_def] at hf
  rw [hf]
  refine Prod.ext rfl ?_
  generalize force κ (st.map (driftPos m (s * h))) (driftPos m (s * h) z) = F
  obtain ⟨z1, ⟨d, e, f⟩⟩ := z
  cases F; coupled_vec3_ring

/-- Scaling conjugacy of every finite schedule, with all durations scaled. -/
-- Modern dependency score: 5/5 (M=5, H=0; transitive project theorems/axioms).
theorem schedule_dilate (κ m s : Rat) : (hs : List Rat) → (st : State) →
    schedule κ m hs (dilate s st) = dilate s (schedule κ m (hs.map (s * ·)) st)
  | [], _ => rfl
  | h :: hs, st => by
      simp only [schedule, List.map_cons, cell_dilate]
      exact schedule_dilate κ m s hs (cell κ m (s * h) st)

/-- The Gauss-law generator has scaling weight three. -/
-- Modern dependency score: 1/1 (M=1, H=0; transitive project theorems/axioms).
theorem gauss_dilate (s : Rat) (st : State) :
    gauss (dilate s st) = Vec3.smul (s * s * s) (gauss st) := by
  simp only [gauss, dilate, List.map_map, Function.comp_def]
  have : (fun z : Vec3 × Vec3 => cross (smul s z.1) (smul (s * s) z.2))
      = fun z => smul (s * s * s) (cross z.1 z.2) := by
    funext z
    obtain ⟨⟨a, b, c⟩, ⟨d, e, f⟩⟩ := z
    coupled_vec3_ring
  rw [this, vsum_smul]

/-- Scaling every duration by `s` scales the elapsed time by `s`. -/
-- Modern dependency score: 0 (M=0, H=0; transitive project theorems/axioms).
theorem elapsed_scale (s : Rat) : (hs : List Rat) → elapsed (hs.map (s * ·)) = s * elapsed hs
  | [] => by simp only [List.map_nil, elapsed]; grind
  | h :: hs => by simp only [List.map_cons, elapsed, elapsed_scale s hs]; grind

end NewtonLimitDynamics.Diagnostic.CoupledPolygons
