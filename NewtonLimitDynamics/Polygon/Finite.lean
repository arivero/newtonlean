import Std

namespace NewtonLimitDynamics.Polygon

/-- Synthetic construction interface. Its two identities are imported Euclidean
    geometry: equal triangles on a common altitude (I.38) and same base between
    parallels (I.37). They are not the polygon area-law conclusion. Centre S is
    fixed in this interface; `area p q` measures twice the oriented area Spq.
    `extend p q` continues pq by an equal segment; `kick q x j` translates x
    parallel to Sq, by the central impulse j and the common time cell. -/
structure EuclideanConstruction (Point Impulse : Type) where
  area : Point → Point → Int
  extend : Point → Point → Point
  kick : Point → Point → Impulse → Point
  equal_base_altitude : ∀ p q, area q (extend p q) = area p q
  same_base_parallels : ∀ q x j, area q (kick q x j) = area q x

variable {Point Impulse : Type}

def step (g : EuclideanConstruction Point Impulse) (p q : Point) (j : Impulse) :=
  g.kick q (g.extend p q) j

theorem central_step_area (g : EuclideanConstruction Point Impulse)
    (p q : Point) (j : Impulse) : g.area q (step g p q j) = g.area p q := by
  rw [step, g.same_base_parallels, g.equal_base_altitude]

/-- Successive pairs of vertices, produced by the construction, not supplied
    with equal-area proofs. Each step has the same positive time cell dt. -/
def motion (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) : Nat → Point × Point
  | 0 => (p, q)
  | n+1 => let old := motion g p q impulse n
           (old.2, step g old.1 old.2 (impulse n))

theorem all_cell_areas (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (n : Nat) :
    g.area (motion g p q impulse n).1 (motion g p q impulse n).2 = g.area p q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [motion]
    rw [central_step_area]
    exact ih

def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n+1 => isum f n + f n

theorem sum_constant (f : Nat → Int) (c : Int) (hf : ∀ i, f i = c) (n : Nat) :
    isum f n = (n : Int) * c := by
  induction n with
  | zero => simp [isum]
  | succ n ih => simp [isum, ih, hf, Int.add_mul]

def swept (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (n : Nat) : Int :=
  isum (fun i => g.area (motion g p q impulse i).1 (motion g p q impulse i).2) n

theorem swept_eq (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (n : Nat) : swept g p q impulse n = (n : Int) * g.area p q :=
  sum_constant _ _ (all_cell_areas g p q impulse) n

/-- Cross-multiplied area/time ratio. Positive common dt is stated; division by
    total times additionally requires positive counts. No curve is produced. -/
theorem equal_time_area_reconstruction (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Int) (_hdt : 0 < dt) (m n : Nat) :
    swept g p q impulse m * ((n : Int) * dt) =
    swept g p q impulse n * ((m : Int) * dt) := by
  rw [swept_eq, swept_eq]
  ac_rfl

/-- Finite sum of natural-number magnitudes. -/
def nsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nsum f n + f n

theorem nsum_constant (f : Nat → Nat) (c : Nat) (hf : ∀ i, f i = c) (n : Nat) :
    nsum f n = n * c := by
  induction n with
  | zero => simp [nsum]
  | succ n ih => simp [nsum, ih, hf, Nat.add_mul]

/-- Magnitude of the supplied oriented doubled triangle-area datum. The
    interpretation as Euclidean area is part of the construction's supplied
    semantics; the two preservation identities alone do not certify it. -/
def unsignedCellArea (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (n : Nat) : Nat :=
  (g.area (motion g p q impulse n).1 (motion g p q impulse n).2).natAbs

theorem all_unsigned_cell_areas (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (n : Nat) :
    unsignedCellArea g p q impulse n = (g.area p q).natAbs :=
  congrArg Int.natAbs (all_cell_areas g p q impulse n)

/-- Sum over a consecutive block of cells, starting at `start`. Revisited
    triangles count again: this is not the area of their geometric union. -/
def unsignedBlock (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (start count : Nat) : Nat :=
  nsum (fun i => unsignedCellArea g p q impulse (start + i)) count

theorem unsigned_block_eq (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (start count : Nat) :
    unsignedBlock g p q impulse start count = count * (g.area p q).natAbs :=
  nsum_constant _ _ (fun i => all_unsigned_cell_areas g p q impulse (start + i)) count

/-- Algebraic cross multiplication, valid also for zero counts. A time-ratio
    interpretation additionally requires a positive cell and positive counts. -/
theorem unsigned_block_time_cross (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (dt start₁ start₂ m n : Nat) :
    unsignedBlock g p q impulse start₁ m * (n * dt) =
      unsignedBlock g p q impulse start₂ n * (m * dt) := by
  rw [unsigned_block_eq, unsigned_block_eq]
  ac_rfl

/-- Positive total times and the finite unsigned-area/time comparison, with
    geometric interpretation and force direction still supplied separately. -/
theorem positive_unsigned_area_comparison (g : EuclideanConstruction Point Impulse)
    (p q : Point) (impulse : Nat → Impulse) (dt : Nat) (hdt : 0 < dt)
    (start₁ start₂ m n : Nat) (hm : 0 < m) (hn : 0 < n) :
    0 < m * dt ∧ 0 < n * dt ∧
      unsignedBlock g p q impulse start₁ m * (n * dt) =
        unsignedBlock g p q impulse start₂ n * (m * dt) :=
  ⟨Nat.mul_pos hm hdt, Nat.mul_pos hn hdt,
    unsigned_block_time_cross g p q impulse dt start₁ start₂ m n⟩

/-- A concrete consistency model in integer coordinates. The synthetic result
    above is conditional on the named Euclidean identities, not on coordinates. -/
abbrev LatticePoint := Int × Int

def det (p q : LatticePoint) : Int := p.1 * q.2 - p.2 * q.1

def extend (p q : LatticePoint) : LatticePoint := (2*q.1-p.1, 2*q.2-p.2)
def kick (q x : LatticePoint) (j : Int) : LatticePoint := (x.1+j*q.1, x.2+j*q.2)

theorem extension_identity (p q : LatticePoint) : det q (extend p q) = det p q := by
  simp only [det, extend, Int.mul_sub, Int.mul_assoc]
  have h : q.1 * (2 * q.2) = q.2 * (2 * q.1) := by ac_rfl
  have h1 : q.1 * p.2 = p.2 * q.1 := Int.mul_comm _ _
  have h2 : q.2 * p.1 = p.1 * q.2 := Int.mul_comm _ _
  omega

theorem parallel_identity (q x : LatticePoint) (j : Int) : det q (kick q x j) = det q x := by
  simp only [det, kick, Int.mul_add]
  have h : q.1 * (j * q.2) = q.2 * (j * q.1) := by ac_rfl
  omega

def lattice : EuclideanConstruction LatticePoint Int :=
  ⟨det, extend, kick, extension_identity, parallel_identity⟩

/-- Checked orientation control: signed and unsigned sums agree here. -/
theorem positive_orientation_unsigned_example :
    swept lattice (1, 0) (1, 1) (fun _ => 0) 3 = 3 ∧
      unsignedBlock lattice (1, 0) (1, 1) (fun _ => 0) 0 3 = 3 := by
  decide

/-- Reversing orientation preserves unsigned magnitude, not the signed sum. -/
theorem negative_orientation_unsigned_example :
    swept lattice (1, 0) (1, -1) (fun _ => 0) 3 = -3 ∧
      unsignedBlock lattice (1, 0) (1, -1) (fun _ => 0) 0 3 = 3 ∧
      swept lattice (1, 0) (1, -1) (fun _ => 0) 3 ≠
        (unsignedBlock lattice (1, 0) (1, -1) (fun _ => 0) 0 3 : Int) := by
  decide

/-- Radial degeneracy, rest, and empty blocks need no area division. -/
theorem degenerate_unsigned_examples :
    unsignedBlock lattice (1, 0) (2, 0) (fun _ => -1) 2 3 = 0 ∧
      unsignedBlock lattice (1, 0) (1, 0) (fun _ => 0) 2 3 = 0 ∧
      unsignedBlock lattice (1, 0) (1, 1) (fun _ => 0) 4 0 = 0 := by
  decide

/-- Even inward radial impulses can revisit triangles. The unsigned cell sum
    counts repeated coverage and therefore cannot identify a sector union. -/
theorem repeated_triangle_coverage_example :
    motion lattice (1, 0) (0, 1) (fun _ => -2) 4 = ((1, 0), (0, 1)) ∧
      unsignedBlock lattice (1, 0) (0, 1) (fun _ => -2) 0 4 = 4 ∧
      unsignedBlock lattice (1, 0) (0, 1) (fun _ => -2) 0 8 = 8 := by
  decide

/-- Zero force is permitted; radial/zero-area configurations need no division. -/
example : swept lattice (1,0) (1,1) (fun _ => 0) 3 = 3 := by decide
example : swept lattice (1,0) (2,0) (fun _ => -1) 3 = 0 := by decide

end NewtonLimitDynamics.Polygon
