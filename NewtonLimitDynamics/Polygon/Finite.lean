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

/-- Zero force is permitted; radial/zero-area configurations need no division. -/
example : swept lattice (1,0) (1,1) (fun _ => 0) 3 = 3 := by decide
example : swept lattice (1,0) (2,0) (fun _ => -1) 3 = 0 := by decide

end NewtonLimitDynamics.Polygon
