import NewtonLimitDynamics.Polygon.Finite

namespace NewtonLimitDynamics.Polygon

/-- Data for one finite motion cell. `departure` and `arrival` are kept
    separate: sharing an endpoint in space does not itself say how motion
    passes through that endpoint. This is a modern diagnostic reconstruction
    of the finite polygon stage, not a continuous trajectory. -/
structure FiniteSegment (Point Velocity : Type) where
  first : Point
  last : Point
  departure : Velocity
  arrival : Velocity

variable {Point Velocity Impulse : Type}

/-- The two pieces meet at the same spatial point. -/
def positionContact (left right : FiniteSegment Point Velocity) : Prop :=
  left.last = right.first

/-- A join with no velocity jump. -/
def velocityContact (left right : FiniteSegment Point Velocity) : Prop :=
  positionContact left right ∧ left.arrival = right.departure

/-- A join whose velocity jump is accounted for by the displayed impulse. -/
def impulseContact (advance : Velocity → Impulse → Velocity)
    (left right : FiniteSegment Point Velocity) (j : Impulse) : Prop :=
  positionContact left right ∧ right.departure = advance left.arrival j

theorem velocityContact_position (left right : FiniteSegment Point Velocity)
    (h : velocityContact left right) : positionContact left right :=
  h.1

theorem impulseContact_position (advance : Velocity → Impulse → Velocity)
    (left right : FiniteSegment Point Velocity) (j : Impulse)
    (h : impulseContact advance left right j) : positionContact left right :=
  h.1

/-- Two finite cells with separately recorded incoming and outgoing data at
    their shared instant. -/
structure TwoCellPath (Point Velocity : Type) where
  firstPoint : Point
  middlePoint : Point
  lastPoint : Point
  initialDeparture : Velocity
  middleArrival : Velocity
  middleDeparture : Velocity
  finalArrival : Velocity

def TwoCellPath.left (path : TwoCellPath Point Velocity) : FiniteSegment Point Velocity :=
  ⟨path.firstPoint, path.middlePoint, path.initialDeparture, path.middleArrival⟩

def TwoCellPath.right (path : TwoCellPath Point Velocity) : FiniteSegment Point Velocity :=
  ⟨path.middlePoint, path.lastPoint, path.middleDeparture, path.finalArrival⟩

/-- Assemble two cells only after their spatial endpoints have been shown to
    agree. The construction retains, rather than erases, the possible velocity
    jump at the shared instant. -/
def glue (left right : FiniteSegment Point Velocity)
    (_h : positionContact left right) : TwoCellPath Point Velocity :=
  ⟨left.first, right.first, right.last,
    left.departure, left.arrival, right.departure, right.arrival⟩

theorem glue_first (left right : FiniteSegment Point Velocity)
    (h : positionContact left right) : (glue left right h).firstPoint = left.first :=
  rfl

theorem glue_last (left right : FiniteSegment Point Velocity)
    (h : positionContact left right) : (glue left right h).lastPoint = right.last :=
  rfl

theorem glue_middle_from_left (left right : FiniteSegment Point Velocity)
    (h : positionContact left right) : (glue left right h).middlePoint = left.last :=
  h.symm

theorem glue_middle_from_right (left right : FiniteSegment Point Velocity)
    (h : positionContact left right) : (glue left right h).middlePoint = right.first :=
  rfl

theorem glued_position_contact (left right : FiniteSegment Point Velocity)
    (h : positionContact left right) :
    positionContact (glue left right h).left (glue left right h).right :=
  rfl

/-- A finite sample records point values at instants, but leaves arrival and
    departure data independent. It therefore represents no claim that a
    continuous trajectory exists. -/
structure SampledPath (Point Velocity : Type) where
  point : Nat → Point
  arriving : Nat → Velocity
  departing : Nat → Velocity

def SampledPath.cell (path : SampledPath Point Velocity) (i : Nat) :
    FiniteSegment Point Velocity :=
  ⟨path.point i, path.point (i+1), path.departing i, path.arriving (i+1)⟩

/-- Restriction is re-indexing of already supplied samples; it constructs no
    new point at an intermediate time. -/
def SampledPath.restrict (path : SampledPath Point Velocity) (offset : Nat) :
    SampledPath Point Velocity :=
  ⟨fun i => path.point (offset+i), fun i => path.arriving (offset+i),
    fun i => path.departing (offset+i)⟩

theorem restriction_cell (path : SampledPath Point Velocity) (offset i : Nat) :
    (path.restrict offset).cell i = path.cell (offset+i) := by
  simp [SampledPath.restrict, SampledPath.cell, Nat.add_assoc]

theorem adjacent_position_contact (path : SampledPath Point Velocity) (i : Nat) :
    positionContact (path.cell i) (path.cell (i+1)) :=
  rfl

theorem adjacent_velocityContact_iff (path : SampledPath Point Velocity) (i : Nat) :
    velocityContact (path.cell i) (path.cell (i+1)) ↔
      path.arriving (i+1) = path.departing (i+1) := by
  simp [velocityContact, positionContact, SampledPath.cell]

theorem adjacent_impulseContact_iff (advance : Velocity → Impulse → Velocity)
    (path : SampledPath Point Velocity) (i : Nat) (j : Impulse) :
    impulseContact advance (path.cell i) (path.cell (i+1)) j ↔
      path.departing (i+1) = advance (path.arriving (i+1)) j := by
  simp [impulseContact, positionContact, SampledPath.cell]

/-- Restarting the finite construction from its kth constructed pair, with the
    shifted impulse sequence, gives the original construction after k+n cells.
    This is a theorem about the existing recursive polygonal motion only. -/
theorem motion_restart (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (k n : Nat) :
    motion g (motion g p q impulse k).1 (motion g p q impulse k).2
      (fun i => impulse (k+i)) n = motion g p q impulse (k+n) := by
  induction n with
  | zero => simp [motion]
  | succ n ih =>
    rw [show k + (n+1) = (k+n)+1 by omega]
    simp only [motion]
    rw [ih]

/-- Consecutive pairs created by `motion` share their middle vertex. -/
theorem motion_adjacent_pair_position_contact
    (g : EuclideanConstruction Point Impulse) (p q : Point)
    (impulse : Nat → Impulse) (n : Nat) :
    (motion g p q impulse n).2 = (motion g p q impulse (n+1)).1 :=
  rfl

/-- Discrete velocity for unit-time lattice cells. -/
def latticeVelocity (p q : LatticePoint) : LatticePoint :=
  (q.1-p.1, q.2-p.2)

def latticeAdd (p q : LatticePoint) : LatticePoint :=
  (p.1+q.1, p.2+q.2)

def latticeScale (j : Int) (q : LatticePoint) : LatticePoint :=
  (j*q.1, j*q.2)

/-- The actual lattice step changes discrete velocity by the radial impulse.
    Unit time is built into the use of adjacent vertex differences. -/
theorem lattice_step_velocity_jump (p q : LatticePoint) (j : Int) :
    latticeVelocity q (step lattice p q j) =
      latticeAdd (latticeVelocity p q) (latticeScale j q) := by
  apply Prod.ext <;>
    simp [latticeVelocity, latticeAdd, latticeScale, step, lattice, kick, extend] <;>
    omega

theorem motion_lattice_velocity_jump (p q : LatticePoint)
    (impulse : Nat → Int) (n : Nat) :
    latticeVelocity (motion lattice p q impulse n).2
      (motion lattice p q impulse (n+1)).2 =
      latticeAdd
        (latticeVelocity (motion lattice p q impulse n).1
          (motion lattice p q impulse n).2)
        (latticeScale (impulse n) (motion lattice p q impulse n).2) := by
  change latticeVelocity (motion lattice p q impulse n).2
      (step lattice (motion lattice p q impulse n).1
        (motion lattice p q impulse n).2 (impulse n)) = _
  exact lattice_step_velocity_jump _ _ _

/-- The nth actual lattice motion cell arrives and departs with its own
    finite-difference velocity. The following cell may have a different one. -/
def latticeMotionCell (p q : LatticePoint) (impulse : Nat → Int) (n : Nat) :
    FiniteSegment LatticePoint LatticePoint :=
  let cell := motion lattice p q impulse n
  ⟨cell.1, cell.2, latticeVelocity cell.1 cell.2, latticeVelocity cell.1 cell.2⟩

theorem latticeMotionCell_adjacent_position_contact (p q : LatticePoint)
    (impulse : Nat → Int) (n : Nat) :
    positionContact (latticeMotionCell p q impulse n)
      (latticeMotionCell p q impulse (n+1)) :=
  motion_adjacent_pair_position_contact lattice p q impulse n

theorem latticeMotionCell_impulseContact (p q : LatticePoint)
    (impulse : Nat → Int) (n : Nat) :
    impulseContact latticeAdd (latticeMotionCell p q impulse n)
      (latticeMotionCell p q impulse (n+1))
      (latticeScale (impulse n) (motion lattice p q impulse n).2) := by
  constructor
  · exact latticeMotionCell_adjacent_position_contact p q impulse n
  · change latticeVelocity (motion lattice p q impulse (n+1)).1
      (motion lattice p q impulse (n+1)).2 = _
    rw [← motion_adjacent_pair_position_contact lattice p q impulse n]
    exact motion_lattice_velocity_jump p q impulse n

theorem latticeMotionCell_zero_impulse_velocityContact (p q : LatticePoint)
    (impulse : Nat → Int) (n : Nat) (hzero : impulse n = 0) :
    velocityContact (latticeMotionCell p q impulse n)
      (latticeMotionCell p q impulse (n+1)) := by
  constructor
  · exact latticeMotionCell_adjacent_position_contact p q impulse n
  · change latticeVelocity (motion lattice p q impulse n).1
      (motion lattice p q impulse n).2 =
        latticeVelocity (motion lattice p q impulse (n+1)).1
          (motion lattice p q impulse (n+1)).2
    rw [← motion_adjacent_pair_position_contact lattice p q impulse n]
    rw [motion_lattice_velocity_jump, hzero]
    simp [latticeAdd, latticeScale]

/-- The two displayed inward central-impulse (discrete-force) histories start
    with the same vertices. Every polygonal swept-area sum agrees, although
    their first constructed next vertex differs. Thus equal areas do not
    identify a polygonal path. The histories are different, so this is not
    nonuniqueness for a fixed specified force law. -/
def inwardOneRadialImpulse : Nat → Int := fun _ => -1
def inwardTwoRadialImpulse : Nat → Int := fun _ => -2

theorem inward_impulses_same_swept (n : Nat) :
    swept lattice (1, 0) (1, 1) inwardOneRadialImpulse n =
      swept lattice (1, 0) (1, 1) inwardTwoRadialImpulse n := by
  rw [swept_eq, swept_eq]

theorem inward_impulses_distinct_next_vertex :
    (motion lattice (1, 0) (1, 1) inwardOneRadialImpulse 1).2 ≠
      (motion lattice (1, 0) (1, 1) inwardTwoRadialImpulse 1).2 := by
  decide

theorem equal_swept_area_does_not_identify_next_vertex :
    (∀ n, swept lattice (1, 0) (1, 1) inwardOneRadialImpulse n =
      swept lattice (1, 0) (1, 1) inwardTwoRadialImpulse n) ∧
    (motion lattice (1, 0) (1, 1) inwardOneRadialImpulse 1).2 ≠
      (motion lattice (1, 0) (1, 1) inwardTwoRadialImpulse 1).2 :=
  ⟨inward_impulses_same_swept, inward_impulses_distinct_next_vertex⟩

end NewtonLimitDynamics.Polygon
