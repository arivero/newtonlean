import BarrowLib.Polygon.Parallelogram
import NewtonLimitDynamics.Polygon.ZeroForce
import NewtonLimitDynamics.Polygon.CentralSchedule

/-! Finite rational reconstruction of Newton's Laws Corollary 1 proof.
The mechanical model takes the change of velocity from an impulse to be an
added vector (Law II and its explanation), and subsequent motion to be the
existing uniform affine map (Law I). These are mechanical premises, not laws
proved from geometry. Transverse invariance, unique intersection for independent
directions, diagonal uniform motion, and the actual central cell's use of that
composition are proved. No force continuity or limit is assumed. -/

namespace NewtonLimitDynamics.Polygon.ImpulseComposition
open NewtonLimitDynamics TimeSubdivision Parallelogram

/-- Law II's directed additive velocity change preserves the transverse
component. The proportionality constant is the explicit scalar `k`. -/
theorem impulse_transverse_unchanged (velocity direction : Point) (k : Fraction) :
    ParallelThrough (pointAdd velocity (pointScale k direction)) velocity direction :=
  parallel_translation velocity direction k

/-- Impulses at the initial point followed by uniform motion give the
parallelogram diagonal at every rational elapsed time. Parallel, opposite
and zero impulse vectors require no division and are included. -/
theorem uniform_impulse_diagonal (p u v : Point) (t : Fraction) :
    pointEquiv (ZeroForce.inertialAt p (pointAdd u v) t)
      (diagonal p (pointScale t u) (pointScale t v)) :=
  pointEquiv_trans
    (pointAdd_congr ⟨Fraction.equiv_refl _,Fraction.equiv_refl _⟩ (pointScale_add t u v))
    (pointEquiv_symm (pointAdd_assoc p (pointScale t u) (pointScale t v)))

/-- The simultaneous endpoint is on both lines reached by the separate
motions. This establishes Newton's two line constraints from the mechanical
model, rather than assuming the parallelogram conclusion. -/
theorem uniform_endpoint_lines (p u v : Point) (t : Fraction) :
    ParallelThrough (ZeroForce.inertialAt p (pointAdd u v) t)
      (ZeroForce.inertialAt p u t) (pointScale t v) ∧
    ParallelThrough (ZeroForce.inertialAt p (pointAdd u v) t)
      (ZeroForce.inertialAt p v t) (pointScale t u) := by
  constructor <;>
    simp only [ParallelThrough,ZeroForce.inertialAt,pointAdd,pointScale,det,
      Fraction.equiv,Fraction.add,Fraction.mul,Int.add_mul,Int.mul_add,
      Int.neg_mul,Int.mul_neg] <;> ac_nf <;> omega

/-- Newton's independent endpoint-line argument: any endpoint with the two
unchanged transverse coordinates is the opposite corner. Uniform motion or
an impulse-at-A clause is not required for this finite inference. -/
theorem endpoint_from_components (p u v x : Point) (h : (det u v).num ≠ 0)
    (hM : ParallelThrough x (pointAdd p u) v)
    (hN : ParallelThrough x (pointAdd p v) u) :
    pointEquiv x (diagonal p u v) :=
  intersection_unique p u v x h hM hN

/-- The actual central-force recurrence uses this same composition. After
the first arrival's impulse, the next drift is its inertial continuation plus
the impulse-generated displacement. This is proved for any sampled field. -/
theorem next_arrival_diagonal (a : CentralSchedule.Field) (h k : Fraction)
    (s : Point × Point) :
    pointEquiv (CentralSchedule.cell a k (CentralSchedule.cell a h s)).1
      (diagonal (CentralSchedule.cell a h s).1 (pointScale k s.2)
        (pointScale k (pointScale h (a (CentralSchedule.cell a h s).1)))) :=
  uniform_impulse_diagonal (CentralSchedule.cell a h s).1 s.2
    (pointScale h (a (CentralSchedule.cell a h s).1)) k

end NewtonLimitDynamics.Polygon.ImpulseComposition
