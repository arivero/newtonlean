# Area of the constructed intervening region

This is a specification for the next geometric proof, not a checked area
theorem. It concerns the primary Proposition I variant that constructs its
motion from actual impulse polygons. The harmonic construction is a modern
rational-coordinate reconstruction, separate from the historical claims in
De Motu, 1687 and 1713. See [the path-area distinction](PROP_I_PATH_DEFECT.md)
and [the construction ledger](CAUCHY_REALIZATION.md).

## Region to construct

After the binary time quotient and its motion map are proved, project the
state values to position values. Construct the level-m polygon map P_m on the
same time quotient from its actual coarse vertices and within-cell inertial
drifts. Prove this map agrees for equivalent time descriptions; a choice of
binary address must not change the polygon position.

The first bounded geometric step is the position projection. State values
contain both position and velocity; they are not planar area coordinates.
Derive the nonexpansive rational projection to (position, zero velocity), its
action on Cauchy names and name equivalence, and its well-defined idempotent
action on values. Position values can then be the values fixed by this
projection. Coordinate projections must also be derived before defining a
completed coordinate square by its two closed coordinate bounds.

A production separation target uses w=1,T=1/4,s=((1,0),(0,1)). The two-cell
endpoint at level1 has position distance 135/512 from its initial point. The
checked state tail there is 3/16. Deriving a position lower bound 39/512 for
all later endpoint levels would prove that the projected right endpoint
differs from the initial position. State separation alone does not prove this.
This is a proposed arithmetic control, not a checked theorem or independent
oracle. Avoid evaluating large unnormalized rational schedules to obtain it.

Define the intervening region as the union of segments joining simultaneous
positions P_m(t) and gamma(t). The segment parameter must range over the
constructed unit interval, with its values and interpolation derived from
rational approximants. The last connector P_m(T) to gamma(T) is included;
their endpoints need not coincide at a finite mesh. The first endpoints must
be proved equal. Crossings and opposite lobes remain in this nonnegative
point set. The definition is a union, while a finite covering sum counts
overlap with multiplicity. Keep these two conventions distinct.

## Nonnegative area to construct

For this region, define finite-square outer content by its upper rational cut:
q is an upper value if there exists a finite coordinate-square cover of the
region whose summed square areas are less than q. A square of nonnegative
rational radius R has area 4*R^2. This definition depends on the region and
actual covers; it does not set the area equal to a proposed budget.

Prove the cut is proper, inhabited, upward closed and rounded from
nonnegative cover areas and a derived finite cover. This constructs the stated
outer-content value without a supplied scalar area or imported measure theorem.
Equality with an inner content or a different conventional area notion needs
its own proof. A signed Kepler-sector difference is not this quantity.

## Candidate enclosure and decay

Write H_m=T/2^m and C=2*(1+|w|)+3*T*|w|. The checked binary-prefix state tail
suggests a square of radius R_m=H_m*M*C about each actual coarse start.
Derive the position bound for every later approximant and the coarse edge's
drift bound before passing to quotient values. Prove representative invariance
and convex closure of the completed-coordinate square. Then show every
simultaneous-position connector lies in its coarse-cell square, including
the last endpoint connector.

One square per coarse cell has the candidate nonnegative budget

    B_m = 4*2^m*R_m^2 = 4*T*H_m*M^2*C^2.

This is a future theorem target. Once the region containment and identity are
proved, the outer-content bound follows from that actual cover. Finite integer
arithmetic should construct a mesh index making B_m less than each positive
rational tolerance, uniformly at all later levels. Zero time and zero initial
state must remain included. Neither signed cancellation nor equality of Kepler
areas supplies any of these premises.

Mechanical identification of gamma with the uninterrupted harmonic force,
partition independence and the general central-field construction remain
separate. A geometric bound for the constructed path cannot silently certify
its acceleration law or a historical limiting argument.
