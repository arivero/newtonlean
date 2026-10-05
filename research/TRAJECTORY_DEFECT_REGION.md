# Area of the constructed intervening region

This is a specification for the next geometric proof, not a checked area
theorem. It concerns the primary Proposition I variant that constructs its
motion from actual impulse polygons. The harmonic construction is a modern
rational-coordinate reconstruction, separate from the historical claims in
De Motu, 1687 and 1713. See [the path-area distinction](PROP_I_PATH_DEFECT.md)
and [the construction ledger](CAUCHY_REALIZATION.md).

## Region to construct

The binary time quotient and its continuous state map are proved.
PositionValues now derives the nonexpansive position and coordinate projections
on rational states, their Cauchy-name maps and equivalence preservation before
quotient lifting. Position values are the values fixed by the proved idempotent
position projection. Its gammaPosition map inherits continuity, time aliases,
endpoints and zero cases. Completed coordinate squares use two closed
coordinate bounds and a nonnegative radius; eventual rational bounds imply
membership. State values retain velocity as well; planar area uses PositionValue.

The production example w=1,T=1/4,s=((1,0),(0,1)) now has a checked position
separation proof: the two-cell endpoint at level 1 has distance 135/512 from
the initial point, its state tail is 3/16, and every later position distance
is at least 39/512. The projected right and left values differ. A radius-1
coordinate square contains (1,1) at centre (0,0), whose L1 distance is 2.
These controls use the disclosed production inputs, not an independent oracle.

HarmonicPolygonCurve now constructs level-m polygon position names from actual
coarse vertices and within-cell inertial drifts at every binary address. Their
whole-cell distance to gammaPosition is bounded uniformly by an explicit
geometric radius. Same-cell equivalent addresses agree. Complete the
different-cell boundary alias bridge before lifting a single P_m to the time
quotient; an address choice must not change the polygon position.

Define the intervening region as the union of segments joining simultaneous
positions P_m(t) and gamma(t). The segment parameter must range over the
constructed unit interval, with its values and interpolation derived from
rational approximants. The last connector P_m(T) to gamma(T) is included;
their endpoints need not coincide at a finite mesh. The first endpoints must
be proved equal. Crossings and opposite lobes remain in this nonnegative
point set. The definition is a union, while a finite covering sum counts
overlap with multiplicity. Keep these two conventions distinct.

## Same-time coarse polygon map to construct

For address b and coarse level m, let (x_m,v_m) be its actual coarse prefix
state and t_m its elapsed time. Use the later actual times t_(m+j) and form
the rational position x_m+(t_(m+j)-t_m)*v_m. Derive that its phase lies between
0 and H_m from the binary ticks. This shift keeps every approximant inside
the selected coarse cell, including at early name indices.

Derive a uniform time-difference bound for arbitrary coarse cells and phases
from actual drift steps. Across different cells, split the difference into the
first remaining drift, the intervening coarse vertices and the last partial
drift. Their nonnegative durations sum to the actual time difference. Within
one cell, use the same incoming velocity. This proves both the name's Cauchy
condition and agreement for equivalent time addresses before any quotient lift.
An address alias at a coarse vertex must yield one polygon position.

The left endpoint must be the initial point and the right endpoint the actual
level-m full-schedule position. Then derive enclosures about each coarse start:
the existing prefix tail suggests radius R_m for gamma's position, while the
coarse drift has radius 2*H_m*M. Prove the latter fits R_m. No supplied polygon
curve, full-time interpolation, limiting point or scalar area enters this step.

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
