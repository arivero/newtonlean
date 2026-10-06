# One finite common-force time subdivision

This is a modern coordinate reconstruction for the refinement obligation in
[the Section II map](SECTION_II.md), and it certifies no historical proof.
Its cell structure is Proposition I's own; the coordinates, impulse scaling
and schedule comparison are modern, as [Newton's time](#newtons-time-parts-and-boundaries)
sets out below. It constructs finite polygons from given cell data, with no
assumed limiting trajectory and no integral calculus.

Choose positive rational durations `h` and `k`, with coarse duration `h+k`,
and common initial position `p`, velocity `v`, and constant accelerative force
`a` (force per unit mass). In each cell of duration `d`, drift from `p` to
`p+d*v`, then apply the velocity impulse `d*a` at the right endpoint. The
terminal impulse changes velocity but adds no displacement in that cell.

The coarse endpoint is `C = p+(h+k)*v`. The fine polygon first reaches
`B = p+h*v`, receives impulse `h*a`, and then reaches
`D = B+k*(v+h*a)`. Its final impulse is `k*a`. Thus the two constructions
use the same initial data, total duration and force coefficient, with matching
total impulse. Their terminal velocities agree, while

`D = C + (h*k)*a`.

This mismatch is a failure of exact nesting for this convention. It does not
establish failure of trajectory existence, fixed-force nonuniqueness or an
obstruction to a different classical scheduling convention.

To compare enclosed finite areas when `D` differs from `C`, close the boundary
explicitly: traverse `p → B → D`, add the straight connector `D → C`, and
return along the reversed coarse edge `C → p`. The connector is geometric
bookkeeping at the shared terminal time, not an additional mechanical cell.
The determinant sum of this boundary is a signed doubled polygon area; its
absolute value is not by itself a bound on position error or on sums of
absolute cell defects.

For the rational example `h=k=1/2`, `p=(0,0)`, `v=(1,0)`, `a=(0,1)`,
the intermediate vertex is `B=(1/2,0)`, the coarse endpoint is `C=(1,0)`,
and the fine endpoint is `D=(1,1/4)`. The connector has displacement
`(0,-1/4)`. The closed boundary has signed doubled area `-1/8` under the
displayed orientation. This scalar is a finite defect between constructed
polygons, not the area between a polygon and an assumed curve.

The Lean implementation uses the existing signed `Fraction` representatives;
coordinate equalities mean cross-multiplication equivalence, not equality of
unnormalized numerator/denominator records. Its algebraic mismatch and velocity
identities hold for arbitrary rational inputs; positive-duration facts give
the intended mechanical specialization.

The finite-partition follow-up is now implemented in
[PartitionControl](PARTITION_CONTROL.md): it derives exact endpoint formulas
and a largest-cell coefficient bound from the constructed schedules, and
`PartialCell.lean` extends both to positions inside a cell. The next
obligation is rational-time convergence across partitions,
tracking non-nested endpoints and connectors explicitly. Keep finite sums of
absolute defects separate from signed cancellation. A general justified limiting
time-to-position map, partition independence and continuous-force
identification remain later obligations. No action constant is selected here.

## Newton's time: parts and boundaries

The cell convention above is Proposition I's construction in both printed
editions. Newton divides time into equal parts, "Dividatur tempus in partes
æquales"; in each part the body moves uniformly by Law I, and the centripetal
force acts "impulsu unico sed magno" when the body reaches the boundary point
B (NATP00077.par45; NATP00082.par51). The modern additions are the rational
coordinates, the impulse `d*a` scaled by cell duration, unequal cells and the
comparison of coarse and fine schedules.

Unbounded refinement has a printed warrant too. The Section I scholium sets
aside the "indivisibilium Hypothesis", spelled "Indivisibilium hypothesis"
in 1713, and asks that apparently least
quantities be read as "evanescentia divisibilia", always to be diminished
"sine limite" (NATP00077.par40 and par42; NATP00082.par46 and par48). In the
construction every positive cell duration can be divided again, and no least
duration exists. Instants serve as cell boundaries; durations are the parts
that refine.

The four witnesses of the area law word the time steps differently. Both
De Motu manuscripts give each moment of time, "singulis temporis momentis",
its own segment and then its own triangle, and close with triangles "numero
infinita et infinitè parva" (NATP00089.par9; NATP00090.par17). The 1687 and
1713 texts say "singulis temporis particulis" and close with a process:
"Augeatur jam numerus & minuatur latitudo triangulorum in infinitum"
(NATP00077.par45; NATP00082.par51). Neither De Motu manuscript discusses
indivisibles. Reading the change as a deliberate move away from indivisible
moments is an `editorial_interpretation` with medium confidence: it agrees
with the new Section I scholium, but no passage states Newton's motive.

The Definitions scholium supplies the remaining structure. Absolute time
"æquabiliter fluit, alioq; nomine dicitur Duratio", and "partium Temporis ordo
est immutabilis" (NATP00075.par21 and par26; NATP00080.par21 and par26).
Equable flow makes durations comparable, the parts are ordered, and Newton
names no origin of time. A formalization that keeps this distinction uses a
type of instants and a separate type of durations: instants differ by
durations, and durations form an ordered additive group. That is the affine
structure of Weyl and of Arnold's treatment of Galilean space-time, and it
belongs in ModernLib as a reconstruction. The present code already treats
durations as primary. `elapsed` sums cell durations, and a completed
`BinaryTime` instant is named by a binary address inside the duration `T`
measured from the start of the motion.

The originating conversation needs two corrections. Its quotation "singulis
temporis particulis æqualibus" from the scholium to the Laws is absent from
the archived 1687 and 1713 texts of that scholium (NATP00076.par24;
NATP00081.par24); it may belong to a later edition and remains unverified.
Its manuscript definition of moments as generating principles, "ut tempus
præsens præteriti et futuri … punctum lineæ" (NATP00091.par24), is struck
through in full, so it records a discarded draft.

Leads outside the archive, quoted in that conversation and still unverified:
the student notebook Quæstiones quædam Philosophiæ, with "a least degree of
time"; the General Scholium, with "durationis indivisibile momentum"; Newton's
draft additions to the scholium on Leibniz; and Book II Lemma II on moments.
Together they would trace a path from temporal atomism in the notebook to
divisible durations in the Principia. That genealogy lies outside the
approved programme of Propositions I–IV.

Source: the conversation export archived in commit `a5f090e`, with each Latin
quotation above checked against the archived TEI. The same commit keeps the
rest of that conversation, including its survey of earlier Lean work on
Newtonian kinematics.
