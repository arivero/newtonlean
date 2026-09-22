# Prioritized case: zero impressed force

The user requested this case explicitly. Here “zero force” means zero
impressed accelerative force in the finite scheduling model. It does not
erase Newton's distinct notion of inherent force (`vis insita`). The aim is
to derive a rational-time rectilinear motion from constructed finite cells,
then identify which further claims require additional premises.

## Source boundary

The following locators motivate a modern coordinate reconstruction. They
create no historical dependency edge or assertion that Newton used our
rational representation.

| Stage and witness | Exact passage | Status and limitation |
| --- | --- | --- |
| De Motu, NATP00089 | [par4](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par4), the inertia statement beginning `Hypoth 2. Corpus omne sola vi insita` | Deleted passage in this witness; do not silently promote it to a surviving premise or infer revision chronology |
| De Motu, NATP00090 | [par5](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par5), `Sola vi insita corpus ... uniformiter in linea recta semper pergere si nil impediat` | The diplomatic witness changes `Hypoth` to `Lex`; keep this witness separate from NATP00089 |
| 1687, NATP00076 | [par1](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par1), `Corpus omne perseverare in statu suo quiescendi vel movendi uniformiter in directum, nisi quatenus a viribus impressis cogitur statum illum mutare.` | Law I; exact stage-local source for the inertial premise |
| 1713, NATP00081 | [par1](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par1), `Corpus omne perseverare in statu suo quiescendi vel movendi uniformiter in directum, nisi quatenus a viribus impressis cogitur statum illum mutare.` | Law I of this edition; not borrowed as a premise for 1687 or De Motu |

The full diplomatic extracts and TEI anchors are already in passages.json.
Confidence in these textual locators is high; any identification of this
formal interface with Newton's complete argument remains a modern
reconstruction.

## Constructed inertial case

`Polygon/ZeroForce.lean` defines `inertialAt p v t = p+t*v` and connects it
to the actual zero-acceleration recurrence. `partitionMotion_zero_force`
gives both the endpoint formula and unchanged velocity.
`inertialAt_time_congr` shows independence of rational representations;
`partitionMotion_cross_partition` covers different positive denominators and
different finite subdivisions with equal represented total times.

`partitionMotion_append` gives exact restart of the finite recurrence.
`inertialAt_add` expresses addition of elapsed times. The within-cell theorem
starts from the actual prefix state and constructs a drift position at an
arbitrary rational increment; the bounded corollary states that the increment
lies inside the selected cell. `partitionMotion_rest` derives the stationary
case without dividing by velocity.

These are stronger statements than collinearity or zero defect area. The
explicit maps `slow(t)=(t,0)` and `fast(t)=(2t,0)` reach the same endpoint
at times `1` and `1/2`, but differ at a common half-time. Their selected
collinear samples have zero signed closed-boundary defect. This use of different
initial velocities concerns insufficient identifying data, not nonuniqueness
for fixed initial data under Law I. Conversely, fixing the kinematic data
must allow a successful classical construction if the finite recurrence
really encodes that law.

The rest and straight-line cases must not require division by speed, swept
area or curvature. Their vanishing deflection cannot discharge an obligation
for a strictly positive quadratic deflection coefficient. A failed attempt
to apply a nondegenerate contact lemma in this case would diagnose the scope
of that lemma, not a failure of the inertial construction.

Even a complete rational-time result does not by itself construct points at
all Euclidean magnitudes of time. State that domain boundary explicitly;
do not use a failure of a Lean tactic or an absent continuum representation
as evidence of a physical obstruction or an action constant.
