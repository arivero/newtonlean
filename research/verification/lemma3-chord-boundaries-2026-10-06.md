# Lemma III Corollary 4: chord boundaries, 6 October 2026

## Target and scope

Prove the chord-boundary component of Corollary 4 on a given curve, then
derive boundary convergence for the actual constructed central-force polygons.
`BoundaryLimit` means that, for every positive rational tolerance, sufficiently
fine boundaries lie within that tolerance of the curve, and every curve point
lies within that tolerance of the boundaries. It concerns entire traces,
including completed chord interiors, not only vertices or scalar areas.

The given-curve theorem requires an explicit uniform modulus and a family of
time meshes with vanishing maximum cell span and node coverage. It allows
unequal cells. Dyadic mesh spans and coverage are proved in the constructed
time domain, including the right endpoint and zero window. The actual
general force client derives its own curve modulus from the existing
regional construction; its force-polygon boundary limit follows from the
proved uniform whole-edge estimate. No curve, modulus or boundary limit is
supplied as an additional premise to that client.

The permitted mechanical premises remain the regional Lipschitz and
calibrated-window Conditions. The proof introduces no completed quantity,
derivative, integral, ODE theorem, mathlib, sorry or project axiom. It is a
modern reconstruction of the chord/trace part. The preceding figures' full
historical enclosure proof, tangent polygons, unrestricted continuous force,
ordinary sector-union area and arclength convergence are not certified.

## Newton's proof chain, read from the archived TEI

Both editions' Lemma I statements/proofs, Lemma II statements/proofs,
Lemma III statements/proofs and all four corollaries were read in full.

1687: NATP00077 par1–10; 1713: NATP00082 par2–11.

[1687 Lemma II proof, par4](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4)
identifies the equal-width enclosure gap with one rectangle and then says
`per Lemma I`. [1713 par5](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par5)
retains that explicit citation. Lemma III uses the largest width in
[1687 par6](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par6)
and [1713 par7](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par7).
The existing `rectangle_gap_bound` proves the finite monotone-patch
arithmetic. Its actual curvilinear enclosure geometry is still a distinct
premise/derivation, and is not inferred from that arithmetic alone.

[1687 Corollary 2, par8](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par8):

> figura rectilinea, quæ chordis evanescentium arcuum ab, bc, cd, &c. comprehenditur, coincidit ultimo cum figura curvilinea

[1713 Corollary 2, par9](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par9)
has the corresponding chord claim. Corollary 3 gives the analogous tangent
figure. The shared shrinking enclosure is an implicit dependency there;
the elliptical `Ut &` sentence does not establish that the tangent proof
depends on the chord proof. That distinction is recorded in the source graph.

[1687 Corollary 4, par10](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10):

> Et propterea hæ figuræ ultimæ (quoad perimetros acE,) non sunt rectilineæ, sed rectilinearum limites curvilinci.

[1713 Corollary 4, par11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11):

> Et propterea hæ Figuræ ultimæ (quoad perimetros acE,) non sunt rectilineæ, sed rectilinearum limites curvilinei.

The figures begin with a given curve. Their preceding scalar-area comparison
does not by itself prove that the entire boundary approaches it. The present
chord proof makes the uniform geometric control explicit. `quoad perimetros`
is reconstructed as a boundary trace statement; no arclength limit is claimed.
Straight or constant curves remain allowed by the mathematical construction.

The explicit Proposition I invocation stays separate:
[1687 par45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par45)
and [1713 par51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par51).
The actual force polygons use their own derived whole-edge estimate, rather
than treating the given-curve lemma as a motion-existence theorem.

De Motu's unnumbered limiting passages, NATP00089 par9 and NATP00090 par17,
have separate actual-boundary wrappers in AreaLaw. Neither is credited with
a printed Lemma III or a later edition's premise.

## Mathematical route and reuse

1. Extend ConvexValues' existing finite anchor bound to an arbitrary completed
   centre by projecting its actual Cauchy approximants. No new quotient is made.
2. Define a closed chord as the closure of its rational convex interpolants.
   The existing `closure_image_bound` passes the same anchor bound to every
   completed chord point. Both endpoints belong to each chord family.
3. Apply the given curve's modulus to adjacent time nodes and to their coverage
   of every curve time. The chord-to-curve and curve-to-chord bounds follow.
   Shrinking maximum cell span then derives their common boundary limit.
4. Derive adjacent dyadic-node time bounds and reuse the already proved
   truncation/time coverage and geometric mesh exhaustion.
5. Instantiate the modulus with GeneralForceTime's derived uniform continuity.
   Independently, pass GeneralForcePolygonCurve's existing whole-edge bound
   to both image-trace directions for the actual force polygons.

The scope harness checks arbitrary completed chord points/centres, constant
curves, the final node in a zero window, the actual derived modulus and both
actual boundary families. All source wrappers compile. A conjunction with
the actual interval swept-area theorem checks that the boundary and area
conclusions concern the same constructed motion.

The discriminating control uses a vanishing width-times-unit-height budget
and a persistent point `(0,1)` a unit from the origin. Its failure at radius
1/2 illustrates why a scalar-area budget alone cannot certify a boundary
limit; this is not a counterexample to the given uniformly controlled curve
theorem.

## Verification and remaining proof work

One independent sequential gpt-6-luna verifier ran all 16 README checklist
commands and the scope harness; every command exited 0. It reviewed the
completed-centre projection, closure of entire chords, both trace directions,
derived dyadic coverage and actual force-curve/polygon applications. Logs:
`/tmp/newton-sol61-cor4-final-01.log` through `-16.log` and
`/tmp/newton-sol61-cor4-scope-final.log`. API audit:
`/tmp/newton-sol61-cor4-api.json`; all 2,165 prior named public signatures
remain, with 24 additions. The catalogue has 1,689 theorem rows. The graph
has 88 nodes, 87 edges and 253 passages, with 1,550 reference checks.
The six new corollary nodes and twelve implicit edges retain exact witness
passages and confidence; tangent enclosure reuse stays medium-confidence,
without a chord-to-tangent dependency claim. Only propext, Classical.choice
and Quot.sound occur. No source sorry/admit/new axiom/mathlib, external
package or reversed foundation import appears. Root reviewed source,
scope/API logs and the regenerated printed-edition proof graphs.
The completion scores remain unchanged. Conversation exports are excluded.

Next within the general Proposition I proof: the full source enclosure chain
and tangent-boundary case behind Corollary 4. The next finite step is to prove
when two given supporting tangents meet inside the rectangle of a monotone
curve cell, including coincident tangents and orientation cases. Derive that
cell enclosure from explicit supporting-line/secant inequalities before
passing it through shrinking maximum width and the given curve's modulus.
The finite lower/upper rectangle sums and their actual curvilinear enclosure
must likewise be connected before calling Lemmas II–III's whole area proof
complete. Historical continuously acting force and
ordinary sector-union identification remain distinct. Kepler remains held
until the general proof requirements are met.
