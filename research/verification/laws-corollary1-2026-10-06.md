# Laws Corollary 1: finite proof route, 6 October 2026

## Statement and mechanical premises

Reconstruct the two steps in Newton's proof: an impulse parallel to a line
leaves the velocity of approach unchanged, and the endpoint constraints for
BD and CD locate the body at their intersection D. In the finite rational
model, Law II supplies directed additive velocity changes; Law I supplies
subsequent uniform motion. These mechanical laws are premises of the model,
not physical laws deduced from affine geometry.

`uniform_endpoint_lines` proves both constraints directly from determinant
arithmetic, without using the diagonal theorem. The cofactor identity and
nonzero rational cancellation prove `Parallelogram.intersection_unique`.
The stage-local `corollary1_endpoint_reconstruction` results then derive D
through those independently proved line constraints. No desired endpoint or
parallelogram identity is a supplied premise. Independent directions are
required for this intersection proof. The separate all-direction composition
identity covers parallel, opposite and zero impulses without division.

`next_arrival_diagonal` applies the composition to the actual central-force
recurrence: after the impulse at its first arrival, the next drift is the
inertial continuation plus the impulse-generated displacement. Thus this is
a dependency used by the existing construction, not a separate force example.
Rational time, the planar model and its mechanical premises remain explicit;
no curve limit or force regularity is claimed here.

## Sources read and witness separation

The archived TEI Laws I/II statements, Law II explanation and Corollary 1
proofs were read in both editions: NATP00076 and NATP00081 par1/3/4/7/8.

[1687 NATP00076 par8](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00076#par8):

> hæc vis nihil mutabit velocitatem accedendi ad lineam illam BD a vi altera genitam

The endpoint is then in BD and CD, hence their intersection D. This proof
does not explicitly cite Laws II or I, or state the later impulse-at-A and
uniform-motion clauses. Its uniform-impulse result is an explicitly named
modern rational specialization, not a claim that those clauses occur here.

[1713 NATP00081 par8](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00081#par8):

> hæc vis per Legem II nihil mutabit velocitatem accedendi ad lineam illam BD a vi altera genitam

> Perget autem motu rectilineo ab A ad D per Legem I.

The initial sentence specifies the forces impressed at A and uniform separate
motion. Both explicit law edges stay local to 1713. The mechanical premises
are reflected in the additive impulse/uniform-motion model, not filled by
a premise bundle containing the desired diagonal result.

[De Motu NATP00090 par10–11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par11)
contains Lemma 1's transverse-approach and intersection proof. The `per Legem 2`
words are an addition in the TEI; the relative revision chronology remains
unresolved. Its result has a separate witness name.

[NATP00089 par7](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par7)
instead states simultaneous/successive composition as a hypothesis. The
separate `natp00089_composition_model` is a modern model consequence and is
not labelled a historical proof of that mechanical hypothesis. Par9's altered
marginal reference labels remain unresolved. No printed limiting lemma is
imported into either De Motu witness.

The existing evidence edges retain exact passages, witness URLs, confidence
and classifications. Formal references now identify the finite composition
proofs instead of area-comparison theorems that did not prove composition.

## Reuse and controls

Rational multiplication cancellation belongs in RationalMagnitudes. Point
congruence, determinant bilinearity and the cofactor identity belong in
PointAlgebra; reused private StripArea identities were moved there. Existing
public determinant and point-subtraction interfaces forward to the shared
proofs with unchanged signatures. Parallelogram is generic Barrow geometry;
the mechanical interpretation stays in NewtonLimitDynamics. No new completed
quantity or quotient lift is introduced.

The scope harness checks nonorthogonal directions, a translated origin,
fractional time, equivalent rational denominators, all printed/de-Motu
proof routes, parallel/opposite/zero impulses, and actual next-cell use.
Two discriminating controls refute uniqueness from just one endpoint line
and from two coincident lines with parallel directions.

## Verification

One independent sequential gpt-6-luna verifier ran all 16 README checklist
commands and the scope harness; all exited 0. It confirmed that the endpoint
lines are derived independently of the diagonal and that the witness-local
endpoint proofs then use unique intersection. Logs:
`/tmp/newton-sol61-cor1-final-01.log` through `-16.log` and
`/tmp/newton-sol61-cor1-scope-final.log`. The API audit at
`/tmp/newton-sol61-cor1-api.json` retains all 2,137 prior named public
signatures, with 28 additions. The catalogue has 1,671 theorem rows; the graph
retains 82 nodes, 75 edges and 253 passages, with 1,532 reference checks.
Only propext, Classical.choice and Quot.sound occur. External packages remain
empty; no source sorry/admit/new axiom/mathlib or reversed foundation import
appears. Root reviewed the source, scope/API logs and changed proof images.
Graph and progress artifacts were regenerated; conversation exports remain
excluded. The completion estimate remains about 40% overall and 66% for
Proposition I; no additional score is assigned to this dependency.

Next: Lemma III Corollary 4 through Lemmas I–III and the preceding
corollaries, retaining the given-curve premise and proving perimeter/trace
convergence rather than only scalar area convergence. Its application to
the constructed force polygons is a separate obligation, before Kepler.
