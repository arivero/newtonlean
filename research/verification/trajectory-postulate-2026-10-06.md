# Given trajectory and the two area obligations, 6 October 2026

## User-authorized change

The user now asks that trajectory existence be taken as a postulate, and
clarifies that equal swept areas in equal times are the conclusion to prove
in Proposition I. The nonnegative area between Newton's polygon and the
given curve is a separate approximation control. The earlier programme made
trajectory construction a prerequisite; that requirement is superseded for
the primary historical route. Its verified constructive results remain.

The Lean representation of the postulate is the supplied curve parameter
`curve : BinaryTime T hT → PositionValue`. No global `axiom` declaration,
area-law field, convergence field, or equality to a constructed curve is
added to this parameter. A curve parameter alone says nothing about force;
the mechanical and regularity premises still have to be stated and used
in the given-trajectory proof. Taking existence as given is not proving it.

## Source boundary

The archived TEI paragraphs were read directly. In 1687
[NATP00077 par44–45](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par44),
the statement concerns bodies in motion and swept areas proportional to
times; the proof constructs impulse polygons, proves the finite area law,
then invokes Lemma III Corollary 4 at the passage to a curve. The separate
1713 witness is
[NATP00082 par50–51](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par50).
Lemma II starts with a curvilinear figure in
[1687 par3](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3)
and [1713 par4](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par4).
That observation does not itself prove convergence of a mechanical polygon
family to a specified physical trajectory.

De Motu's distinct Theorem 1 passages are
[NATP00089 par8–9](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089#par8)
and [NATP00090 par16–17](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090#par16).
They pass to indefinitely small triangles without importing the printed
Lemma III. Their composition references remain witness-local.

The existence convention has status `editorial_interpretation`, explicitly
authorized by the user, not `explicit_dependency` or an axiom quoted from
Newton. Confidence is high that the cited proof paragraphs contain the
stated steps; no claim is made that they explicitly formulate this modern
existence postulate. Existing historical graph edges and classifications
are unchanged.

## Lean interface and what is proved

`SweptArea.Proportional` is a proposition to prove for the given curve, not
an assumption bundled into its existence. For every pair of times, it
requires convergence of the actual curve-node fans to
`abs(ell)*abs(t1-t0)/2`, using the existing completed operations. The
coefficient must be identified from the motion's mechanical data.

`SweptArea.proportional_equal_times` derives a common swept area for two
equal-duration intervals from a proved proportional-area law. The common
area exists in its conclusion; it is not a vacuous uniqueness implication.
`GeneralForceArea.proportional_swept_area` proves that the retained regional
construction satisfies this new primary target, by the previously checked
interval theorem. No new general given-motion area proof is claimed by
this packaging.

(A) This swept fan area counts multiplicity. Its ordinary sector-union
interpretation is a separate geometric identification. (B) `MatchedRegion`
and the all-cover outer content describe the between-path set; their
nonnegative content and decay are distinct from (A). The existing finite
control `PathDefect.equal_Kepler_areas_positive_path_defect` proves equal
signed and unsigned sector sums with positive intervening patch budget.
It excludes inferring path agreement merely from equal swept areas.

No new completed quantity, force instance, historical dependency edge or
completion score is added. The generic given-curve lemmas can serve the
primary proof. The next substantive obligation is the mechanical
polygon-to-given-trajectory bridge and its area passage, with existence
already granted and both area conclusions still to prove.

## Interrupted rectangle work

The explicitly requested Astra worker exhausted its usage allowance during
the earlier rectangle-union task. Its partial interval lemmas and controls
were not verified or committed. They are preserved under
`/tmp/newton-astra-rectangle-union-partial/`; the active library was restored
to its verified rectangle baseline before this change of primary scope.
The rectangle-union identification remains useful supporting work and open.

## Verification

One independent sequential gpt-6-luna verifier ran all 16 README commands
and the trajectory-postulate scope harness; every command exited 0. All
three build targets passed. The scope review found no circularity or hidden
area result in the trajectory parameter. The two new theorem axiom sets
contain only propext, Classical.choice and Quot.sound. No project axiom,
sorry/admit, mathlib dependency or reversed foundation import was added.

The source API inventory against f4778c0, independently repeated by the root,
found all 2,241 prior public package names/signatures unchanged and exactly
three additions (one goal definition and two theorem interfaces). Catalogue:
1,729 theorems. Graph: 88 nodes, 87 edges, 253 passages and 1,584 checked Lean
references. Progress artifacts record the committed baseline's 1,727
library theorems; the editorial completion scores are unchanged. This is
an interface and programme revision, not another proof of the general
historical Proposition I.

Logs: `/tmp/newton-astra-postulate-final-01.log` through `-16.log`;
scope `/tmp/newton-astra-postulate-scope.log`;
API `/tmp/newton-astra-postulate-api.json`. Conversation exports remain
excluded. Final `git diff --check` passed before commit.
