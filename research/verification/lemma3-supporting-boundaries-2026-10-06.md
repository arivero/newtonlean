# Lemma III supporting boundaries, 6 October 2026

This increment proves the finite supporting-line cell enclosure and its
whole closed boundary limit. It follows the chord increment and serves the
Corollaries 3–4 branch invoked by Proposition I. It introduces no force
instance or completed quantity. The completion scores remain unchanged.

## Source and scope

The archived Newton Project TEI was read directly. In 1687
[NATP00077 par9](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par9)
states `Ut & figura rectilinea quæ tangentibus eorundem arcuum circumscribitur`;
[par10](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par10)
begins `Et propterea` and specifies `quoad perimetros acE`. In 1713
[NATP00082 par10](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par10)
has the separately retained wording `Figura rectilinea circumscripta quæ
tangentibus eorundem arcuum comprehenditur`;
[par11](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par11)
gives that edition's perimeter conclusion. The preceding Lemma III proofs
are NATP00077 par5–6 and NATP00082 par6–7: unequal widths are bounded by the
largest width. Lemma II's actual curvilinear-area enclosure and Lemma I's
exhaustion remain part of the proof chain.

The historical enclosure reuse is `implicit_dependency`, medium confidence:
the elliptical `Ut &` does not establish a chord-to-tangent proof dependency.
The collective Corollary 3-to-4 edge is implicit, high confidence. Exact
witnesses, passages, URLs and revision layers stay in dependencies.json.
The new Lean references are modern rational reconstructions with narrower
explicit geometric premises, not certifications of these historical edges.
No printed tangent corollary is imported into De Motu.

## Derived construction

`SupportingTangents.Cell` records two endpoint lines over one rational
horizontal cell, opposite endpoint support inequalities and a shared
monotone ordinate direction. Both upper/lower support orientations and
increasing/decreasing ordinates are allowed. It does not record a meeting,
rectangle enclosure or boundary limit.

`affine_crossing` constructs a rational unit parameter by balancing the two
nonnegative endpoint slacks. Zero slacks choose the left endpoint: coincident
lines do not require a unique infinite-line intersection. `meeting_exists`
constructs the meeting; `meeting_on_lines` proves incidence. For independent
directions, `meeting_unique` uses the existing determinant-coordinate theorem
to identify any intersection with this constructed meeting.

`meeting_rectangle` derives both coordinate bounds. Reversed abscissae and
horizontal/zero cells are included. `rectangle_distance_bound` then bounds
the distance from an endpoint by the distance between endpoints.
`SupportingBoundary.cellTrace_bound` transfers this bound to every completed
point of both joined finite segments through the canonical convex operation
and metric closure. Arbitrary points of an infinite coincident line are not
allowed as polygon vertices. The old chord interface is retained, with its
bound now an application of the shared `closedChord_ball` theorem.

`supportingTrace_limit` derives both boundary directions from shrinking
maximum time-cell spans, time-node coverage, uniform convergence of finite
nodes to a given curve, and that curve's explicit uniform modulus. Unequal
cells are allowed. A quarter-tolerance accounts for the two endpoint errors,
curve variation and final endpoint comparison. `dyadic_supportingTrace_limit`
derives the dyadic spans/coverage, including the right boundary and zero
windows. The separately named 1687 and 1713 Corollaries 3–4 wrappers use this
shared proof.

## Controls and remaining work

The scope harness checks nonparallel upper/lower supports, decreasing and
reversed-coordinate patches, an arbitrary line intersection, coincident
horizontal lines, whole completed segments, final nodes and zero windows.
An outside point lies on the infinite coincident line but is excluded from
the finite meeting. A separate pair of supported lines with opposite
ordinate directions meets outside the endpoint rectangle: this checks that
the monotone-direction premise is substantive.

Finite supporting-line data and convergence of their samples remain explicit
premises. Existence and identification of actual curve tangents, vertical
tangents over a nonzero horizontal cell and patch decomposition are not
proved here. Nor are area, arclength, unrestricted force identification or
the full historical Proposition I certified by this boundary result.

Next within Order 1: connect the lower/upper rectangle point sets and their
finite area sums to the given monotone curvilinear figure, then exhaust their
maximum-width gap through Lemma I. This is required before claiming the
whole historical area-enclosure proof. Kepler remains held.

## Verification

One independent sequential gpt-6-luna verifier ran all 16 README checklist
commands and both the supporting-boundary and retained chord scope harnesses;
all exited 0. It confirmed the affine crossing parameter is constructed from
the endpoint support slacks, arbitrary intersections of independent lines
are identified with that meeting, and only joined finite segments are used
when supports coincide. Both support orientations and increasing/decreasing
ordinate patches are admitted. The support-only/no-monotonicity negative
control compiles and exhibits an intersection outside the endpoint rectangle.

The public named API audit against HEAD 0b1032a found all 2,189 prior names
and signatures unchanged, with 22 additions. Catalogue: 1,706 theorems;
graph: 88 nodes, 87 edges, 253 passages and 1,565 Lean references. The
1687/1713 enclosure-reuse edges remain implicit at medium confidence and do
not assert chord-to-tangent dependence. Only propext, Classical.choice and
Quot.sound occur. No source sorry/admit/project axioms/Mathlib, external
packages or reversed BarrowLib imports appear. Finite rational support data,
the given-curve modulus and convergence of its finite nodes remain premises;
actual tangent existence, vertical patches, and the full historical area
proof remain open. No arclength or full Proposition I claim is made.

Logs: /tmp/newton-sol61-support-final-01.log through -16.log;
support scope /tmp/newton-sol61-support-scope-final.log;
retained chord scope /tmp/newton-sol61-support-chord-scope-final.log;
API /tmp/newton-sol61-support-api.json. Conversation exports remain excluded.
