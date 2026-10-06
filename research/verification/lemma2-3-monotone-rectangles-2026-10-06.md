# Monotone rectangle enclosure, 6 October 2026

This increment connects actual lower/upper rectangle point sets to a given
monotone graph, constructs the largest cell width, and derives the finite
rectangle-sum gap and its exhaustion. It continues the invoked Lemmas II–III
proof chain after the supporting-boundary increment f753c6b. No completed
quantity or force instance is introduced; completion scores remain unchanged.

## Source

The archived TEI passages were read directly. In 1687
[NATP00077 par3](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par3)
gives the curvilinear figure and equal-width inscribed/circumscribed rectangles.
[Par4](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par4)
identifies their difference as one common width times the sum of heights,
namely the total height Aa, then explicitly invokes Lemma I. Lemma III
[par5–6](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077#par5)
allows unequal widths and replaces the common width by the greatest, AF.
The separately retained 1713 passages are
[NATP00082 par4–5](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par4)
and [par6–7](https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082#par6).

The source graph preserves each exact passage, witness, URL, status and
confidence. Lemma I-to-II is an explicit high-confidence citation. II-to-III
retains the high-confidence implicit `Eædem rationes ultimæ` inference; III-to-
Corollary 1 retains `Hinc`. New formal references support the finite geometric
and exhaustion steps without certifying the historical area-ratio conclusion.
Neither edition supplies a premise to the other or to De Motu.

## Construction and bounds

`MonotoneRectangles.Partition a b` has a positive finite count, ordered nodes,
and endpoint equality by Fraction.equiv. Repeated nodes and zero widths are
allowed. `node_bounds` and `partition_cover` derive the range and coverage,
including the last endpoint. `MonotoneOn` is local to the fixed interval;
there is no global graph regularity premise.

`rectangle` and `figure` are explicit rational planar point sets.
`lowerFigure` and `upperFigure` are the actual finite rectangle unions, using
the left and right endpoint ordinates respectively. `figure_enclosure`
derives lower union ⊆ graph region ⊆ upper union from monotonicity and
coverage. `completed_enclosure` transfers both inclusions through metric
closure to every completed point of these regions.

The finite `lowerSum` and `upperSum` multiply each actual width by its actual
endpoint height. Their nonnegativity follows from nonnegative initial height
and graph monotonicity. `gap` is their difference, not a freely supplied
error. `gap_identity` expresses it as the sum of width × ordinate increment.
The canonical rational sum kit supplies nonnegativity, common-factor
distribution and telescoping. Endpoint ordinate equality is derived from
local monotonicity and the partition's represented endpoint equality.

`maxWidth` selects the largest actual finite width. `maxWidth_bounds` proves
it bounds every cell and lies below every common width bound. It is not a
field naming a desired budget. `gap_equal_width` proves Lemma II's exact
common-width × total-height identity. `gap_bound` gives the nonnegative
unequal-width gap bound of Lemma III. `gaps_vanish` exhausts this derived gap
under shrinking actual maximum widths, including zero total height.
The separately named 1687 and 1713 wrappers combine completed set enclosure,
nonnegative sums, the maximum-width bound and its exhaustion.

## Controls and boundary

The scope harness uses a curved quadratic graph. With unequal nodes 0,1,3,
the actual lower/upper sums are 2 and 19, gap 17, maximum width 2 and budget
18. A point (2,3) belongs to the graph region and upper union but not the
lower union. Raw 0/2 and 2/2 endpoint aliases test represented equality and
the equal-width formula. Actual dyadic partitions derive their widths and
maximum-width exhaustion before instantiating the theorem. Zero-width
partitions retain their vertical point sets and have zero sum gap.

A polynomial hump has zero endpoint rectangle gap but a positive interior
ordinate outside the upper rectangle. Its failed monotonicity and failed
enclosure are proved. This prevents scalar gap exhaustion from silently
standing in for the geometric inclusion.

These are side-product sums and explicit point-set inclusions. Their
identification with ordinary area of geometric unions, area additivity,
realization of the curvilinear figure's area and the ultimate equality ratio
remain open. A ratio conclusion also needs an explicit nonzero-area premise;
the zero-width/zero-height gap controls do not assert a ratio at zero. No Cauchy area value is constructed here. The graph and shrinking
partitions are supplied geometric data; this does not construct a force
motion or identify its tangents. Tangent existence/vertical patches,
ordinary sector-union area and unrestricted historical force remain separate.
Kepler stays held until the general proof requirements are met.

Next: connect the rectangle side-product sums to ordinary union area and
realize the given curvilinear area between them, before applying Lemma I to
that actual area quantity, making the nonzero-area requirement for ratios
explicit. Do not rename a supplied scalar squeeze as this
construction.

## Verification

One independent sequential gpt-6-luna verifier ran all 16 README commands,
the rectangle scope harness and the retained supporting-boundary harness;
all exited 0. The API audit against HEAD f753c6b retained all 2,211 prior
public names and signatures, with 29 additions. Catalogue inventory: 1,727
theorems; progress count: 1,706 library theorems at f753c6b. Graph: 88 nodes,
87 edges, 253 passages and 1,582 Lean references. Lemma I-to-II remains an
explicit high-confidence edge; II-to-III and III-to-Corollary 1 remain
implicit high-confidence edges with their separate witnesses and passages.
Only propext, Classical.choice and Quot.sound occur. No source
sorry/admit/project axioms/Mathlib, external packages or reversed BarrowLib
imports appear.

The result concerns a nondecreasing rational graph on a fixed rational
interval, its metric closure, and finite side-product sums. Descending patches
require an explicit coordinate change; no invariance theorem is claimed for
them. There is no arbitrary completed ordinate-valued graph or actual sector
chart theorem. Ordinary rectangle-union area/additivity, completed
curvilinear-area realization and the ultimate ratio remain open; zero-gap
controls do not assert a ratio at zero. Logs: /tmp/newton-sol61-rect-final-01.log
through -16.log; scope /tmp/newton-sol61-rect-scope-final.log; retained
support scope /tmp/newton-sol61-rect-support-scope-final.log; API
/tmp/newton-sol61-rect-api.json. Final `git diff --check` passed. Conversation
exports remain excluded.
