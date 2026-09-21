# Research state

The approved governing target is now the three-stage formalization of
De Motu, 1687 and 1713 arguments corresponding to Book I, Section II,
Propositions I–IV: see [goals](GOALS.md). M1–M4 below are supporting work.
The first new obligation is finite joining versus trajectory realization;
the action-constant hypothesis remains separate and unproved.

New finite diagnostic: `Polygon/Contact.lean` now compiles with explicit
position/velocity/impulse contact, restriction of supplied samples, and finite
gluing results. `motion_restart` proves exact continuation from the current
vertex pair with shifted impulses. The lattice construction derives the
velocity jump and zero-impulse velocity contact, rather than assuming them.
Its counterexample gives equal swept sums and unequal next vertices under
two different inward impulse histories (-1 and -2). It establishes insufficiency
of area data for identification, not failure of existence or fixed-force
uniqueness. Continuous-time refinement and mechanical realization remain open.

The [Section II source map](SECTION_II.md) now identifies printed I–IV
dependencies and De Motu antecedents for I and IV. Counterparts of II/III
were not found in the inspected De Motu ranges; this is not an edition-wide
absence claim. Proposition IV's explicit route differs between 1687
(Proposition II, Lemmas V/XI) and 1713 (Proposition II, Proposition I corollaries
2/4, Lemma VII). See the [ordered obligations](TASKS.md) for continuation.

The implementation request authorizes M1–M4 beyond the earlier M1-only boundary.
Scope stays within the requested changing proof architecture. Lean 4.19.0,
core/Std only; external dependencies remain empty.

| Milestone | Checked progress | Remaining completion barrier |
| --- | --- | --- |
| M1 | Independent H4 edited witness; rational consistency model; constructed s/t² and triangle normalization; conditional bridge and force-coefficient algebra; TEI/page-anchor collation | Direct image inspection and earliest H4 chronology; curved contact construction; mechanical velocity-area enclosure; variable-force corollaries |
| M2 | Constructed finite polygon, equal-area sums, maximum-width rectangle bound, conditional sector-ratio transfer | Geometric refinement connecting the constructed polygon family to an enclosed curve; continuous-force trajectory identification is a separate open issue |
| M3 | Conditional contact/cubic inequalities, finite sums, rectangle-derived 1/2 and 1/3 coefficients, reciprocal error convergence, rational uniform N^-2 bound | General curved contact geometry and mechanical identification of the velocity-area construction |
| M4 | C44 identity; evidence-qualified proposed outline; actual-edition DAGs and generated comparison; matched constant-force route algebra; TEI/page-anchor collation including 1726 views | Direct C42 and draft-folio/image collation; general generated/sagitta limiting comparison |

**M1–M4 are not certified complete.** Compiling conditional theorems and four
reports do not discharge their displayed geometric and historical premises.
See M1.md through M4.md and formal-results.json for exact boundaries.

Sources: TEI is the machine-readable authority; identifying translations and
untranslated passages are labelled. The source-collation report records page
and facsimile targets without downloading or reading manuscript images.
Selected PDF passages were visually checked; no general manuscript-image audit
is claimed. See [collation](collation.md) and edition-comparison.md.

Validation commands are in README.md. No sorry or project axioms were added;
standard Lean logical axioms can appear in generated dependency inspection.

Unrelated conversation-export deletion/new file remain untouched. No mathlib,
cache download, toolchain upgrade, correspondence or publication was performed.
