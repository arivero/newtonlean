# One historical result per file

Requested by the user on 6 October 2026, after the given-motion consistency
increment `85a76ec`. The design and starting inventory are retained below; the executed working-tree
migration is recorded in the final section.

## Unit of organization

The main library is a readable formal edition of Newton's arguments. Each
historical file owns exactly one historical result across its witnesses: a theorem,
proposition, lemma, law or corollary, with its own definitions and proof.
A historical statement can require several Lean declarations. Counting one
Lean `theorem` per file would fragment the very proof we want to read.
Reusable auxiliary mathematics belongs in a supporting library, not in a
second unrelated historical result inside the same file.

The user selected **one file per historical result, with separate edition
sections**. Each section contains its own Latin and separately named
formalization. Keep De Motu's two witnesses, 1687 and 1713 distinct, including
their different premises and citations. Proposed 1694 and 1726 remain
supporting comparisons. A shared file does not license a shared historical
premise or retrospectively number De Motu as a Principia proposition.

The layout is:

```text
NewtonLimitDynamics/Historical/
  AreaLaw.lean               # De Motu Theorem I; 1687/1713 Proposition I
  CompositionOfMotions.lean  # De Motu lemma/hypothesis; Laws Corollary I
  LemmaI.lean                # ultimate equality, separate printed editions
  LemmaII.lean
  LemmaIII.lean
  LemmaIII/CorollaryI.lean
  LemmaIII/CorollaryII.lean
  LemmaIII/CorollaryIII.lean
  LemmaIII/CorollaryIV.lean
BarrowLib/                   # elementary arithmetic, ratios, finite geometry, exhaustion
ClassicsLib/                 # identified source-backed classical results, e.g. Euclid
ModernLib/                   # post-Newtonian concepts and modern reconstructions
```

Within `AreaLaw.lean`, for example, use explicit sections for NATP00089,
NATP00090, 1687 and 1713, preserving the existing separately qualified
names where possible. The De Motu sections must be headed Theorem I, not
Proposition I. Every section owns its source text, definitions/premises,
proof and limits; do not put a merged Latin statement above a single proof.
Dependencies on other historical results import their one canonical file
but call only the justified witness-specific declaration.

The user's later 6 October clarification permits anachronical proofs in the
same result file. Primary proofs use BarrowLib, ClassicsLib and untainted
historical results. Place anachronical proofs after the primary witness
sections, below this exact form of comment header:

```lean
/-
===============================================================================
===============================================================================
===============================================================================
===============================================================================
===============================================================================
ANACHRONICAL PROOFS
-/
```

Keep witness subsections within that separate section. They may use ModernLib.
An anachronical result taints every downstream proof that uses it, including
through a type, private helper or another historical document. Importing a
file with both sections does not taint an otherwise independent primary
proof. This clarification supersedes starting-inventory suggestions that
all edition-specific modern wrappers must leave historical files.

This describes ownership, not completed proofs. A result awaiting proof has
its Latin text, the exact checked partial reconstruction, and explicit open
obligations; never a `sorry` or a theorem-shaped axiom standing in for Newton.
A historical hypothesis is labelled as a hypothesis, not converted into a
proved law. The NATP00089 composition passage is such a case.

## Contents of a historical file

1. Result identity, edition/witness, local TEI path and source hash, exact
   statement and proof anchors, source URL and textual-layer convention.
2. The complete Latin statement and Newton's proof for this result. Preserve
   original spelling, punctuation and textual variants; do not silently
   repair apparent errors. Revisions in manuscripts remain marked. Keep
   headings/figure references and consult the original for formula layout.
3. A short correspondence between the Latin proof steps and the Lean
   declarations below. For each imported historical dependency retain the
   exact passage, witness, URL, classification and confidence already required
   by AGENTS.md. An import used for computation is not automatically a
   historical citation by Newton.
4. Local definitions and explicit premises, followed by the checked proof
   or accurately delimited partial reconstruction. State which definitions
   are modern representations and which premises remain unproved.
5. A precise status boundary. In particular, finite triangle sums, swept fans,
   geometric sector area, between-path outer content and planarity are distinct.

Latin should be embedded as readable Lean documentation and checked against
an explicit diplomatic rendering of the archived TEI. The existing
`scripts/catalogue_m1.py:render` already preserves orig rather than joining
orig and reg, and marks additions/deletions/notes/unclear readings. Reuse and
test that extraction rule rather than introduce a second transcription.
TEI `fw` elements are page furniture and catchwords: omit them from the
running-text rendering while preserving their following text. The original
TEI and its hash remain intact. In particular, this removes the duplicated
catchword/page number from NATP00090 par17; the suspicious 1713 reading
`Ipsi S BS` remains unchanged because it is the TEI's body text.
Whitespace presentation can be normalized only if documented; the TEI stays
the machine-readable authority. A check must fail when embedded Latin drifts
from its selected source. Literal TEI fragments or their hashes preserve the
source boundary where plain text cannot represent the layout faithfully.

## Supporting-library boundaries

| Library | Mathematical responsibility | Important boundary |
| --- | --- | --- |
| BarrowLib | Elementary rational arithmetic, ratios, finite sums/products, coordinate geometry, elementary exhaustion arguments | A generic name does not make a modern concept elementary. Lean's implementation language alone does not make an elementary result post-Newtonian. |
| ClassicsLib | A source-identified classical proposition used as mathematics, such as a proved Euclidean area or parallel-line result | Do not label a determinant identity “Euclid” merely because it proves a familiar geometric fact. Identify the classical proposition and its proof first; its arithmetic implementation may use BarrowLib. |
| ModernLib | Cauchy names and quotient completions, completed time/position/scalar operations, topology of completed values, Lipschitz-oracle reconstruction and modern motion/area comparison | Put the new given-motion consistency machinery here as a modern reconstruction. Newton-facing use must retain its modern status and extra premises. |
| Historical main library | Newton's actual result, own definitions and stage-local argument, with exact Latin | No unrelated diagnostic, generic utility or unlabelled modern replacement proof. |

Acyclic intended dependencies: ClassicsLib uses BarrowLib where needed;
ModernLib uses the elementary/classical libraries; Newton's result files
use the libraries and the historical dependencies appropriate to their own
stage. Supporting libraries must not import historical result files. Modern
reconstructions may be exposed from historical files only with explicit
status, not presented as the missing historical proof.

The old boundary in `BARROWLIB_BOUNDARY.md` expressly permits modern Cauchy
infrastructure in BarrowLib. The new user direction changes that boundary;
it must be revised during migration, not cited as a reason to keep completions
there. Do not move all coordinate geometry into ClassicsLib without a source
identification, nor reclassify a modern reconstruction as classical because
it lacks calculus syntax.

## Inventory at 85a76ec

There are 66 BarrowLib implementation modules and 95 NewtonLimitDynamics
modules (including compatibility facades). Thirteen files occupy the three
primary historical-stage directories. Principal ownership problems:

| Current file(s) | Required separation |
| --- | --- |
| `DeMotu1684/AreaLaw.lean` | Move into the shared area-law file with separate NATP00089 and NATP00090 sections. Retain each witness's own composition premise and limiting passage. Supporting constructed-area/boundary clients belong in ModernLib. |
| `DeMotu1684/Composition.lean` | NATP00090 Lemma I is a proved historical argument; NATP00089 par7 is a revised hypothesis. They must not share an undifferentiated historical result file. |
| `DeMotu1684/QuadraticDeflection.lean` | A formal premise interface, not a completed historical theorem. Attach the source hypothesis to its historical context; move the abstract modern interface out of the main historical narrative. |
| Both `Principia*/Laws.lean` | These currently formalize Corollary I, not the whole laws section. Put them in separate sections of the one composition-result file, each with its own exact Latin. |
| Both `Principia*/LemmaIII.lean` | These contain Lemma II's equal-width argument, Lemma III's unequal-width argument, and chord/supporting/perimeter corollary work. Split by actual result. Shared finite geometry and modern completed-boundary clients belong in supporting libraries. |
| Both `Principia*/PropositionI.lean` | Keep Proposition I and its own proof steps; move constructed-curve implementation and generic defect-control machinery to ModernLib. A checked modern application may remain explicitly cited, never silently promoted to historical completion. |
| Both `Principia*/LemmaX.lean` | Preserve separate historical arguments and Latin. Move generic enclosure/bridge machinery out; do not import a De Motu premise merely to share an abstract type. |
| `Principia1687/ConstructedRatio.lean` | This is supporting enclosure machinery, not a separately numbered historical result. Move to the appropriate supporting library. |
| `Principia1713/ForceComparison.lean` | Corollaries IV and V require separate historical result files, each with its edition sections. Generic quotient/generated-coefficient algebra is support, not a proof of the finite-time force law. |
| `BarrowLib/Polygon/CauchyValues.lean`, `BinaryTime.lean`, `PositionValues.lean`, completed-value/area/content clients | Move the completion-dependent chain to ModernLib in dependency order. Keep finite dyadic arithmetic and elementary inequalities below it. |
| `NewtonLimitDynamics/Polygon/*`, `Comparison/*`, `Diagnostic/*` | Inventory actual mathematical content. Move elementary support to BarrowLib, source-identified classical mathematics to ClassicsLib, and modern models/diagnostics to ModernLib; do not classify solely by directory or filename. |

The Latin passages for the immediate dependency chain were reread locally:
NATP00077 par3–10, par44–45; NATP00076 par7–8; the separately archived
1713 law file is NATP00081. De Motu NATP00089 par7–9 and NATP00090 par10–11
retain the hypothesis/lemma and revision distinctions above. No new historical
dependency is inferred from this file inventory.

## Migration order and acceptance

1. Implement the chosen one-result/multiple-edition layout, write a source/result manifest, and
   provide source-checked specimens for the area law and its immediate
   Laws Corollary I dependency. Preserve all existing declarations while
   moving their ownership; avoid wrapper proliferation.
2. Extract the modern completion chain from BarrowLib, then the modern Newton
   clients. Register `ModernLib` as a real build target. Update catalogues,
   inventories, source-reference checks, dependency checks and progress tools
   so moved declarations are still counted exactly once.
3. Identify and source the classical facts actually used by those proofs;
   add ClassicsLib with checked content rather than a renamed bag of geometry.
4. Split historical mixed-result files in the Proposition I dependency order:
   Laws Corollary I; Lemmas I–III and their separately identified corollaries;
   Proposition I. Repeat with separate evidence for 1687 and 1713, and keep
   De Motu's own route. Supporting Lemma X work follows without merging stages.
5. Remove obsolete historical facades or move compatibility imports outside
   the result tree. Preserve fully qualified Lean names where practical and
   document unavoidable API changes. Do not keep duplicate proofs solely to
   preserve old paths.

Every migrated increment must pass the full existing 16-check list, the
historical-unit/embedded-Latin check, the new library builds when registered,
and an API/import-boundary audit. No mathematical completion score increases
because files moved or Latin was embedded. The migration is complete only
when every main historical file has one manifested result and the checked
source text of each included witness, and support has no backward imports into those files.

## Design checkpoint

The preceding mathematical increment `85a76ec` is verified and pushed.
This design introduces no Lean changes. All 16 existing checklist commands
passed on the design checkpoint; logs are
`/tmp/newton-sol61-refactor-design-01.log` through `-16.log`.
The selected layout is recorded in AGENTS.md and GOALS.md. Migration and new
library targets are still pending; no proof-completion credit is added.

## Executed migration, 6 October

The complete existing Lean implementation has been reorganized in the working
tree for ultracorrection review. No refactor commit or push has been made.
The earlier design and inventory above remain a record of the starting layout.

There are now 19 one-result historical files with 67 source-checked paragraph
anchors. Each witness section contains diplomatic Latin, source path, hash,
URL, proof-step correspondence and the already recorded dependency edges
with their classifications and confidence. The result catalogue and
[historical index](HISTORICAL_INDEX.md) distinguish checked partial statements
from text-only open obligations. De Motu keeps its two manuscripts and their
own numbering; printed editions keep separate names and premises.

The retained public statements live in 39 elementary BarrowLib modules,
three ClassicsLib modules and 109 ModernLib modules, plus the 19 historical
files. The finite calibration and tolerance arithmetic, and rational
monotone-rectangle geometry, were separated from their Cauchy/closure clients.
ClassicsLib owns the existing integer-coordinate special cases of Euclid
I.37/I.38, with source links and limits. It does not claim to prove those
synthetic propositions in full. The modern Cauchy, completed-value, force
construction and diagnostics live in ModernLib. Edition-specific conditional
area clients remain in AreaLaw's anachronical section. The manifest partitions
43 historical declarations into 25 primary and 18 anachronical declarations;
these include definitions and partial results, not 25 completed Newton proofs.
No supporting library imports a historical result file.

All 2,252 public declarations are retained, with nine intentional renames in
[declaration-renames.json](declaration-renames.json). Lemma I/II namespaces now
match their own result. Lemma II's two equal-width names change accordingly;
four combined II–III/Corollaries III–IV reconstructions are generic modern
support rather than proofs owned by one historical result; three generic
quadratic/coefficient names lose misleading historical ownership. Other
qualified names are unchanged. Statements and proof/definition bodies are
unchanged after applying that map. Old import-only facades were removed. Module import paths
intentionally change; [module-migration.json](module-migration.json) records
old-to-new ownership, including split modules. The old one-module build API
should be migrated using that map; the aggregate `import NewtonLimitDynamics`
still exposes the complete declaration API under the recorded renames.

Elementary historical wrappers were returned from ModernLib to their owning
result files, and their finite support closure was moved to BarrowLib or the
source-identified ClassicsLib lattice model. A historical namespace does not
by itself justify elementary placement: completion-dependent proofs retain
their anachronical status.

The compiled ledger currently finds no cross-file use of a manifested
historical declaration. Its 75 source-evidenced proof dependencies are all
still without a detected formal use: 26 have a source result outside the current historical
files, 41 have no primary source formalization, five have no primary target
formalization, and three have no primary declaration use. These counts expose
the interface gap; they do not invalidate Newton's source dependencies or
turn comments into checked proof steps. The next mathematical work must
derive the needed interfaces from the corresponding historical lemmas.

### Verification tools

- `scripts/check_architecture.py` checks one-result ownership, declaration
  section membership, source hashes/URLs, exact embedded diplomatic text,
  duplicate public declarations, import existence/cycles and library boundaries.
  It also checks the five-line separator, primary/anachronical ownership,
  Lemma I/II namespaces and absence of combined-result historical theorem names.
  It is a local provenance/architecture check, not a historical proof certificate.
- `scripts/test_architecture.py` checks known running-text examples and rejects
  eight corruptions, including catchword reinjection, a missing separator,
  wrong lemma namespace and false primary classification.
- `scripts/check_migration_api.py` compares public names, normalized statements
  and bodies against `9f3ec58`. With `--kernel` it also builds an isolated old
  checkout and compares every printed declaration type to the working tree,
  after the nine declared renames and joining only printer continuation lines.
- `scripts/proof_dependencies.lean` inspects compiled types and proof/definition
  bodies, including generated/private constants. `scripts/check_proof_layers.py`
  propagates taint from ModernLib and explicitly anachronical historical
  declarations. It rejects tainted primary declarations and emits
  [proof-dependencies.json](proof-dependencies.json), keeping actual kernel
  uses separate from the quoted source-evidence edges. No detected modern
  dependency means only that: supplied interfaces can still hide unfinished
  historical proof obligations. `scripts/test_proof_layers.py` includes a
  compiled private-bridge control, type-only use, transitive cross-document
  use and cyclic dependency controls.
- `catalogue_formal.py` now inventories four libraries and emits the historical
  navigation index. Declaration origins preserve source attribution across
  moves. `progress_stats.py` recognizes all four libraries at future commits;
  old snapshots retain their historical paths. The declaration reader now
  recognizes `private noncomputable` correctly, with a regression control.
- Existing verification harness imports follow the relocated modules. The
  old archived source hashes and the historical dependency graph are unchanged.

The final verification record is
[historical-file-refactor-2026-10-06.md](verification/historical-file-refactor-2026-10-06.md).
This migration adds no theorem, axiom or proof-completion credit. New historical
files for missing portions contain their exact source and open status; they
introduce no theorem-shaped placeholder.

### Tool update, 6 October review corrections

The existing renderer and architecture/API tools were patched rather than
replaced. The new instrument answers a previously unchecked question: which
compiled constants does a primary declaration actually use, and does any
dependency path reach an anachronical result? Counts of files, imports and
source comments cannot answer it. The negative controls above check that the
instrument detects intentionally planted violations. This is provenance
verification, not an independent proof of the mathematical premises.

After changing the rendering rule, regenerate source text deliberately with
`python3 scripts/catalogue_m1.py --refresh-historical`, then run the normal
source/formal catalogues and graph check. For ordinary review, run
`python3 scripts/check_proof_layers.py --report research/proof-dependencies.json`
and `python3 scripts/test_proof_layers.py` after the architecture checks. The
manifest hash and compiled-graph hash identify the ledger's inputs.
