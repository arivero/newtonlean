# Primary witnesses and source coverage

M1 originals are in docs/m1; additional revision/1726 sources are in docs/m4.
Historical Lean files contain marked Latin, stable paragraph links and witness
hashes. The TEI headers carry source metadata; docs/SHA256SUMS checks archive
identity. Mechanical extraction preserves deletion/addition boundaries and does
not constitute a manuscript-image audit.

| Stage/witness | Primary source | M1 anchors |
| --- | --- | --- |
| Revised De motu in gyrum, NATP00089 | https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00089 | par19: Hyp 1 revised to Lem 2; par7 composition |
| De motu sphaericorum, NATP00090 | https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00090 | par12–13: Lemma 2 and geometric proof; par27 citation |
| Principia 1687 Book I, NATP00077 | https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00077 | par25–28: Lemmas IX and X |
| Principia 1713 Book I, NATP00082 | https://www.newtonproject.ox.ac.uk/view/texts/diplomatic/NATP00082 | par26–34: Lemmas IX and X, corollaries |

Identifying snippets: 1687 uses “vi regulari”; 1713 uses “Vi finita”.
Both Lemma X proofs cite “per Lemma IX”. NATP00089's local-force annotation
changes “Hyp 1” to “Lem. 2”. These observations do not date every manuscript
layer or identify a complete first-state H4.

English Motte/Chittenden 1846 and Motte/Wilkins 1729 reading aids remain in
../navstokgap/docs. They are not substitutes for the 1687 Latin witness.
The original M1 pass excluded 1694; the authorized M4 additions below now cover selected revision evidence.

See [M1.md](M1.md) for translations, classification, confidence, additional
premises, and outstanding first-state witness identification.

## M1–M4 implementation additions (2026-09-21)

The previous M1-only inventory above records the earlier scope. The current
request authorizes the following additional witnesses and selected passages:

- NATP00075/76 and NATP00080/81: definitions and laws for 1687 and 1713,
  archived TEI with same-stem normalized and diplomatic HTML views.
- Rouse Ball's edited Royal Society-copy reprint, pp.35–37: independent H4
  numbering, visually checked; direct earliest manuscript chronology unresolved.
- NATP00087: 1726 Book I TEI, selected chain in docs/m4, separate from 1713.
- NATP00085 and NATP00086: 1726 Definitions and Laws TEI in docs/m4, retrieved
  5 October 2026; anchors par10, par18 (Definitions) and par8, par25 (Laws).
- Gregory C44 edited Latin: separate-booklet proposal and manuscript identity
  checked visually. **Not** C42; the latter's direct text remains a source gap.
- Brackenridge's publisher edition, chapter 8 and notes: secondary locator
  digest for projected numbering, not a direct draft-folio collation.

See docs/m4 companions for retrieval failures and exact coverage;
the milestone/source notes and historical Lean sections for source-linked
Euclidean, conic, contact and mechanical premises and checked proof boundaries.
Source hashes record byte identity, not source truth or proof verification.

## Archived edited reprint

The retained [Rouse Ball extract](../docs/m1/rouse-ball-demotu-pp35-37.pdf)
contains printed pp.35–37 of *An Essay on Newton's Principia* (Macmillan, 1893),
extracted from [scan pages 49–51](https://rcin.org.pl/impan/Content/235304/6087.pdf#page=49)
on 21 September 2026. Page 36 was visually checked for Hypothesis 4's wording
and numbering. Rouse Ball declares corrections to diagrams and clerical errors,
modernized punctuation and multiplication notation on p.35. This edited reprint
is independent of NATP00089; direct manuscript collation and earliest-state
chronology remain open. The historical text is public domain; scan markings
remain, without a claim about a separate license for the scan. The PDF is a
three-page extraction, not the complete book. Its hash is in docs/SHA256SUMS.
