# Primary witnesses and source coverage

M1 originals are in docs/m1; additional revision/1726 sources are in docs/m4. Read [passages.md](passages.md) for
marked Latin and stable paragraph links. Metadata and hashes accompany each
XML. Mechanical extraction preserves deletion/addition boundaries and does
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
  archived TEI with same-stem companions. selections.json identifies coverage.
- Rouse Ball's edited Royal Society-copy reprint, pp.35–37: independent H4
  numbering, visually checked; direct earliest manuscript chronology unresolved.
- NATP00087: 1726 Book I TEI, selected chain in docs/m4, separate from 1713.
- Gregory C44 edited Latin: separate-booklet proposal and manuscript identity
  checked visually. **Not** C42; the latter's direct text remains a source gap.
- Brackenridge's publisher edition, chapter 8 and notes: secondary locator
  digest for projected numbering, not a direct draft-folio collation.

See docs/m4 companions for retrieval failures and exact coverage;
imported-premises.json for source-linked Euclidean, conic, contact and mechanical
premises; formal-results.json for checked signatures and historical boundaries.
Source hashes record byte identity, not source truth or proof verification.
