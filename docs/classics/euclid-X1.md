# Euclid, Elements X.1: exhaustion by repeated subtraction

Author: Euclid. Witness: original Greek transcription hosted by Dimitrios E.
Mourmouras at NTUA, identified by the page as the Evangelos Stamatis edition
(ΟΕΣΒ, 1953). This is an online edited-text witness, not a manuscript image.

Source: [Book X, Proposition 1](https://physics.ntua.gr/mourmouras/euclid_desktop/book10/postulate1.html).
Retrieved 9 October 2026; downloaded HTML retained as [euclid-X1.html](euclid-X1.html),
with its SHA-256 in [the archive checksums](../SHA256SUMS).
The ancient text is public domain. The site's notices are retained; no
separate license for its transcription, layout or images is asserted here.

The selected result says that repeatedly removing more than half of the
larger magnitude eventually leaves less than the given smaller magnitude.
The proof first takes a multiple of the smaller magnitude exceeding the
larger. Its final sentence expressly includes exact halves:

> ὁμοίως δὲ δειχθήσεται, κἂν ἡμίση ᾖ τὰ ἀφαιρούμενα.

Locator: the heading `Πρότασις α΄. [1]`, statement in the following `h3`, and
final proof paragraph beginning `Καταλείπεται ἄρα`. In the preserved HTML,
these occur at lines 597–608. The complete selected statement and closing
sentence are quoted in [MagnitudeContent](../../BarrowLib/Polygon/MagnitudeContent.lean).
[Joyce's English translation](https://mathcs.clarku.edu/~djoyce/elements/bookX/propX1.html)
is a reading aid; its modern commentary supplies no formal premise.

Reading coverage: the proposition's statement and whole Greek proof were
read from the archived HTML, including the closing paragraph omitted from
the web tool's main extraction. Browser text extraction and direct HTML
inspection were used. The linked diagram and the 1953 printed page have not
been collated visually. No OCR or independent translation was undertaken.

The source-to-model step is an **editorial interpretation**, confidence high
for this specialization: comparable area magnitudes, a positive area unit,
and its rationally represented unit halves give `Rules.unit_halves_exhaust`.
This remains a supplied field for arbitrary `Q`; only its rational instance
is proved here. The source is not credited with the project's pullback proof
or exact typed interface. No Newton citation of X.1 is asserted.

This premise transfers an already proved rational gap exhaustion to the
supplied magnitude domain. Addition and order then give approximation to
any supplied area magnitude, without requiring that magnitude to be rational.
No general curved-area existence or Eudoxian ratio theorem follows from this
implementation. See [Book V definitions](euclid-V.md) for the comparability
boundary and [the theorem report](../../THEOREM_CASCADE.md) for proof provenance.
