# Euclid, Elements V, definitions 2, 4 and 5

Author: Euclid. Witness: original Greek transcription hosted by Dimitrios E.
Mourmouras at NTUA, whose navigation identifies the Evangelos Stamatis edition
(ΟΕΣΒ, 1953). This is an edited-text transcription, not a manuscript image.

Source: [Book V, definitions](https://physics.ntua.gr/mourmouras/euclid/book5/elements5.html).
Retrieved 9 October 2026; original HTML: [euclid-V.html](euclid-V.html).
Its SHA-256 is recorded in [the archive checksums](../SHA256SUMS).
The ancient text is public domain; the site's notices remain intact.
No separate license for the online transcription or layout is asserted.

Definition 2 describes a multiple:

> Πολλαπλάσιον δὲ τὸ μεῖζον τοῦ ἐλάττονος, ὅταν καταμετρῆται ὑπὸ τοῦ ἐλάττονος.

Definition 4, following the heading `Ὅροι ιη΄ [18]`, is the comparability
condition used in reading X.1's first proof step:

> Λόγον ἔχειν πρὸς ἄλληλα μεγέθη λέγεται, ἃ δύναται πολλαπλασιαζόμενα ἀλλήλων ὑπερέχειν.

Definition 5 describes equal ratios through matching comparisons of
equimultiples:

> Ἐν τῷ αὐτῷ λόγῳ μεγέθη λέγεται εἶναι πρῶτον πρὸς δεύτερον καὶ τρίτον πρὸς τέταρτον, ὅταν τὰ τοῦ πρώτου καὶ τρίτου ἰσάκις πολλαπλάσια τῶν τοῦ δευτέρου καὶ τετάρτου ἰσάκις πολλαπλασίων καθ᾿ ὁποιονοῦν πολλαπλασιασμὸν ἑκάτερον ἑκατέρου ἢ ἅμα ὑπερέχῃ ἢ ἅμα ἴσα ᾖ ἢ ἅμα ἐλλείπῃ ληφθέντα κατάλληλα.

Locators: paragraphs labeled `β΄ [2]`, `δ΄ [4]` and `ε΄ [5]`, archived HTML
lines 669, 673 and 675. The site's numbered anchors come at paragraph ends;
use the definition labels when checking the quotations.

Reading coverage: these three definitions were read in the downloaded HTML
and checked against the web text extraction. Other propositions in Book V
and printed-page images were not reviewed in this increment. No OCR or
independent critical-text collation was undertaken.

Source-to-model status: **editorial_interpretation**, confidence high for
the comparability/ratio distinction. Definition 4 explains the same-kind
magnitude boundary behind the supplied [X.1 specialization](euclid-X1.md).
Definitions 2 and 5 provide the language for the integer-multiple comparisons
now proved in [MagnitudeContent](../../BarrowLib/Polygon/MagnitudeContent.lean).
For each fixed positive integer pair `n<m`, both `nX<mY` and `nY<mX` hold
eventually. This is an editorial encoding of an ultimate unit ratio, not
Euclid's sequence-limit definition, exact finite equality under V.5, or a full
ratio calculus. Repeated addition is defined; weak addition compatibility
and preservation of strict rational comparisons are visible supplied laws,
realized by the rational instance. The limit conclusion is proved from
enclosures, an eventual positive rational bracket and shrinking finite gaps.
The abstract `positive` predicate is not identified with order positivity;
no separate theorem `positive A` is claimed. No definition supplies general
curved-area existence, order completeness or a nonrational model.
