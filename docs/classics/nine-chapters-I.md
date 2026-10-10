# 九章算術 — 卷第一 方田, scan pages 13–25 of Sibu Congkan0390-劉徽-九章算術-3-1.djvu

Anonymous base text; transmitted with 魏劉徽注 and 唐李淳風等奉敕注釋.
Witness: **四部叢刊本**, whose heading identifies the photographic exemplar as
景上海涵芬樓藏微波榭刊本. This is a later printed witness with a modern Chinese
Wikisource transcription, not an ancient manuscript or a critical edition.

Source: [fixed page revision 2658134](https://zh.wikisource.org/w/index.php?oldid=2658134).
Retrieved 10 October 2026. Original rendered HTML: [nine-chapters-I.html](nine-chapters-I.html).
SHA-256: `617c46d63cdc51f6c3c7bceb5f0909b4bef8d5ab3bcc32aaf788f84623921599` (also in [the archive checksums](../SHA256SUMS)).
The ancient text is public domain; the archived Wikisource notices, attribution,
revision links and CC BY-SA 4.0 statement remain intact.

Reading coverage: the selected fraction rules or 正負 clauses and their adjacent
annotations were read in the rendered HTML and web extraction. Small-type
annotations are separated from the rule text below. Scan page links in the HTML
locate the passages; their transcription quality flag is 1 (not proofread).
No independent scan collation, OCR correction or whole-book review is claimed.
The revision URL fixes the containing page, while transcluded scan-page text
can change independently; the archived bytes and SHA identify the version used.

## Rule text (術), with commentary removed

Line wraps are joined. Characters are retained, including 乗 in 課分.
The 合分 quotation is an excerpt: the final same-denominator clause is
outside the encoded two-fraction rule and is not silently reconstructed
from the image used for its rare character in the transcription.

- **約分術**: 術曰可半者半之不可半者副置分母子之數以少減多更相減損求其等也以等數約之
- **合分術** (excerpts): 術曰母互乘子并以爲實母相乘爲法 / 實如法而一不滿法者以法命之
- **減分術**: 術曰母互乘子以少減多餘爲實母相乘爲法實如法而一
- **課分術**: 術曰母互乘子以少減多餘爲實母相乗爲法實如法而一卽相多也
- **平分術**: 術曰母互乘子副并爲平實母相乘爲法以列數乘未并者各自爲列實亦以列數乘法以平實減列實餘約之爲所減并所減以益於少以法命平實各得其平
- **經分術**: 術曰以人數爲法錢數爲實實如法而一有分者通之重有分者同而通之
- **乘分術**: 術曰母相乘爲法子相乘爲實實如法而一

The cross-products for 減分 have the smaller removed from the larger. 課分
computes the excess as well as comparing; the Lean iff isolates comparison
and is classified R. 平分 uses the number of entries, not an implicit two;
Lean records conservation and redistribution to their mean for a nonempty
list of positive parts. It does not simulate the common-denominator array.
經分 divides the money by the people, both possibly fractional. These roles
are preserved in the dividend/divisor order.

## Commentary witness, separate from 術

The small-type annotation after 約分 says:

> 等數約之卽除也其所以相減者皆等數之重疊故以等數約之

The earlier explanation gives two equivalent representations:

> 設有四分之二者繁而言之亦可爲八分之四約而言之則二分之一也雖則異辭至於爲數亦同歸爾

These are commentary, not added words in the rule. The witness also has later
annotations explicitly introduced by 臣淳風等謹按; those are not labelled Liu Hui
merely because they appear in the same edition. No critical collation of
unmarked commentary layers was undertaken.

## Source-to-model correspondence

[FractionRules.lean](../../ClassicsLib/NineChapters/FractionRules.lean)
restricts chapter-I fraction inputs to positive numerators and denominators.
The common-measure definition executes the subtraction branch, with positive
termination; its identification with `Nat.gcd` is R. Dividing both parts by
that measure preserves value, and optional simultaneous halving is verified
separately in the same reduction theorem. This parallels Euclid VII.2's
common-measure procedure without treating the Greek and Chinese traditions
as one source or asserting transmission.

Addition, positive-remainder subtraction, product and division retain the
rule's domain. Signed multiplication, general zero arithmetic and order of
signed quantities receive no attestation from these passages. Core Rat can
perform more operations than the quoted source supports. No existing Newton
proof is routed through these provenance theorems.

Source-to-model status: **editorial_interpretation**, confidence high for the
quoted rule/commentary distinction and the stated qualified arithmetic
correspondence; transcription accuracy remains subject to scan collation.
This classification records the encoding decision, not a historical claim
that Newton used the text or its formal algorithms.
