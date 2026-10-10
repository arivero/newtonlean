# 九章算術 — 卷第八 方程, scan pages 9–11 of Sibu Congkan0392-劉徽-九章算術-3-3.djvu

Anonymous base text; transmitted with 魏劉徽注 and 唐李淳風等奉敕注釋.
Witness: **四部叢刊本**, whose heading identifies the photographic exemplar as
景上海涵芬樓藏微波榭刊本. This is a later printed witness with a modern Chinese
Wikisource transcription, not an ancient manuscript or a critical edition.

Source: [fixed page revision 2658141](https://zh.wikisource.org/w/index.php?oldid=2658141).
Retrieved 10 October 2026. Original rendered HTML: [nine-chapters-VIII.html](nine-chapters-VIII.html).
SHA-256: `c93008f96cf488209503b97207e9f812472a317fa5b35be9195de5f5ad972247` (also in [the archive checksums](../SHA256SUMS)).
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

The two clauses are kept distinct. Line wraps are joined without adding
punctuation to the Chinese quotation.

Subtraction:

> 正負術曰同名相除異名相益正無入負之負無入正之

Addition:

> 其異名相除同名相益正無入正之負無入負之

除 here concerns removal/subtraction in the 方程 procedure, not division of
signed quantities. The names identify opposite kinds of entries. Same names
subtract and opposite names augment in the first clause; the second reverses
those actions. The text's 無入 refers to an absent opposing entry. Its encoding
by 0 in the explicit cases does not source general arithmetic with zero.

## Liu Hui commentary witness, separate from 術

The annotation opening the 正負 rule reads:

> 今兩算得失相反要令正負以名之正算赤負算黑否則以邪正爲異

It names opposite gains/losses 正 and 負 and distinguishes rods by colour or
orientation. The annotation continues after this excerpt in the archived HTML;
those later words have not been inserted into the rule.

Liu Hui's commentary is dated **263 CE**, while Li Chunfeng's later
subcommentary was presented in **656**. This chronology is supported by
[Karine Chemla's discussion of the commentary layers](https://www.cambridge.org/core/journals/bjhs-themes/article/reading-instructions-of-the-past-classifying-them-and-reclassifying-them-commentaries-on-the-canon-the-nine-chapters-on-mathematical-procedures-from-the-third-to-the-thirteenth-centuries/F402B3DE252D1799135618C259E5C706),
section “The sources”; it is secondary dating evidence, not the source of the
arithmetic theorem. The exact Chinese passages above come from the archived
primary-text transcription. The printed/transcribed witness is not a 263
manuscript. No claim that every unmarked annotation is securely assigned to
one layer is made; Chemla notes transmission can blur the layers.

## Source-to-model correspondence

[FractionRules.lean](../../ClassicsLib/NineChapters/FractionRules.lean)
embeds positive whole magnitudes, their opposing names and the explicit
absent-entry cases in core Rat. Its two signed theorems are **R**: cases on
natural magnitudes determine the name remaining after removal, and the
coordinate sign convention is stated. This is not a source for general signed
rational arithmetic, signed multiplication or numerical ordering of signed
quantities. The case comparison only selects the surviving magnitude.

No existing proof is routed through this source file. A future claim about
signed multiplication, general zero arithmetic or signed order requires an
exact passage of its own; possible later Chinese or Indian sources are not
attributed without that review.

Source-to-model status: **editorial_interpretation**, confidence high for the
quoted rule/commentary distinction and the stated qualified arithmetic
correspondence; transcription accuracy remains subject to scan collation.
This classification records the encoding decision, not a historical claim
that Newton used the text or its formal algorithms.
