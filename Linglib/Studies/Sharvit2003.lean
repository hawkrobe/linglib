import Linglib.Data.Examples.Schema
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Tense.Basic

/-!
# [sharvit-2003]: Embedded Tense and Universal Grammar
[sharvit-2003] [abusch-1997] [ogihara-1996]

Sharvit (Linguistic Inquiry 34(4), 2003) observes a cross-linguistic
correlation between (a) the obligatoriness of utterance-time reference
for present-under-past sentences and (b) the availability of a
"vacuous" past tense in complement clauses. She proposes the
**Embeddability Principle (EP)**: any well-formed matrix LF must be
embeddable under an attitude verb. The EP excludes "type 4" languages
(no SOT rule + matrix-indexical present), predicting the attested
typology of SOT/non-SOT and English/Hebrew/Modern Greek.

## Empirical anchors (verified vs PDF)

- (1) "A week ago, John decided that in ten days, at breakfast, he
  would tell his mother that he missed her." — multiply-embedded SOT,
  nonpast + anteriority readings.
- (2) "John believed that Mary was pregnant." — past-under-past,
  both readings.
- (3) "John believed that Mary is pregnant." — present-under-past,
  ONLY double-access reading.
- (4a)/(4b) "Two years ago, Sally found out that Mary was/is pregnant."
  — diagnostic asymmetry from pregnancy-duration mismatch with double
  access.
- (5)/(6) Hebrew non-SOT minimal pair: embedded PRES gives nonpast,
  embedded PAST gives only anteriority.

## Scope of the Reichenbach frames below

The frames cover the embedded-present-under-future shape (close to
Sharvit's (3) but with future matrix). The (R,E)-frame cannot fully
capture present-under-past double-access — see the JSON's `ex3` for
the empirical content. The Hebrew minimal pair (Sharvit's (5)/(6))
lives entirely in the JSON; structurally the past-form and
present-form would produce identical (R,E)-frames so encoding the
contrast as separate Lean defs would be vacuous.

-/

namespace Sharvit2003

open Semantics.Tense.Reichenbach
open Semantics.Tense
open Data.Examples (LinguisticExample)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/Sharvit2003.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def ex1 : LinguisticExample :=
  { id := "sharvit2003_ex1"
    source := ⟨"abusch-1997", "inspiration"⟩
    reportedIn := some ⟨"sharvit-2003", "(1)"⟩
    language := "stan1293"
    primaryText := "A week ago, John decided that in ten days, at breakfast, he would tell his mother that he missed her."
    discourseSegments := []
    glossedTokens := []
    translation := "A week ago, John decided that in ten days, at breakfast, he would tell his mother that he missed her."
    context := "Past-under-past-under-past with embedded past `missed`. Two readings: nonpast (telling-time and missing-time overlap, both future of utterance) and anteriority (missing-time precedes telling-time)."
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast (missing overlaps telling)", .acceptable), ("anteriority (missing precedes telling)", .acceptable)]
    paperFeatures := []
    comment := "Sharvit 2003 ex (1), LI 34(4) p. 669. Inspired by Abusch 1997. Cornerstone SOT phenomenon — nonpast/anteriority ambiguity of multiply-embedded past."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2 : LinguisticExample :=
  { id := "sharvit2003_ex2"
    source := ⟨"sharvit-2003", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary was pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed that Mary was pregnant."
    context := "Past-under-past. Two readings: nonpast (pregnancy overlaps believing) and anteriority (pregnancy precedes believing)."
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast (pregnancy at believing)", .acceptable), ("anteriority (pregnancy before believing)", .acceptable)]
    paperFeatures := []
    comment := "Sharvit 2003 ex (2), p. 669. Sharvit cites Enç 1987 as a prior user of this example shape. (No enc-1987 bib entry yet; sourced to Sharvit directly.) Standard past-under-past with both readings — diagnostic for SOT."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3 : LinguisticExample :=
  { id := "sharvit2003_ex3"
    source := ⟨"sharvit-2003", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary is pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed that Mary is pregnant."
    context := "Present-under-past. ONLY the double-access reading: pregnancy must contain BOTH the believing time AND the utterance time. Nonpast reading unavailable."
    judgment := .acceptable
    alternatives := []
    readings := [("double access (pregnancy spans believing + utterance)", .acceptable), ("nonpast (pregnancy at believing only)", .ungrammatical)]
    paperFeatures := []
    comment := "Sharvit 2003 ex (3), p. 670. Cornerstone present-under-past example. Motivates the Embeddability Principle: every well-formed matrix LF must be embeddable; the syntactic means differ by language."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex4a : LinguisticExample :=
  { id := "sharvit2003_ex4a"
    source := ⟨"sharvit-2003", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two years ago, Sally found out that Mary was pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "Two years ago, Sally found out that Mary was pregnant."
    context := "Past-under-past with adverbial. Acceptable via nonpast reading: pregnancy overlaps finding-out (two years ago)."
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast (pregnancy at finding-out two years ago)", .acceptable)]
    paperFeatures := []
    comment := "Sharvit 2003 ex (4a), p. 670. Acceptability of (4a) and oddity of (4b) jointly diagnose the present-vs-past asymmetry."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex4b : LinguisticExample :=
  { id := "sharvit2003_ex4b"
    source := ⟨"sharvit-2003", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Two years ago, Sally found out that Mary is pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "Two years ago, Sally found out that Mary is pregnant."
    context := "Present-under-past with adverbial. ODD: double-access requires pregnancy to span both two-years-ago and now — incompatible with pregnancy duration."
    judgment := .unacceptable
    alternatives := []
    readings := [("double access (pregnancy spans 2y window)", .unacceptable)]
    paperFeatures := []
    comment := "Sharvit 2003 ex (4b), p. 670. Marked with `#` in the paper (pragmatic infelicity). Diagnostic for the obligatoriness of the double-access reading."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex5 : LinguisticExample :=
  { id := "sharvit2003_ex5"
    source := ⟨"sharvit-2003", "(5)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney shavua, Dan hexlit she be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo she hu mitga'agea ele-ha."
    discourseSegments := []
    glossedTokens := [("Lifney", "before"), ("shavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("she", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat", "meal-CST"), ("ha-boker", "the-morning"), ("hu", "he"), ("yomar", "will.tell-FUT"), ("le-imo", "to-his.mother"), ("she", "that"), ("hu", "he"), ("mitga'agea", "miss-PRES"), ("ele-ha", "to-her")]
    translation := "A week ago, Dan decided that in ten days, at breakfast, he would tell his mother that he misses her."
    context := "Hebrew non-SOT: embedded PRESENT (`mitga'agea`) delivers the nonpast reading. Hebrew lacks the SOT rule but its present-tense morpheme is not matrix-indexical, so it can be bound as a zero tense."
    judgment := .acceptable
    alternatives := []
    readings := [("nonpast via Hebrew embedded PRES", .acceptable)]
    paperFeatures := []
    comment := "Sharvit 2003 ex (5), p. 670. Hebrew counterpart to English (1)'s nonpast reading. Together with (6), establishes the SOT typology Sharvit's Embeddability Principle must account for."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex6 : LinguisticExample :=
  { id := "sharvit2003_ex6"
    source := ⟨"sharvit-2003", "(6)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Lifney shavua, Dan hexlit she be'od asara yamim, bizman aruxat ha-boker, hu yomar le-imo she hu hitga'agea ele-ha."
    discourseSegments := []
    glossedTokens := [("Lifney", "before"), ("shavua", "week"), ("Dan", "Dan"), ("hexlit", "decide-PAST"), ("she", "that"), ("be'od", "in"), ("asara", "ten"), ("yamim", "days"), ("bizman", "at-time"), ("aruxat", "meal-CST"), ("ha-boker", "the-morning"), ("hu", "he"), ("yomar", "will.tell-FUT"), ("le-imo", "to-his.mother"), ("she", "that"), ("hu", "he"), ("hitga'agea", "miss-PAST"), ("ele-ha", "to-her")]
    translation := "A week ago, Dan decided that in ten days, at breakfast, he would tell his mother that he missed her."
    context := "Hebrew non-SOT: embedded PAST (`hitga'agea`) delivers ONLY the anteriority reading. In Hebrew (vs English), embedded past cannot be SOT-deleted to give the nonpast reading."
    judgment := .acceptable
    alternatives := []
    readings := [("anteriority (missing before telling)", .acceptable), ("nonpast (missing at telling)", .ungrammatical)]
    paperFeatures := []
    comment := "Sharvit 2003 ex (6), p. 670. Minimal pair partner of (5) — same surface meaning, embedded PAST vs PRES. The asymmetry diagnostics Hebrew as non-SOT."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex1, ex2, ex3, ex4a, ex4b, ex5, ex6]

end Examples
-- END GENERATED EXAMPLES


-- ════════════════════════════════════════════════════════════════
-- § Reichenbach frames for embedded present under future
-- ════════════════════════════════════════════════════════════════

/-- Matrix "John will say..." — future tense, perfective. -/
def matrixWillSay : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3
  eventTime := 3

/-- Embedded present under future "Mary is sick" — sickness at the
    future saying time, R = P relative to the shifted perspective. -/
def embeddedPresentUnderFuture : ReichenbachFrame ℤ :=
  embeddedFrame matrixWillSay 3 3

/-- Matrix frame satisfies `isFuture` (R > P). -/
theorem matrixWillSayIsFuture : matrixWillSay.isFuture := by
  simp only [ReichenbachFrame.isFuture, matrixWillSay]; omega

/-- Embedded present under future: R = P relative to shifted perspective. -/
theorem embeddedPresentUnderFutureIsPresent : embeddedPresentUnderFuture.isPresent := by
  simp only [ReichenbachFrame.isPresent, embeddedPresentUnderFuture, embeddedFrame, matrixWillSay]

end Sharvit2003
