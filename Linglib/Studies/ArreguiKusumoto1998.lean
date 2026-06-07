import Linglib.Data.Examples.Schema
import Linglib.Semantics.Tense.Reichenbach

/-!
# [arregui-kusumoto-1998]: Tense in Temporal Adjunct Clauses
[arregui-kusumoto-1998] [ogihara-sharvit-2012]

Arregui & Kusumoto (SALT VIII, 1998) argue that tense in temporal
adjunct clauses (TACs) is **not** semantically in the scope of the
matrix tense. They reject the relative-tense analysis of Ogihara (1994,
1996) on the basis of:

- Japanese when-clauses with past tense (ex 8) are episodic and
  acceptable, contradicting a relative-tense prediction of clash with
  `toki` ('when').
- Polish before- or after-clauses pattern with English (past + past), but
  Polish lacks the SOT rule — so the English pattern can't be a
  SOT-deletion effect.
- Geis-style ambiguities (ex 14) in English when-, before-, after-clauses
  indicate a relative-clause structure where the embedded tense is
  evaluated independently with the speech time as its reference.

A&K propose: English and Polish TACs are relative-clause-like (absolute
tenses); Japanese before- or after-clauses involve direct TP-selection by
the temporal connective (no relative-clause structure); Japanese
when-clauses are absolute (like English when). The past-vs-present
contrast in Japanese TACs is **quantificational** (episodic vs
habitual), not temporal — present tense is a temporal variable bound
by adverbs of quantification.

## Empirical anchors (verified vs PDF)

- (1) "Bernhard said that Junko was sick" — English SOT context-setter.
- (5a/b) Japanese before+past * vs before+present OK.
- (6a/b) Japanese after+past OK vs after+present *.
- (7a/b) English Elliott/Eva with both past+past tense.
- (8) "Junko was in her room when Satoshi came" — Japanese when+past
  (episodic), the counterexample to Ogihara's relative tense.
- (9) "...whenever Satoshi came" — Japanese when+present (habitual).
- (14) "I encountered Satoshi in Amherst when you said he had left"
  — Geis ambiguity.
- (18a/b) "I watered the plant before/after it died" — before/after
  veridicality contrast.

## Scope of the Reichenbach frames below

A&K's English-side anchor example is **Elliott left before Eva came**
(ex 7a); frames are named `elliottLeft` / `evaCame` accordingly.

The (R,E)-frames only capture temporal ordering between two past
events. A&K's actual contribution — the relative-clause analysis of
English/Polish TACs vs direct TP-selection in Japanese, plus the
past/present quantificational contrast — is not encodable in
(S,P,R,E) and lives in the JSON above + the verified Geis-ambiguity
example.

-/

namespace ArreguiKusumoto1998

open Semantics.Tense.Reichenbach
open Data.Examples (LinguisticExample)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/ArreguiKusumoto1998.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def ex1 : LinguisticExample :=
  { id := "arreguikusumoto1998_ex1"
    source := ⟨"arregui-kusumoto-1998", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bernhard said that Junko was sick."
    discourseSegments := []
    glossedTokens := []
    translation := "Bernhard said that Junko was sick."
    context := "English SOT context-setter. Ambiguous between simultaneous (Bernhard said: 'Junko is sick') and past-shifted (Bernhard said: 'Junko was sick') readings. Establishes the SOT phenomenon Arregui & Kusumoto's TAC analysis contrasts with."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (Junko sick at saying time)", .acceptable), ("past-shifted (Junko sick before saying)", .acceptable)]
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (1), SALT VIII p. 1. Originating discussion of this example shape is Enç 1987 (cited by A&K as [Eng 1987]; no enc-1987 bib entry yet)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex5a : LinguisticExample :=
  { id := "arreguikusumoto1998_ex5a"
    source := ⟨"arregui-kusumoto-1998", "(5a)"⟩
    reportedIn := none
    language := "stan1316"
    primaryText := "*Junko-ga kita mae-ni Satoshi-wa kaetta."
    discourseSegments := []
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kita", "come-PAST"), ("mae-ni", "before"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave-PAST")]
    translation := "'Satoshi left before Junko came' (intended)"
    context := "Japanese before-clause with past tense — UNGRAMMATICAL. The past tense in the adjunct under a relative-tense analysis would place Junko's coming before Satoshi's leaving, contradicting `mae-ni` ('before'). Diagnostic for the Ogihara relative-tense analysis of Japanese TACs."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (5a), p. 2. Together with (5b), establishes that Japanese before-clauses obligatorily take present tense. Ogihara's relative-tense analysis predicts this."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex5b : LinguisticExample :=
  { id := "arreguikusumoto1998_ex5b"
    source := ⟨"arregui-kusumoto-1998", "(5b)"⟩
    reportedIn := none
    language := "stan1316"
    primaryText := "Junko-ga kuru mae-ni Satoshi-wa kaetta."
    discourseSegments := []
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kuru", "come-PRES"), ("mae-ni", "before"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave-PAST")]
    translation := "Satoshi left before Junko came."
    context := "Japanese before-clause with present tense. The present is interpreted as future-relative-to-matrix-event (Japanese present can have future orientation), compatible with `mae-ni` ('before'). The grammatical counterpart to (5a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (5b), p. 2. Minimal pair with (5a). Establishes obligatory present in Japanese before-clauses."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex6a : LinguisticExample :=
  { id := "arreguikusumoto1998_ex6a"
    source := ⟨"arregui-kusumoto-1998", "(6a)"⟩
    reportedIn := none
    language := "stan1316"
    primaryText := "Junko-ga kita ato-ni Satoshi-wa kaetta."
    discourseSegments := []
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kita", "come-PAST"), ("ato-ni", "after"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave-PAST")]
    translation := "Satoshi left after Junko came."
    context := "Japanese after-clause with past tense — GRAMMATICAL. Mirror image of (5a): past tense under `ato-ni` ('after') is compatible because Junko's coming precedes Satoshi's leaving, matching the `after` denotation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (6a), p. 3. Mirrors (5a)/(5b) distribution: Japanese after-clauses take past, before-clauses take present."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex6b : LinguisticExample :=
  { id := "arreguikusumoto1998_ex6b"
    source := ⟨"arregui-kusumoto-1998", "(6b)"⟩
    reportedIn := none
    language := "stan1316"
    primaryText := "*Junko-ga kuru ato-ni Satoshi-wa kaetta."
    discourseSegments := []
    glossedTokens := [("Junko-ga", "Junko-NOM"), ("kuru", "come-PRES"), ("ato-ni", "after"), ("Satoshi-wa", "Satoshi-TOP"), ("kaetta", "leave-PAST")]
    translation := "'Satoshi left after Junko came' (intended)"
    context := "Japanese after-clause with present tense — UNGRAMMATICAL. Present-tense Japanese can mean future-relative-to-matrix, contradicting `ato-ni` ('after')."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (6b), p. 3. Completes the Japanese before/after × past/present × grammaticality square."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex7a : LinguisticExample :=
  { id := "arreguikusumoto1998_ex7a"
    source := ⟨"arregui-kusumoto-1998", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Elliott left before Eva came."
    discourseSegments := []
    glossedTokens := []
    translation := "Elliott left before Eva came."
    context := "English before-clause with past tense in BOTH matrix and adjunct — GRAMMATICAL. Contrasts directly with Japanese (5a). Ogihara's account: English has the SOT-rule, which deletes the embedded past at LF, so the temporal ordering comes from `before` rather than from a tense conflict."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (7a), p. 4. The English-side anchor example for A&K's TAC analysis."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex7b : LinguisticExample :=
  { id := "arreguikusumoto1998_ex7b"
    source := ⟨"arregui-kusumoto-1998", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Elliott left after Eva came."
    discourseSegments := []
    glossedTokens := []
    translation := "Elliott left after Eva came."
    context := "English after-clause counterpart of (7a). Both past tenses; SOT-deletion lets `after` carry the ordering. Grammatical, parallel to (7a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (7b), p. 4. Mirror of (7a). English allows past in both before- and after-clauses thanks to SOT-deletion."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8 : LinguisticExample :=
  { id := "arreguikusumoto1998_ex8"
    source := ⟨"arregui-kusumoto-1998", "(8)"⟩
    reportedIn := none
    language := "stan1316"
    primaryText := "Satoshi-ga kita toki Junko-wa heya-ni ita."
    discourseSegments := []
    glossedTokens := [("Satoshi-ga", "Satoshi-NOM"), ("kita", "come-PAST"), ("toki", "when"), ("Junko-wa", "Junko-TOP"), ("heya-ni", "room-at"), ("ita", "be-PAST")]
    translation := "Junko was in her room when Satoshi came. (episodic)"
    context := "Japanese when-clause with past tense — GRAMMATICAL, episodic reading. Unexpected for Ogihara's relative-tense analysis (since `toki` ('when') indicates simultaneity, past-shifted should clash). Motivates A&K's alternative: Japanese when-clauses are absolute, like English when-clauses."
    judgment := .acceptable
    alternatives := []
    readings := [("episodic (one specific past coming)", .acceptable)]
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (8), p. 5. Cornerstone counterexample to Ogihara's relative-tense analysis of Japanese TACs. A&K respond by treating Japanese when-clauses as absolute (relative-clause-like) rather than relative tenses."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex9 : LinguisticExample :=
  { id := "arreguikusumoto1998_ex9"
    source := ⟨"arregui-kusumoto-1998", "(9)"⟩
    reportedIn := none
    language := "stan1316"
    primaryText := "Satoshi-ga kuru toki Junko-wa heya-ni ita."
    discourseSegments := []
    glossedTokens := [("Satoshi-ga", "Satoshi-NOM"), ("kuru", "come-PRES"), ("toki", "when"), ("Junko-wa", "Junko-TOP"), ("heya-ni", "room-at"), ("ita", "be-PAST")]
    translation := "Junko was in her room whenever Satoshi came. (quantificational/habitual)"
    context := "Japanese when-clause with present tense — GRAMMATICAL but with a habitual interpretation. The past-vs-present contrast in Japanese when-clauses is QUANTIFICATIONAL (episodic vs habitual) rather than purely temporal. Motivates A&K's claim that Japanese present is a temporal variable bound by adverbs of quantification."
    judgment := .acceptable
    alternatives := []
    readings := [("habitual / quantificational", .acceptable)]
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (9), p. 5. Minimal pair with (8). The quantificational shift (episodic → habitual) under tense change is A&K's key evidence that Japanese present is a variable, not an operator."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex14 : LinguisticExample :=
  { id := "arreguikusumoto1998_ex14"
    source := ⟨"arregui-kusumoto-1998", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I encountered Satoshi in Amherst when you said he had left."
    discourseSegments := []
    glossedTokens := []
    translation := "I encountered Satoshi in Amherst when you said he had left."
    context := "Geis ambiguity: 'when'-clause is ambiguous between high (when = time of your saying) and low (when = time he had left, per you) construals. A&K take this as evidence for a relative-clause analysis of English TACs."
    judgment := .acceptable
    alternatives := []
    readings := [("upstairs (when = saying time)", .acceptable), ("downstairs (when = his leaving, per you)", .acceptable)]
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (14), p. 7. Originally Geis 1970. (No geis-1970 bib entry; sourced via reportedIn = A&K.) Cornerstone Geis-ambiguity example — extraction from main clause vs embedded clause yields two readings."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex18a : LinguisticExample :=
  { id := "arreguikusumoto1998_ex18a"
    source := ⟨"arregui-kusumoto-1998", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I watered the plant before it died."
    discourseSegments := []
    glossedTokens := []
    translation := "I watered the plant before it died."
    context := "Non-veridical `before`: the before-clause needn't refer to an actual event. (18a) can be true even if the plant didn't actually die — perhaps because the watering kept it alive."
    judgment := .acceptable
    alternatives := []
    readings := [("veridical (plant died)", .acceptable), ("non-veridical (plant didn't die)", .acceptable)]
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (18a), p. 10. Diagnostic for the before/after veridicality asymmetry — citing Anscombe 1964, Landman 1991, Ogihara 1995."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex18b : LinguisticExample :=
  { id := "arreguikusumoto1998_ex18b"
    source := ⟨"arregui-kusumoto-1998", "(18b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I watered the plant after it died."
    discourseSegments := []
    glossedTokens := []
    translation := "I watered the plant after it died."
    context := "Veridical `after`: the after-clause must refer to an actual event. (18b) presupposes the plant did die. Contrasts with (18a)."
    judgment := .acceptable
    alternatives := []
    readings := [("veridical (plant died)", .acceptable)]
    paperFeatures := []
    comment := "Arregui & Kusumoto 1998 ex (18b), p. 10. The after-clause requires a real event, unlike before. Motivates A&K's denotations: `before P` = no-P-time after; `after P` = ∃ P-time before."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1, ex5a, ex5b, ex6a, ex6b, ex7a, ex7b, ex8, ex9, ex14, ex18a, ex18b]

end Examples
-- END GENERATED EXAMPLES


-- ════════════════════════════════════════════════════════════════
-- § Reichenbach frames (illustrative; named for A&K ex 7a Elliott/Eva)
-- ════════════════════════════════════════════════════════════════

/-! These frames represent A&K example (7a) — `Elliott left before Eva
    came`. The (R,E)-frame only encodes the temporal ordering between
    the two past events; A&K's actual claims about TAC structure
    (relative-clause vs direct TP-selection) and the
    episodic/habitual quantificational contrast are not encoded in
    Reichenbach frames. The JSON above carries those facts. -/

/-- Adjunct clause "before Eva came" — Eva's coming event.
    Past tense; in A&K's analysis, this past tense in English is
    interpreted absolutely (with speech time as reference), unlike
    the Ogihara relative-tense story. -/
def evaCame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- absolute: P = S
  referenceTime := -3
  eventTime := -3

/-- Matrix clause "Elliott left" — Elliott's leaving event.
    Past tense; absolute perspective. -/
def elliottLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2


-- ════════════════════════════════════════════════════════════════
-- § Per-datum verifications
-- ════════════════════════════════════════════════════════════════

/-- `before`-ordering: the adjunct event precedes the matrix event.
    This is the structural consequence of `before` in the temporal
    connective, not of any tense composition. -/
theorem evaCame_before_elliottLeft :
    evaCame.eventTime < elliottLeft.eventTime := by decide

end ArreguiKusumoto1998
