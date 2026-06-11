import Linglib.Data.Examples.Schema

/-!
# `Klecha2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Klecha2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Klecha2016.Examples`.
-/

namespace Klecha2016.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "klecha2016_ex1"
    source := ⟨"klecha-2016", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martina thought Carissa was pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "Martina thought Carissa was pregnant."
    context := "Klecha's canonical SOT example. Past matrix (`thought`) + past embedded (`was pregnant`). Both RTs precede speech time; additionally, per the Upper Limit Constraint, the embedded RT (Carissa's pregnancy time) is no later than the matrix RT (Martina's thinking)."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (pregnancy at thinking)", .acceptable), ("shifted (pregnancy before thinking)", .acceptable), ("future-shifted (pregnancy after thinking)", .ungrammatical)]
    paperFeatures := []
    comment := "Klecha 2016 ex (1), Semantics & Pragmatics 9(10) p. 9:1. Opening example introducing ULC; both deictic-tense and relative-tense theories are surveyed in his §1 against this datum. The DOX modal base under `think` blocks future-shifted reading, which is Klecha's central explanatory move."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2a : LinguisticExample :=
  { id := "klecha2016_ex2a"
    source := ⟨"klecha-2016", "(2a) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said Sorenstam had no business playing the PGA Tour, he hoped she missed the cut and he'd withdraw if paired with her, the AP reported."
    discourseSegments := ["He said Sorenstam had no business playing the PGA Tour,", "he hoped she missed the cut and he'd withdraw if paired with her,", "the AP reported."]
    glossedTokens := []
    translation := "He said Sorenstam had no business playing the PGA Tour, he hoped she missed the cut and he'd withdraw if paired with her, the AP reported."
    context := "Naturally-occurring example showing future-shifted reading of embedded past under `hope`. `She missed the cut` is in past tense morphology but the cut-missing is future-of-the-hoping (Singh hoped, at the time of hoping, that the cut-missing would occur AFTER the hoping)."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (missed-cut after hoping)", .acceptable)]
    paperFeatures := []
    comment := "Klecha 2016 ex (2a), p. 9:2-3. Corpus of Contemporary American English (Davies 2008). Cornerstone of Klecha's argument: under `hope` (which permits a CIR modal base), embedded past can have a future-shifted reading — impossible under `think` (DOX-only). Diagnoses the modal-base parameter, not the attitude verb per se."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "klecha2016_ex2b"
    source := ⟨"klecha-2016", "(2b) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He was going to find that Guardian and do what he had to do. But his gut dropped at the thought of killing anyone in cold blood, even to save his brother. He hoped she tried to kill him first. Then he could behead her with a clean conscience."
    discourseSegments := ["He was going to find that Guardian and do what he had to do.", "But his gut dropped at the thought of killing anyone in cold blood, even to save his brother.", "He hoped she tried to kill him first.", "Then he could behead her with a clean conscience."]
    glossedTokens := []
    translation := "He hoped she tried to kill him first."
    context := "Second naturally-occurring example of future-shifted past under `hope`. The kill-attempt is future of the hoping; the embedded past tense morphology doesn't force temporal precedence."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (try-to-kill after hoping)", .acceptable)]
    paperFeatures := []
    comment := "Klecha 2016 ex (2b), p. 9:3. Second corpus example for the same point."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3a : LinguisticExample :=
  { id := "klecha2016_ex3a"
    source := ⟨"klecha-2016", "(3a) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There were times when I picked one receiver and prayed he got open."
    discourseSegments := []
    glossedTokens := []
    translation := "There were times when I picked one receiver and prayed he got open."
    context := "Future-shifted reading under `pray`. `Got open` is past morphology but the getting-open is future-of-the-praying."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (got-open after praying)", .acceptable)]
    paperFeatures := []
    comment := "Klecha 2016 ex (3a), p. 9:3. `Pray` patterns with `hope`: CIR-base attitude verbs permit future-shifted embedded past. Quarterback Kerry Collins, attributed in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3b : LinguisticExample :=
  { id := "klecha2016_ex3b"
    source := ⟨"klecha-2016", "(3b) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Thirteen months and she would legally be able to walk out the door and live on her own. Her trust fund would be hers. She would no longer be dependent on her mother and Victor. Thirteen months. She prayed she survived that long."
    discourseSegments := ["Thirteen months and she would legally be able to walk out the door and live on her own.", "Her trust fund would be hers.", "She would no longer be dependent on her mother and Victor.", "Thirteen months.", "She prayed she survived that long."]
    glossedTokens := []
    translation := "She prayed she survived that long."
    context := "Past morphology `survived` in the embedded clause of `pray`, but the surviving is future-of-the-praying (thirteen months out)."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (survival after praying)", .acceptable)]
    paperFeatures := []
    comment := "Klecha 2016 ex (3b), p. 9:3. Fourth corpus example. The (2a-b)/(3a-b) cluster establishes that future-shifted past is systematic across CIR-compatible attitude verbs, not exceptional."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1, ex2a, ex2b, ex3a, ex3b]

end Klecha2016.Examples
