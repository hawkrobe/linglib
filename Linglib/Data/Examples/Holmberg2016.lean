import Linglib.Data.Examples.Schema

/-!
# `Holmberg2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Holmberg2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Holmberg2016.Examples`.
-/

namespace Holmberg2016.Examples

open Data.Examples

def english_yes_to_neg : LinguisticExample :=
  { id := "holmberg2016_english_yes_to_neg"
    source := ⟨"holmberg-2016", "yes answering a negative question (English, polarity-based)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Doesn't John drink? — Yes."
    discourseSegments := ["Doesn't John drink?", "Yes."]
    glossedTokens := []
    translation := "Doesn't John drink? — Yes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("question_polarity", "negative"), ("particle", "yes"), ("answer_polarity", "positive"), ("system", "polarityBased")]
    comment := "Migrated from Phenomena/Questions/PolarAnswerStructure.lean english_yes_to_neg; the prior Lean file's chapter pointers are stripped here. In the polarity-based English system, 'Yes' answering the negative question means 'John drinks': the particle assigns positive polarity to the elided answer clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def japanese_hai_to_neg : LinguisticExample :=
  { id := "holmberg2016_japanese_hai_to_neg"
    source := ⟨"holmberg-2016", "hai answering a negative question (Japanese, truth-based)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kare-wa nomanai no? — Hai."
    discourseSegments := ["Kare-wa nomanai no?", "Hai."]
    glossedTokens := []
    translation := "Doesn't he drink? — Yes (= he doesn't drink)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("question_polarity", "negative"), ("particle", "hai"), ("answer_polarity", "negative"), ("system", "truthBased")]
    comment := "Migrated from Phenomena/Questions/PolarAnswerStructure.lean japanese_hai_to_neg; the prior Lean file's chapter pointers are stripped here. In the truth-based Japanese system, 'Hai' affirms the question's negative proposition: it means 'He doesn't drink' — the opposite answer polarity from English 'Yes' to the same negative question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [english_yes_to_neg, japanese_hai_to_neg]

end Holmberg2016.Examples
