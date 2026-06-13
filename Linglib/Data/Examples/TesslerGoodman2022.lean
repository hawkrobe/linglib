import Linglib.Data.Examples.Schema

/-!
# `TesslerGoodman2022` — typed example data

Auto-generated from `Linglib/Data/Examples/TesslerGoodman2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TesslerGoodman2022.Examples`.
-/

namespace TesslerGoodman2022.Examples

open Data.Examples

def tg2022_tall_basketball : LinguisticExample :=
  { id := "tg2022_tall_basketball"
    source := ⟨"tessler-goodman-2022", "UNVERIFIED §3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "tall basketball player"
    discourseSegments := []
    glossedTokens := []
    translation := "tall basketball player"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "tall"), ("polarity", "positive"), ("noun", "basketball player"), ("prior_expectation", "high"), ("inferred_class", "superordinate")]
    comment := "Positive adjective + high prior expectation: inferred comparison class is superordinate (tall even compared to people in general)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def tg2022_short_basketball : LinguisticExample :=
  { id := "tg2022_short_basketball"
    source := ⟨"tessler-goodman-2022", "UNVERIFIED §3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "short basketball player"
    discourseSegments := []
    glossedTokens := []
    translation := "short basketball player"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "short"), ("polarity", "negative"), ("noun", "basketball player"), ("prior_expectation", "high"), ("inferred_class", "subordinate")]
    comment := "Negative adjective + high prior expectation: inferred comparison class is subordinate (short for a basketball player)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def tg2022_tall_jockey : LinguisticExample :=
  { id := "tg2022_tall_jockey"
    source := ⟨"tessler-goodman-2022", "UNVERIFIED §3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "tall jockey"
    discourseSegments := []
    glossedTokens := []
    translation := "tall jockey"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "tall"), ("polarity", "positive"), ("noun", "jockey"), ("prior_expectation", "low"), ("inferred_class", "subordinate")]
    comment := "Positive adjective + low prior expectation: inferred comparison class is subordinate (tall for a jockey)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def tg2022_short_jockey : LinguisticExample :=
  { id := "tg2022_short_jockey"
    source := ⟨"tessler-goodman-2022", "UNVERIFIED §3.2.1, Fig. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "short jockey"
    discourseSegments := []
    glossedTokens := []
    translation := "short jockey"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjective", "short"), ("polarity", "negative"), ("noun", "jockey"), ("prior_expectation", "low"), ("inferred_class", "superordinate")]
    comment := "Negative adjective + low prior expectation: inferred comparison class is superordinate (short even compared to people in general)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [tg2022_tall_basketball, tg2022_short_basketball, tg2022_tall_jockey, tg2022_short_jockey]

end TesslerGoodman2022.Examples
