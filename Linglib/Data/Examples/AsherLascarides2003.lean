import Linglib.Data.Examples.Schema

/-!
# `AsherLascarides2003` — typed example data

Auto-generated from `Linglib/Data/Examples/AsherLascarides2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AsherLascarides2003.Examples`.
-/

namespace AsherLascarides2003.Examples

open Data.Examples

def ex_18 : LinguisticExample :=
  { id := "asherlascarides2003_18"
    source := ⟨"asher-lascarides-2003", "(18)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John had a great evening last night. He had a great meal. He ate salmon. He devoured lots of cheese. He then won a dancing competition."
    discourseSegments := ["John had a great evening last night.", "He had a great meal.", "He ate salmon.", "He devoured lots of cheese.", "He then won a dancing competition."]
    glossedTokens := []
    translation := "John had a great evening last night. He had a great meal. He ate salmon. He devoured lots of cheese. He then won a dancing competition."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "(17)")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18_pink : LinguisticExample :=
  { id := "asherlascarides2003_18_pink"
    source := ⟨"asher-lascarides-2003", "(18), p. 147 continuation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John had a great evening last night. He had a great meal. He ate salmon. He devoured lots of cheese. He then won a dancing competition. It was a beautiful pink."
    discourseSegments := ["John had a great evening last night.", "He had a great meal.", "He ate salmon.", "He devoured lots of cheese.", "He then won a dancing competition.", "It was a beautiful pink."]
    glossedTokens := []
    translation := "John had a great evening last night. He had a great meal. He ate salmon. He devoured lots of cheese. He then won a dancing competition. It was a beautiful pink."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "(17)"), ("antecedent", "salmon"), ("antecedentLabel", "3")]
    comment := "The salmon is introduced in the constituent labelled π3, which is not on the right frontier."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "asherlascarides2003_19"
    source := ⟨"asher-lascarides-2003", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John bought an apartment but he rented it."
    discourseSegments := ["John bought an apartment", "but he rented it."]
    glossedTokens := []
    translation := "John bought an apartment but he rented it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relations", "Contrast, Narration")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "asherlascarides2003_22"
    source := ⟨"asher-lascarides-2003", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drives a car. It is red."
    discourseSegments := ["John drives a car.", "It is red."]
    glossedTokens := []
    translation := "John drives a car. It is red."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("relations", "Background"), ("antecedent", "car")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "asherlascarides2003_23"
    source := ⟨"asher-lascarides-2003", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If a farmer doesn't drive a car then it's red."
    discourseSegments := ["If a farmer doesn't drive a car", "then it's red."]
    glossedTokens := []
    translation := "If a farmer doesn't drive a car then it's red."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("relations", "Consequence"), ("antecedent", "car")]
    comment := "The car is under negation in the antecedent and so not available to the pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_18, ex_18_pink, ex_19, ex_22, ex_23]

end AsherLascarides2003.Examples
