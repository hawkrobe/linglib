import Linglib.Data.Examples.Schema

/-!
# `Krifka2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Krifka2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krifka2026.Examples`.
-/

namespace Krifka2026.Examples

open Data.Examples

def ex3a : LinguisticExample :=
  { id := "krifka2026_ex3a"
    source := ⟨"krifka-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John killed a spider because they are ugly."
    discourseSegments := []
    glossedTokens := []
    translation := "John killed a spider because they are ugly."
    context := "Kind anaphora to an object-referring antecedent, with a number mismatch between the singular antecedent and the plural anaphor."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "count"), ("anaphor", "they")]
    comment := "The paper credits the observation to Krifka et al. (1995)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3b : LinguisticExample :=
  { id := "krifka2026_ex3b"
    source := ⟨"krifka-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drank some milk even though he is allergic to it."
    discourseSegments := []
    glossedTokens := []
    translation := "John drank some milk even though he is allergic to it."
    context := "Kind anaphora to a mass antecedent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "mass"), ("anaphor", "it")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5a : LinguisticExample :=
  { id := "krifka2026_ex5a"
    source := ⟨"krifka-2026", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't own a dog. He is afraid of them. But Mary owns one."
    discourseSegments := ["John doesn't own a dog.", "He is afraid of them.", "But Mary owns one."]
    glossedTokens := []
    translation := "John doesn't own a dog. He is afraid of them. But Mary owns one."
    context := "Kind anaphora and one-anaphora reach a concept introduced under negation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "they")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5b : LinguisticExample :=
  { id := "krifka2026_ex5b"
    source := ⟨"krifka-2026", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary didn't buy any milk. She cannot digest it. But John bought some."
    discourseSegments := ["Mary didn't buy any milk.", "She cannot digest it.", "But John bought some."]
    glossedTokens := []
    translation := "Mary didn't buy any milk. She cannot digest it. But John bought some."
    context := "Kind anaphora and some-anaphora reach a mass concept introduced under negation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "mass"), ("island", "negation"), ("anaphor", "it")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5c : LinguisticExample :=
  { id := "krifka2026_ex5c"
    source := ⟨"krifka-2026", "(5c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John doesn't own a dog. It is friendly."
    discourseSegments := ["John doesn't own a dog.", "It is friendly."]
    glossedTokens := []
    translation := "John doesn't own a dog. It is friendly."
    context := "An entity pronoun cannot reach a referent introduced under negation."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "entityPronoun")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7a : LinguisticExample :=
  { id := "krifka2026_ex7a"
    source := ⟨"krifka-2026", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John noticed a spider in the bathroom. He has a phobia against them."
    discourseSegments := ["John noticed a spider in the bathroom.", "He has a phobia against them."]
    glossedTokens := []
    translation := "John noticed a spider in the bathroom. He has a phobia against them."
    context := "A count antecedent, singular or plural, requires the plural kind anaphor."
    judgment := .acceptable
    alternatives := [("He has a phobia against it.", .unacceptable)]
    readings := []
    paperFeatures := [("antecedent", "count"), ("anaphor", "they")]
    comment := "The antecedent may also be *spiders* or *two spiders*."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7b : LinguisticExample :=
  { id := "krifka2026_ex7b"
    source := ⟨"krifka-2026", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John noticed mold in the bathroom. He is allergic against it."
    discourseSegments := ["John noticed mold in the bathroom.", "He is allergic against it."]
    glossedTokens := []
    translation := "John noticed mold in the bathroom. He is allergic against it."
    context := "A mass antecedent requires the singular kind anaphor."
    judgment := .acceptable
    alternatives := [("He is allergic against them.", .unacceptable)]
    readings := []
    paperFeatures := [("antecedent", "mass"), ("anaphor", "it")]
    comment := "The antecedent may also be *a spot of mold* or *two spots of mold*."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8a : LinguisticExample :=
  { id := "krifka2026_ex8a"
    source := ⟨"krifka-2026", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There is a lot of pollen in the air. I am allergic against it."
    discourseSegments := ["There is a lot of pollen in the air.", "I am allergic against it."]
    glossedTokens := []
    translation := "There is a lot of pollen in the air. I am allergic against it."
    context := "The same individuals under a mass noun take the singular kind anaphor."
    judgment := .acceptable
    alternatives := [("I am allergic against them.", .unacceptable)]
    readings := []
    paperFeatures := [("antecedent", "mass"), ("anaphor", "it")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8b : LinguisticExample :=
  { id := "krifka2026_ex8b"
    source := ⟨"krifka-2026", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There are a lot of pollen grains in the air. I am allergic against them."
    discourseSegments := ["There are a lot of pollen grains in the air.", "I am allergic against them."]
    glossedTokens := []
    translation := "There are a lot of pollen grains in the air. I am allergic against them."
    context := "The same individuals under a count noun take the plural kind anaphor."
    judgment := .acceptable
    alternatives := [("I am allergic against it.", .questionable)]
    readings := []
    paperFeatures := [("antecedent", "count"), ("anaphor", "they")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19a : LinguisticExample :=
  { id := "krifka2026_ex19a"
    source := ⟨"krifka-2026", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't get a dog from the animal shelter downtown. He is afraid of them."
    discourseSegments := ["John didn't get a dog from the animal shelter downtown.", "He is afraid of them."]
    glossedTokens := []
    translation := "John didn't get a dog from the animal shelter downtown. He is afraid of them."
    context := "Kind anaphora: John is afraid of dogs, since dogs from the shelter downtown do not form a kind."
    judgment := .acceptable
    alternatives := []
    readings := [("afraid of dogs", .acceptable)]
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "they")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19b : LinguisticExample :=
  { id := "krifka2026_ex19b"
    source := ⟨"krifka-2026", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't get a dog from the animal shelter downtown. But Mary got one."
    discourseSegments := ["John didn't get a dog from the animal shelter downtown.", "But Mary got one."]
    glossedTokens := []
    translation := "John didn't get a dog from the animal shelter downtown. But Mary got one."
    context := "Concept anaphora: Mary got a dog from the shelter downtown, the full property of the antecedent."
    judgment := .acceptable
    alternatives := []
    readings := [("a dog from the shelter downtown", .acceptable)]
    paperFeatures := [("antecedent", "count"), ("island", "negation"), ("anaphor", "one")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex3a, ex3b, ex5a, ex5b, ex5c, ex7a, ex7b, ex8a, ex8b, ex19a, ex19b]

end Krifka2026.Examples
