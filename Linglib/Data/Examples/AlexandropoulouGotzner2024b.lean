import Linglib.Data.Examples.Schema

/-!
# `AlexandropoulouGotzner2024b` — typed example data

Auto-generated from `Linglib/Data/Examples/AlexandropoulouGotzner2024b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlexandropoulouGotzner2024b.Examples`.
-/

namespace AlexandropoulouGotzner2024b.Examples

open Data.Examples

def ag2024b_1 : LinguisticExample :=
  { id := "ag2024b_1"
    source := ⟨"alexandropoulou-gotzner-2024b", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not large"
    discourseSegments := []
    glossedTokens := []
    translation := "My apartment is not large"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("My apartment is small", .acceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "implicates")]
    comment := "Negative strengthening: the negated positive weak relative adjective implicates its antonym."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_2 : LinguisticExample :=
  { id := "ag2024b_2"
    source := ⟨"alexandropoulou-gotzner-2024b", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not small"
    discourseSegments := []
    glossedTokens := []
    translation := "My apartment is not small"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("My apartment is large", .unacceptable)]
    paperFeatures := [("adjective", "small"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "does_not_implicate")]
    comment := "The double negative does not give rise to negative strengthening; its implicated meaning would be evaluatively positive."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_5a : LinguisticExample :=
  { id := "ag2024b_5a"
    source := ⟨"alexandropoulou-gotzner-2024b", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not clean"
    discourseSegments := []
    glossedTokens := []
    translation := "The apartment is not clean"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The apartment is dirty", .acceptable)]
    paperFeatures := [("adjective", "clean"), ("adjectiveType", "absolute"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "entails")]
    comment := "Same sentence as (3); a negated maximum-standard absolute adjective entails its antonym."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_5b : LinguisticExample :=
  { id := "ag2024b_5b"
    source := ⟨"alexandropoulou-gotzner-2024b", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not dirty"
    discourseSegments := []
    glossedTokens := []
    translation := "The apartment is not dirty"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The apartment is clean", .acceptable)]
    paperFeatures := [("adjective", "dirty"), ("adjectiveType", "absolute"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "entails")]
    comment := "Same sentence as (4); a negated minimum-standard absolute adjective entails its antonym."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_6a : LinguisticExample :=
  { id := "ag2024b_6a"
    source := ⟨"alexandropoulou-gotzner-2024b", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not large"
    discourseSegments := []
    glossedTokens := []
    translation := "The apartment is not large"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The apartment is small", .unacceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "does_not_entail")]
    comment := "Relative antonyms leave a semantic extension gap, so the negated form does not entail the antonym."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_6b : LinguisticExample :=
  { id := "ag2024b_6b"
    source := ⟨"alexandropoulou-gotzner-2024b", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not small"
    discourseSegments := []
    glossedTokens := []
    translation := "The apartment is not small"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The apartment is large", .unacceptable)]
    paperFeatures := [("adjective", "small"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "does_not_entail")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_7a : LinguisticExample :=
  { id := "ag2024b_7a"
    source := ⟨"alexandropoulou-gotzner-2024b", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not very clean"
    discourseSegments := []
    glossedTokens := []
    translation := "The apartment is not very clean"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The apartment is dirty", .unacceptable)]
    paperFeatures := [("adjective", "clean"), ("modifier", "very"), ("adjectiveType", "absolute"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "does_not_entail")]
    comment := "The entailment to the antonym fails for modified absolute adjectives."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_7b : LinguisticExample :=
  { id := "ag2024b_7b"
    source := ⟨"alexandropoulou-gotzner-2024b", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is not pristine"
    discourseSegments := []
    glossedTokens := []
    translation := "The apartment is not pristine"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The apartment is filthy", .unacceptable), ("The apartment is dirty", .unacceptable)]
    paperFeatures := [("adjective", "pristine"), ("adjectiveType", "absolute"), ("strength", "strong"), ("polarity", "positive"), ("negation", "negated"), ("relation", "does_not_entail")]
    comment := "The entailment to the antonym fails for stronger scale-mates: the sentence is compatible with the apartment being clean, dirty or filthy."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_9 : LinguisticExample :=
  { id := "ag2024b_9"
    source := ⟨"alexandropoulou-gotzner-2024b", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The apartment is large"
    discourseSegments := []
    glossedTokens := []
    translation := "The apartment is large"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("The apartment is large but not gigantic", .acceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "nonNegated"), ("relation", "implicates")]
    comment := "Q-based upper-bounding implicature: gigantic asymmetrically entails large."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_10 : LinguisticExample :=
  { id := "ag2024b_10"
    source := ⟨"alexandropoulou-gotzner-2024b", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not large."
    discourseSegments := []
    glossedTokens := []
    translation := "My apartment is not large."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("My apartment is small", .acceptable)]
    paperFeatures := [("adjective", "large"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "positive"), ("negation", "negated"), ("relation", "implicates"), ("inference", "negative_strengthening")]
    comment := "Horn's R-based implicature: the speaker conceals the stronger negative meaning of the simple antonym."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def ag2024b_11 : LinguisticExample :=
  { id := "ag2024b_11"
    source := ⟨"alexandropoulou-gotzner-2024b", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My apartment is not small."
    discourseSegments := []
    glossedTokens := []
    translation := "My apartment is not small."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("My apartment is neither large nor small", .acceptable)]
    paperFeatures := [("adjective", "small"), ("adjectiveType", "relative"), ("strength", "weak"), ("polarity", "negative"), ("negation", "negated"), ("relation", "implicates"), ("inference", "middling")]
    comment := "Horn's Q/R-based middling interpretation: the prolix double negative conveys the extension gap."
    metaLanguage := "stan1293"
    lgrConformance := "NONE" }

def all : List LinguisticExample := [ag2024b_1, ag2024b_2, ag2024b_5a, ag2024b_5b, ag2024b_6a, ag2024b_6b, ag2024b_7a, ag2024b_7b, ag2024b_9, ag2024b_10, ag2024b_11]

end AlexandropoulouGotzner2024b.Examples
