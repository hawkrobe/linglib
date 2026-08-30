import Linglib.Data.Examples.Schema

/-!
# `BarAsherSiegal2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BarAsherSiegal2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BarAsherSiegal2026.Examples`.
-/

namespace BarAsherSiegal2026.Examples

open Data.Examples

def bas2026_1a : LinguisticExample :=
  { id := "bas2026_1a"
    source := ⟨"bar-asher-siegal-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A kangaroo is a marsupial because it has a pouch."
    discourseSegments := []
    glossedTokens := []
    translation := "A kangaroo is a marsupial because it has a pouch."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "because"), ("relation", "grounding")]
    comment := "Dowty 1979, example 132b: dependency without temporal precedence and counterfactuality."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bas2026_1b : LinguisticExample :=
  { id := "bas2026_1b"
    source := ⟨"bar-asher-siegal-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary's living nearby causes John to prefer this neighborhood."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary's living nearby causes John to prefer this neighborhood."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cause"), ("relation", "grounding")]
    comment := "Dowty 1979, example 132c."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bas2026_1c : LinguisticExample :=
  { id := "bas2026_1c"
    source := ⟨"bar-asher-siegal-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The floor is black because of the ants that might infest it."
    discourseSegments := []
    glossedTokens := []
    translation := "The floor is black because of the ants that might infest it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "because of"), ("relation", "grounding")]
    comment := "Adapted from Maienborn and Herdtfelder 2017."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bas2026_2a : LinguisticExample :=
  { id := "bas2026_2a"
    source := ⟨"bar-asher-siegal-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam opened the door."
    discourseSegments := []
    glossedTokens := []
    translation := "Sam opened the door."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "lexical causative"), ("entails", "(2b)")]
    comment := "Fodor 1970's one-way entailment."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bas2026_2b : LinguisticExample :=
  { id := "bas2026_2b"
    source := ⟨"bar-asher-siegal-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sam caused the door to open."
    discourseSegments := []
    glossedTokens := []
    translation := "Sam caused the door to open."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Sam opened a window and a gust blew the door open", .acceptable)]
    paperFeatures := [("construction", "periphrastic causative"), ("entails", "(2a)")]
    comment := "Does not entail (2a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bas2026_i : LinguisticExample :=
  { id := "bas2026_i"
    source := ⟨"bar-asher-siegal-2026", "(i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The city council denied the demonstrators the permit because they advocated violence."
    discourseSegments := []
    glossedTokens := []
    translation := "The city council denied the demonstrators the permit because they advocated violence."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "because"), ("pronoun", "they"), ("antecedent", "the demonstrators")]
    comment := "Hobbs 1979, discussed in Wolf et al. 2004."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bas2026_ii : LinguisticExample :=
  { id := "bas2026_ii"
    source := ⟨"bar-asher-siegal-2026", "(ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The city council denied the demonstrators the permit because they feared violence."
    discourseSegments := []
    glossedTokens := []
    translation := "The city council denied the demonstrators the permit because they feared violence."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "because"), ("pronoun", "they"), ("antecedent", "the city council")]
    comment := "Hobbs 1979."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bas2026_iii : LinguisticExample :=
  { id := "bas2026_iii"
    source := ⟨"bar-asher-siegal-2026", "(iii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John drank wine at the party, which caused the accident he was involved in later that night as he drove back home."
    discourseSegments := []
    glossedTokens := []
    translation := "John drank wine at the party, which caused the accident he was involved in later that night as he drove back home."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "cause"), ("enrichment", "John drank enough wine to impair his driving")]
    comment := "Bar-Asher Siegal 2020: the causal context enriches the first clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [bas2026_1a, bas2026_1b, bas2026_1c, bas2026_2a, bas2026_2b, bas2026_i, bas2026_ii, bas2026_iii]

end BarAsherSiegal2026.Examples
