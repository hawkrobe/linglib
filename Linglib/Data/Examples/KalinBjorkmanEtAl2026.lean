module

public import Linglib.Data.Examples.Schema

/-!
# `KalinBjorkmanEtAl2026` — typed example data

Auto-generated from `Linglib/Data/Examples/KalinBjorkmanEtAl2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KalinBjorkmanEtAl2026.Examples`.
-/

@[expose] public section

namespace KalinBjorkmanEtAl2026.Examples

open Data.Examples

def kb2026_cat : Datum :=
  { id := "kb2026_cat"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "cat"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "free"), ("p", "free"), ("cell", "canonicalWord")] }

def kb2026_plural_s : Datum :=
  { id := "kb2026_plural_s"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "-s (plural)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "bound"), ("p", "bound"), ("cell", "canonicalAffix")] }

def kb2026_possessive_s : Datum :=
  { id := "kb2026_possessive_s"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'s (possessive)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "free"), ("p", "bound"), ("cell", "simpleClitic")] }

def kb2026_dutch_prefix : Datum :=
  { id := "kb2026_dutch_prefix"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Dutch prefixes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "bound"), ("p", "free"), ("cell", "nonCoheringAffix")] }

def kb2026_cat_form : Datum :=
  { id := "kb2026_cat_form"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "cat /kæt/"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "oneToOne")] }

def kb2026_plural_allomorphy : Datum :=
  { id := "kb2026_plural_allomorphy"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dog-z, ox-ən, sheep-∅"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "allomorphy")] }

def kb2026_amharic_plural : Datum :=
  { id := "kb2026_amharic_plural"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "amha1245"
    primaryText := "k'al-at-otʃtʃ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "multipleExponence")] }

def kb2026_ed : Datum :=
  { id := "kb2026_ed"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "-ed (past tense, passive participle)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "syncretism")] }

def kb2026_am : Datum :=
  { id := "kb2026_am"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "am"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "portmanteau")] }

def kb2026_stride : Datum :=
  { id := "kb2026_stride"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "stride (no past participle)"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "morphologicalGap")] }

def kb2026_theme_vowel : Datum :=
  { id := "kb2026_theme_vowel"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "roma1334"
    primaryText := "Romance theme vowel"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "emptyMorph")] }

def all : List Datum := [kb2026_cat, kb2026_plural_s, kb2026_possessive_s, kb2026_dutch_prefix, kb2026_cat_form, kb2026_plural_allomorphy, kb2026_amharic_plural, kb2026_ed, kb2026_am, kb2026_stride, kb2026_theme_vowel]

end KalinBjorkmanEtAl2026.Examples
