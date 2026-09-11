import Linglib.Data.Examples.Schema

/-!
# `KalinBjorkmanEtAl2026` — typed example data

Auto-generated from `Linglib/Data/Examples/KalinBjorkmanEtAl2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KalinBjorkmanEtAl2026.Examples`.
-/

namespace KalinBjorkmanEtAl2026.Examples

open Data.Examples

def kb2026_cat : LinguisticExample :=
  { id := "kb2026_cat"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "cat"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "free"), ("p", "free"), ("cell", "canonicalWord")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_plural_s : LinguisticExample :=
  { id := "kb2026_plural_s"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "-s (plural)"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "bound"), ("p", "bound"), ("cell", "canonicalAffix")]
    comment := "Combines only with nouns."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_possessive_s : LinguisticExample :=
  { id := "kb2026_possessive_s"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'s (possessive)"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "free"), ("p", "bound"), ("cell", "simpleClitic")]
    comment := "No morphosyntactic relationship with the word it is phonologically bound to: the dean who I had a Zoom call with's cat."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_dutch_prefix : LinguisticExample :=
  { id := "kb2026_dutch_prefix"
    source := ⟨"kalin-bjorkman-etal-2026", "Table 3"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Dutch prefixes"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.3"), ("ms", "bound"), ("p", "free"), ("cell", "nonCoheringAffix")]
    comment := "All Dutch prefixes are non-cohering; suffixes may be cohering or non-cohering (Booij 1995)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_cat_form : LinguisticExample :=
  { id := "kb2026_cat_form"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "cat /kæt/"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "oneToOne")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_plural_allomorphy : LinguisticExample :=
  { id := "kb2026_plural_allomorphy"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dog-z, ox-ən, sheep-∅"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "allomorphy")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_amharic_plural : LinguisticExample :=
  { id := "kb2026_amharic_plural"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "amha1245"
    primaryText := "k'al-at-otʃtʃ"
    discourseSegments := []
    glossedTokens := []
    translation := "word-PL-PL"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "multipleExponence")]
    comment := "Two plural suffixes, one plural interpretation (Kramer 2016)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_ed : LinguisticExample :=
  { id := "kb2026_ed"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "-ed (past tense, passive participle)"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "syncretism")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_am : LinguisticExample :=
  { id := "kb2026_am"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "am"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "portmanteau")]
    comment := "1st person, singular, present, copula."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_stride : LinguisticExample :=
  { id := "kb2026_stride"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "stride (no past participle)"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "morphologicalGap")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kb2026_theme_vowel : LinguisticExample :=
  { id := "kb2026_theme_vowel"
    source := ⟨"kalin-bjorkman-etal-2026", "4"⟩
    reportedIn := none
    language := ""
    primaryText := "Romance theme vowel"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("mapping", "emptyMorph")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [kb2026_cat, kb2026_plural_s, kb2026_possessive_s, kb2026_dutch_prefix, kb2026_cat_form, kb2026_plural_allomorphy, kb2026_amharic_plural, kb2026_ed, kb2026_am, kb2026_stride, kb2026_theme_vowel]

end KalinBjorkmanEtAl2026.Examples
