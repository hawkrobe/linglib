module

public import Linglib.Data.Examples.Schema

/-!
# `HaslingerHienEtAl2025` — typed example data

Auto-generated from `Linglib/Data/Examples/HaslingerHienEtAl2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HaslingerHienEtAl2025.Examples`.
-/

@[expose] public section

namespace HaslingerHienEtAl2025.Examples

open Data.Examples

def ex_71a : LinguisticExample :=
  { id := "haslingerhienetal2025_71a"
    source := ⟨"haslinger-etal-2025-nllt", "(71a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A train arrives every ten minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "A train arrives every ten minutes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "nonOverlap"), ("form", "every")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_71b : LinguisticExample :=
  { id := "haslingerhienetal2025_71b"
    source := ⟨"haslinger-etal-2025-nllt", "(71b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Alle zehn Minuten kommt ein Zug."
    discourseSegments := []
    glossedTokens := [("Alle", "UQ"), ("zehn", "ten"), ("Minuten", "minute.PL"), ("kommt", "come.3SG"), ("ein", "a"), ("Zug.", "train")]
    translation := "Every ten minutes, a train arrives."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "bare"), ("form", "alle")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_73a : LinguisticExample :=
  { id := "haslingerhienetal2025_73a"
    source := ⟨"haslinger-etal-2025-nllt", "(73a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "every ten minutes"
    discourseSegments := []
    glossedTokens := []
    translation := "every ten minutes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "nonOverlap"), ("form", "every")]
    comment := "Annotated [+dist] in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_73b : LinguisticExample :=
  { id := "haslingerhienetal2025_73b"
    source := ⟨"haslinger-etal-2025-nllt", "(73b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "each ten minutes"
    discourseSegments := []
    glossedTokens := []
    translation := "each ten minutes"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("structure", "atomic"), ("form", "each")]
    comment := "Starred and annotated [+dist] in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_74a : LinguisticExample :=
  { id := "haslingerhienetal2025_74a"
    source := ⟨"haslinger-etal-2025-nllt", "(74a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "alle zehn Minuten"
    discourseSegments := []
    glossedTokens := [("alle", "UQ"), ("zehn", "ten"), ("Minuten", "minute.PL")]
    translation := "every ten minutes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "bare"), ("form", "alle")]
    comment := "Annotated [-dist] in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_74b : LinguisticExample :=
  { id := "haslingerhienetal2025_74b"
    source := ⟨"haslinger-etal-2025-nllt", "(74b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "jede zehn Minuten"
    discourseSegments := []
    glossedTokens := [("jede", "UQ"), ("zehn", "ten"), ("Minuten", "minute.PL")]
    translation := "every ten minutes"
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("structure", "atomicOnly"), ("form", "jeder")]
    comment := "Marked % and annotated [+dist] in the paper, which notes that the oddness is subject to variation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_71a, ex_71b, ex_73a, ex_73b, ex_74a, ex_74b]

end HaslingerHienEtAl2025.Examples
