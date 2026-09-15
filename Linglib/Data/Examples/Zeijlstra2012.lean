import Linglib.Data.Examples.Schema

/-!
# `Zeijlstra2012` — typed example data

Auto-generated from `Linglib/Data/Examples/Zeijlstra2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zeijlstra2012.Examples`.
-/

namespace Zeijlstra2012.Examples

open Data.Examples

def ex_20a : LinguisticExample :=
  { id := "zeijlstra2012_20a"
    source := ⟨"zeijlstra-2012", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said Mary was ill"
    discourseSegments := []
    glossedTokens := []
    translation := "John said Mary was ill"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sequence of tense")]
    comment := "The subordinate past does not introduce a semantic past of its own; the sentence allows a simultaneous and a back-shifted reading but no forward shift."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20b : LinguisticExample :=
  { id := "zeijlstra2012_20b"
    source := ⟨"zeijlstra-2012", "(20b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan zei dat Marie ziek was"
    discourseSegments := []
    glossedTokens := [("Jan", "John"), ("zei", "said"), ("dat", "that"), ("Marie", "Mary"), ("ziek", "ill"), ("was", "was")]
    translation := "John said Mary was ill"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sequence of tense")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "zeijlstra2012_21"
    source := ⟨"zeijlstra-2012", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wolfgang played tennis on every Sunday"
    discourseSegments := []
    glossedTokens := []
    translation := "Wolfgang played tennis on every Sunday"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "tense scope")]
    comment := "The quantifier scopes between the past tense and the verb, so the past morpheme is not itself the semantic past operator."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_50a : LinguisticExample :=
  { id := "zeijlstra2012_50a"
    source := ⟨"zeijlstra-2012", "(50a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non ha detto niente a nessuno"
    discourseSegments := []
    glossedTokens := [("Gianni", "Gianni"), ("non", "NEG"), ("ha", "has"), ("detto", "said"), ("niente", "n-thing"), ("a", "to"), ("nessuno", "n-body")]
    translation := "Gianni didn't say anything to anybody"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("type", "non-strict")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_51a : LinguisticExample :=
  { id := "zeijlstra2012_51a"
    source := ⟨"zeijlstra-2012", "(51a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dnes nikdo nevolá nikomu"
    discourseSegments := []
    glossedTokens := [("Dnes", "today"), ("nikdo", "n-body"), ("nevolá", "NEG.calls"), ("nikomu", "n-body")]
    translation := "Today nobody is calling anybody"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("type", "strict")]
    comment := "The negative marker is obligatory; without it the sentence is out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_53 : LinguisticExample :=
  { id := "zeijlstra2012_53"
    source := ⟨"zeijlstra-2012", "(53)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non ha detto che ha telefonato a nessuno"
    discourseSegments := []
    glossedTokens := [("Gianni", "Gianni"), ("non", "NEG"), ("ha", "has"), ("detto", "said"), ("che", "that"), ("ha", "has"), ("telefonato", "called"), ("a", "to"), ("nessuno", "n-body")]
    translation := "John didn't say that he called anybody"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("locality", "across CP")]
    comment := "Negative Concord does not cross the embedded clause boundary, unlike Sequence of Tense."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_20a, ex_20b, ex_21, ex_50a, ex_51a, ex_53]

end Zeijlstra2012.Examples
