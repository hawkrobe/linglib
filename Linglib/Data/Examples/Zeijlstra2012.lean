module

public import Linglib.Data.Examples.Schema

/-!
# `Zeijlstra2012` — typed example data

Auto-generated from `Linglib/Data/Examples/Zeijlstra2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zeijlstra2012.Examples`.
-/

@[expose] public section

namespace Zeijlstra2012.Examples

def ex_20a : Datum :=
  { id := "zeijlstra2012_20a"
    source := ⟨"zeijlstra-2012", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said Mary was ill"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sequence of tense")] }

def ex_20b : Datum :=
  { id := "zeijlstra2012_20b"
    source := ⟨"zeijlstra-2012", "(20b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Jan zei dat Marie ziek was"
    glossedTokens := [("Jan", "John"), ("zei", "said"), ("dat", "that"), ("Marie", "Mary"), ("ziek", "ill"), ("was", "was")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "sequence of tense")] }

def ex_21 : Datum :=
  { id := "zeijlstra2012_21"
    source := ⟨"zeijlstra-2012", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wolfgang played tennis on every Sunday"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "tense scope")] }

def ex_50a : Datum :=
  { id := "zeijlstra2012_50a"
    source := ⟨"zeijlstra-2012", "(50a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non ha detto niente a nessuno"
    glossedTokens := [("Gianni", "Gianni"), ("non", "NEG"), ("ha", "has"), ("detto", "said"), ("niente", "n-thing"), ("a", "to"), ("nessuno", "n-body")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("type", "non-strict")] }

def ex_51a : Datum :=
  { id := "zeijlstra2012_51a"
    source := ⟨"zeijlstra-2012", "(51a)"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Dnes nikdo nevolá nikomu"
    glossedTokens := [("Dnes", "today"), ("nikdo", "n-body"), ("nevolá", "NEG.calls"), ("nikomu", "n-body")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("type", "strict")] }

def ex_53 : Datum :=
  { id := "zeijlstra2012_53"
    source := ⟨"zeijlstra-2012", "(53)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni non ha detto che ha telefonato a nessuno"
    glossedTokens := [("Gianni", "Gianni"), ("non", "NEG"), ("ha", "has"), ("detto", "said"), ("che", "that"), ("ha", "has"), ("telefonato", "called"), ("a", "to"), ("nessuno", "n-body")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "negative concord"), ("locality", "across CP")] }

def all : List Datum := [ex_20a, ex_20b, ex_21, ex_50a, ex_51a, ex_53]

end Zeijlstra2012.Examples
