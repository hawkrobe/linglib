module

public import Linglib.Data.Examples.Schema

/-!
# `Magri2009` — typed example data

Auto-generated from `Linglib/Data/Examples/Magri2009.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Magri2009.Examples`.
-/

@[expose] public section

namespace Magri2009.Examples

open Data.Examples

def ex_8a : Datum :=
  { id := "magri2009_8a"
    source := ⟨"diesing-1992", "UNVERIFIED"⟩
    reportedIn := some ⟨"magri-2009", "(8a)"⟩
    language := "stan1295"
    primaryText := "weil ja doch Feuerwehrmänner verfügbar sind."
    glossedTokens := [("weil", "since"), ("ja doch", "PARTS"), ("Feuerwehrmänner", "firemen"), ("verfügbar", "available"), ("sind", "are")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("existential", .acceptable), ("generic", .unacceptable)]
    paperFeatures := [("predicate_level", "stage"), ("position", "right")] }

def ex_8b : Datum :=
  { id := "magri2009_8b"
    source := ⟨"diesing-1992", "UNVERIFIED"⟩
    reportedIn := some ⟨"magri-2009", "(8b)"⟩
    language := "stan1295"
    primaryText := "weil Feuerwehrmänner ja doch verfügbar sind."
    glossedTokens := [("weil", "since"), ("Feuerwehrmänner", "firemen"), ("ja doch", "PARTS"), ("verfügbar", "available"), ("sind", "are")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate_level", "stage"), ("position", "left")] }

def ex_8c : Datum :=
  { id := "magri2009_8c"
    source := ⟨"diesing-1992", "UNVERIFIED"⟩
    reportedIn := some ⟨"magri-2009", "(8c)"⟩
    language := "stan1295"
    primaryText := "weil ja doch Feuerwehrmänner intelligent sind."
    glossedTokens := [("weil", "since"), ("ja doch", "PARTS"), ("Feuerwehrmänner", "firemen"), ("intelligent", "intelligent"), ("sind", "are")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate_level", "individual"), ("position", "right")] }

def ex_8d : Datum :=
  { id := "magri2009_8d"
    source := ⟨"diesing-1992", "UNVERIFIED"⟩
    reportedIn := some ⟨"magri-2009", "(8d)"⟩
    language := "stan1295"
    primaryText := "weil Feuerwehrmänner ja doch intelligent sind."
    glossedTokens := [("weil", "since"), ("Feuerwehrmänner", "firemen"), ("ja doch", "PARTS"), ("intelligent", "intelligent"), ("sind", "are")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("predicate_level", "individual"), ("position", "left")] }

def all : List Datum := [ex_8a, ex_8b, ex_8c, ex_8d]

end Magri2009.Examples
