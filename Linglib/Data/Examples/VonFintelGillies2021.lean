module

public import Linglib.Data.Examples.Schema

/-!
# `VonFintelGillies2021` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintelGillies2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintelGillies2021.Examples`.
-/

@[expose] public section

namespace VonFintelGillies2021.Examples

open Data.Examples

def cant_possible : Datum :=
  { id := "vonfintelgillies2021_cant_possible"
    source := ⟨"von-fintel-gillies-2021", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suppose it's possible the keys are in the drawer but they can't be."
    glossedTokens := []
    context := "Flat-footed conjunction of 'possible phi' with 'can't phi', embedded under suppose."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "inference"), ("pattern", "cant_possible_contradiction"), ("modal", "cant")] }

def phil_dinner : Datum :=
  { id := "vonfintelgillies2021_phil_dinner"
    source := ⟨"von-fintel-gillies-2021", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinner must be ready."
    glossedTokens := []
    context := "Phil has cooked the dinner, checking all the food himself, and knows it is ready."
    judgment := .unacceptable
    alternatives := [("Dinner is ready.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "direct"), ("must_entails_prejacent", "true")] }

def meryl_dinner : Datum :=
  { id := "vonfintelgillies2021_meryl_dinner"
    source := ⟨"von-fintel-gillies-2021", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Dinner must be ready."
    glossedTokens := []
    context := "Meryl followed the recipe's instructions but has not checked everything herself and wonders whether anything more was planned."
    judgment := .acceptable
    alternatives := [("Dinner is ready.", .acceptable)]
    readings := []
    paperFeatures := [("kind", "must_pair"), ("modal", "must"), ("evidence", "indirect"), ("must_entails_prejacent", "true")] }

def all : List Datum := [cant_possible, phil_dinner, meryl_dinner]

end VonFintelGillies2021.Examples
