module

public import Linglib.Data.Examples.Schema

/-!
# `TesslerFranke2019` — typed example data

Auto-generated from `Linglib/Data/Examples/TesslerFranke2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TesslerFranke2019.Examples`.
-/

@[expose] public section

namespace TesslerFranke2019.Examples

open Data.Examples

def happy : Datum :=
  { id := "tesslerfranke2019_happy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED quadruplet, bare positive"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is happy."
    glossedTokens := []
    context := "Bare positive of the happy/unhappy quadruplet. Baseline against which the three negated forms are compared."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "positive"), ("inner_neg", "none"), ("cost", "0"), ("equivalent_to_positive", "true")] }

def unhappy : Datum :=
  { id := "tesslerfranke2019_unhappy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED Experiment 1, morphological negation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is unhappy."
    glossedTokens := []
    context := "Morphological negation prefers the contrary (polar-opposite) interpretation: 'unhappy' means positively unhappy (below a low threshold), not merely 'not happy'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "negative"), ("inner_neg", "morphological"), ("interpretation", "contrary"), ("cost", "2"), ("equivalent_to_positive", "false")] }

def not_happy : Datum :=
  { id := "tesslerfranke2019_not_happy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED Experiment 1, syntactic negation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is not happy."
    glossedTokens := []
    context := "Syntactic negation is flexible between contradictory and contrary readings; the costlier two-word form licenses the marked contradictory reading more readily than 'unhappy' (Horn's division of pragmatic labor)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "notPositive"), ("inner_neg", "syntactic"), ("interpretation", "contradictory"), ("cost", "3"), ("equivalent_to_positive", "false")] }

def not_unhappy : Datum :=
  { id := "tesslerfranke2019_not_unhappy"
    source := ⟨"tessler-franke-2019", "UNVERIFIED §1, double negation"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She is not unhappy."
    glossedTokens := []
    context := "The paper's central observation: 'not unhappy' does NOT reduce to 'happy'. The inner morphological negation is contrary, so 'not unhappy' covers the gap region between the negative and positive thresholds, where 'happy' is false."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "notNegative"), ("inner_neg", "morphological"), ("interpretation", "contrary"), ("cost", "5"), ("equivalent_to_positive", "false")] }

def all : List Datum := [happy, unhappy, not_happy, not_unhappy]

end TesslerFranke2019.Examples
