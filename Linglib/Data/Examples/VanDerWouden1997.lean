module

public import Linglib.Data.Examples.Schema

/-!
# `VanDerWouden1997` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerWouden1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerWouden1997.Examples`.
-/

@[expose] public section

namespace VanDerWouden1997.Examples

def ex_184a : Datum :=
  { id := "vanderwouden1997_184a"
    source := ⟨"vanderwouden-1997", "(184a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Een van de kinderen gaat ooit bij oma op bezoek."
    glossedTokens := [("Een", "one"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "notMonotoneDecreasing")] }

def ex_184b : Datum :=
  { id := "vanderwouden1997_184b"
    source := ⟨"vanderwouden-1997", "(184b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Weinig kinderen gaan ooit bij oma op bezoek."
    glossedTokens := [("Weinig", "few"), ("kinderen", "children"), ("gaan", "go"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "monotoneDecreasing")] }

def ex_184c : Datum :=
  { id := "vanderwouden1997_184c"
    source := ⟨"vanderwouden-1997", "(184c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Geen van de kinderen gaat ooit bij oma op bezoek."
    glossedTokens := [("Geen", "none"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "antiAdditive")] }

def ex_184d : Datum :=
  { id := "vanderwouden1997_184d"
    source := ⟨"vanderwouden-1997", "(184d)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Een van de kinderen gaat niet ooit bij oma op bezoek."
    glossedTokens := [("Een", "one"), ("van", "of"), ("de", "the"), ("kinderen", "children"), ("gaat", "goes"), ("niet", "not"), ("ooit", "ever"), ("bij", "with"), ("oma", "granny"), ("op", "on"), ("bezoek", "visit")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "ooit"), ("context", "antimorphic")] }

def all : List Datum := [ex_184a, ex_184b, ex_184c, ex_184d]

end VanDerWouden1997.Examples
