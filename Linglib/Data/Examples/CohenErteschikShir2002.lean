module

public import Linglib.Data.Examples.Schema

/-!
# `CohenErteschikShir2002` — typed example data

Auto-generated from `Linglib/Data/Examples/CohenErteschikShir2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace CohenErteschikShir2002.Examples`.
-/

@[expose] public section

namespace CohenErteschikShir2002.Examples

open Data.Examples

def boys_brave : Datum :=
  { id := "cohenerteschikshir2002_boys_brave"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Boys are brave."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .unacceptable)]
    paperFeatures := [("predicate_level", "individual")] }

def italians_good_looking : Datum :=
  { id := "cohenerteschikshir2002_italians_good_looking"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Italians are good-looking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .unacceptable)]
    paperFeatures := [("predicate_level", "individual")] }

def lawyers_intelligent : Datum :=
  { id := "cohenerteschikshir2002_lawyers_intelligent"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lawyers are intelligent."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .unacceptable)]
    paperFeatures := [("predicate_level", "individual")] }

def boys_present : Datum :=
  { id := "cohenerteschikshir2002_boys_present"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Boys are present."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")] }

def firemen_available : Datum :=
  { id := "cohenerteschikshir2002_firemen_available"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Firemen are available."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")] }

def soldiers_arrived : Datum :=
  { id := "cohenerteschikshir2002_soldiers_arrived"
    source := ⟨"cohen-erteschik-shir-2002", "UNVERIFIED §2.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Soldiers arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("generic", .acceptable), ("existential", .acceptable)]
    paperFeatures := [("predicate_level", "stage"), ("locative_status", "argument")] }

def all : List Datum := [boys_brave, italians_good_looking, lawyers_intelligent, boys_present, firemen_available, soldiers_arrived]

end CohenErteschikShir2002.Examples
