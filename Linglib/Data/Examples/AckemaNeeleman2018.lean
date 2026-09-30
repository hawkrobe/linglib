module

public import Linglib.Data.Examples.Schema

/-!
# `AckemaNeeleman2018` — typed example data

Auto-generated from `Linglib/Data/Examples/AckemaNeeleman2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AckemaNeeleman2018.Examples`.
-/

@[expose] public section

namespace AckemaNeeleman2018.Examples

open Data.Examples

def ex_2a : LinguisticExample :=
  { id := "ackemaneeleman2018_2a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Mary has left for Paris."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third")] }

def ex_2b : LinguisticExample :=
  { id := "ackemaneeleman2018_2b"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is raining again in Edinburgh."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third")] }

def ex_20a : LinguisticExample :=
  { id := "ackemaneeleman2018_20a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck!"
    glossedTokens := []
    context := "John discovers he has a winning lottery ticket and talks to himself."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk"), ("roles", "i and u co-incide")] }

def ex_21a : LinguisticExample :=
  { id := "ackemaneeleman2018_21a"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I can't believe your luck! If we hurry, we can still collect the money today."
    glossedTokens := []
    context := "John discovers he has a winning lottery ticket and talks to himself."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "self-talk"), ("person", "first plural")] }

def ex_24 : LinguisticExample :=
  { id := "ackemaneeleman2018_24"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It seems that Vitesse won."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("It seem that Vitesse won.", .ungrammatical), ("I seem that Vitesse won.", .ungrammatical), ("You seem that Vitesse won.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("person", "third singular")] }

def ex_25 : LinguisticExample :=
  { id := "ackemaneeleman2018_25"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (25)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Nog jaren is naar een oplossing gezocht."
    glossedTokens := [("Nog", "still"), ("jaren", "years"), ("is", "be.3SG"), ("naar", "for"), ("een", "a"), ("oplossing", "solution"), ("gezocht", "searched")]
    context := ""
    judgment := .acceptable
    alternatives := [("Nog jaren ben naar een oplossing gezocht.", .ungrammatical), ("Nog jaren bent naar een oplossing gezocht.", .ungrammatical), ("Nog jaren zijn naar een oplossing gezocht.", .ungrammatical)]
    readings := []
    paperFeatures := [("phenomenon", "default agreement"), ("construction", "impersonal passive")] }

def ex_30 : LinguisticExample :=
  { id := "ackemaneeleman2018_30"
    source := ⟨"ackema-neeleman-2018", "ch. 2 (30)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Men schijnt dat men regent."
    glossedTokens := [("Men", "one"), ("schijnt", "seems"), ("dat", "that"), ("men", "one"), ("regent", "rains")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expletive"), ("pronoun", "featureless impersonal")] }

def all : List LinguisticExample := [ex_2a, ex_2b, ex_20a, ex_21a, ex_24, ex_25, ex_30]

end AckemaNeeleman2018.Examples
