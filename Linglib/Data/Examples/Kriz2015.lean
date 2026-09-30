module

public import Linglib.Data.Examples.Schema

/-!
# `Kriz2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Kriz2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kriz2015.Examples`.
-/

@[expose] public section

namespace Kriz2015.Examples

open Data.Examples

def switches_pos_gap : LinguisticExample :=
  { id := "kriz2015_switches_pos_gap"
    source := ⟨"kriz-2015", "canonical switches homogeneity item"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The switches are on."
    glossedTokens := [("The", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("on", "on")]
    context := "Ten switches; 5 of the 10 switches are on."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("gap_detected", "true")] }

def switches_neg_gap : LinguisticExample :=
  { id := "kriz2015_switches_neg_gap"
    source := ⟨"kriz-2015", "canonical switches homogeneity item, negated"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The switches are not on."
    glossedTokens := [("The", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("not", "NEG"), ("on", "on")]
    context := "Ten switches; 5 of the 10 switches are on."
    judgment := .questionable
    alternatives := [("It's not the case that the switches are on.", .questionable)]
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("gap_detected", "true")] }

def switches_nonmax_existential : LinguisticExample :=
  { id := "kriz2015_switches_nonmax_existential"
    source := ⟨"kriz-2015", "(11) switches non-maximality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Oh no, the switches are on!"
    glossedTokens := [("Oh", "oh"), ("no", "no"), ("the", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("on", "on")]
    context := "Fire risk if any switch is on; 2 of the 10 switches are on. Implicit question: Are any of the switches on?"
    judgment := .acceptable
    alternatives := [("Oh no, all the switches are on!", .unacceptable)]
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("issue", "existential")] }

def switches_nonmax_universal : LinguisticExample :=
  { id := "kriz2015_switches_nonmax_universal"
    source := ⟨"kriz-2015", "(11) switches non-maximality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Oh no, the switches are on!"
    glossedTokens := [("Oh", "oh"), ("no", "no"), ("the", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("on", "on")]
    context := "Fire risk only if all 10 switches are on; 2 of the 10 switches are on. Implicit question: Are all the switches on?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("issue", "universal")] }

def all : List LinguisticExample := [switches_pos_gap, switches_neg_gap, switches_nonmax_existential, switches_nonmax_universal]

end Kriz2015.Examples
