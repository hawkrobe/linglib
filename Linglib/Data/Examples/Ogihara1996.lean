module

public import Linglib.Data.Examples.Schema

/-!
# `Ogihara1996` — typed example data

Auto-generated from `Linglib/Data/Examples/Ogihara1996.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ogihara1996.Examples`.
-/

@[expose] public section

namespace Ogihara1996.Examples

def ex2a : Datum :=
  { id := "ogihara1996_ex2a"
    source := ⟨"ogihara-1996", "ch. 3, (2a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byooki-da-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-da", "be-sick-PRES"), ("-to", "that"), ("it-ta", "say-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (Hanako sick at saying time)", .acceptable), ("shifted (Hanako sick before saying)", .ungrammatical)]
    paperFeatures := [] }

def ex2b : Datum :=
  { id := "ogihara1996_ex2b"
    source := ⟨"ogihara-1996", "ch. 3, (2b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byookidat-ta-to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byookidat-ta", "be-sick-PAST"), ("-to", "that"), ("it-ta", "say-PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("shifted (Hanako sick before saying)", .acceptable), ("simultaneous (Hanako sick at saying time)", .ungrammatical)]
    paperFeatures := [] }

def ex19d : Datum :=
  { id := "ogihara1996_ex19d"
    source := ⟨"ogihara-1996", "ch. 1, (19d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said that Mary had been reading books yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Mary's reading at yesterday (definite past)", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex2a, ex2b, ex19d]

end Ogihara1996.Examples
