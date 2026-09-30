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

open Data.Examples

def ex2a : Datum :=
  { id := "ogihara1996_ex2a"
    source := ⟨"ogihara-1996", "(2a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byooki-da to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byooki-da", "be.sick-PRES"), ("to", "COMP"), ("it-ta", "say-PAST")]
    context := "Past matrix + PRESENT embedded → simultaneous reading. In non-SOT Japanese, the embedded clause uses present (`-da`) to express simultaneity with the saying time; the embedded clause's tense is interpreted relative to speech time, so PRESENT here is anchored to the saying time via attitude-context shift, not to speech time."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (Hanako sick at saying time)", .acceptable), ("shifted (Hanako sick before saying)", .ungrammatical)]
    paperFeatures := [] }

def ex2b : Datum :=
  { id := "ogihara1996_ex2b"
    source := ⟨"ogihara-1996", "(2b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-wa Hanako-ga byookidat-ta to it-ta."
    glossedTokens := [("Taroo-wa", "Taro-TOP"), ("Hanako-ga", "Hanako-NOM"), ("byookidat-ta", "be.sick-PAST"), ("to", "COMP"), ("it-ta", "say-PAST")]
    context := "Past matrix + PAST embedded → ONLY shifted reading. Hanako's sickness strictly precedes the saying. No simultaneous reading is available — sharply diagnostic of non-SOT Japanese vs SOT English."
    judgment := .acceptable
    alternatives := []
    readings := [("shifted (Hanako sick before saying)", .acceptable), ("simultaneous (Hanako sick at saying time)", .ungrammatical)]
    paperFeatures := [] }

def ex19d : Datum :=
  { id := "ogihara1996_ex19d"
    source := ⟨"ogihara-1996", "(19d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said that Mary had been reading books yesterday."
    glossedTokens := []
    context := "English past perfect under past matrix. The adverbial `yesterday` denotes a definite past interval and restricts the embedded event's temporal location — solid evidence that the perfect can be used as a preterit."
    judgment := .acceptable
    alternatives := []
    readings := [("Mary's reading at yesterday (definite past)", .acceptable)]
    paperFeatures := [] }

def all : List Datum := [ex2a, ex2b, ex19d]

end Ogihara1996.Examples
