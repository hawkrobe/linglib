module

public import Linglib.Data.Examples.Schema

/-!
# `Ogihara1989` — typed example data

Auto-generated from `Linglib/Data/Examples/Ogihara1989.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ogihara1989.Examples`.
-/

@[expose] public section

namespace Ogihara1989.Examples

def ex_46a : Datum :=
  { id := "ogihara1989_46a"
    source := ⟨"partee-1973", ""⟩
    reportedIn := some ⟨"ogihara-1989", "(46a)"⟩
    language := "stan1293"
    primaryText := "I didn't turn off the stove."
    glossedTokens := []
    context := "Uttered when the speaker is driving down the freeway."
    judgment := .acceptable
    alternatives := []
    readings := [("no past time at which I turn off the stove", .unacceptable), ("some past time at which I do not turn off the stove", .unacceptable), ("no subinterval of the contextually salient past interval at which I turn off the stove", .acceptable)]
    paperFeatures := [("use", "deictic")] }

def ex_47 : Datum :=
  { id := "ogihara1989_47"
    source := ⟨"partee-1973", ""⟩
    reportedIn := some ⟨"ogihara-1989", "(47)"⟩
    language := "stan1293"
    primaryText := "Sheila had a party last Friday, and Sam got drunk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("Sam got drunk at the time of Sheila's party", .acceptable)]
    paperFeatures := [("use", "anaphoric")] }

def ex_57 : Datum :=
  { id := "ogihara1989_57"
    source := ⟨"ogihara-1989", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill: Did you see Mary? I have to talk to her. John: Yes, I saw her, but I don't know where she is now. Bill: What time did you see her? John: Sometime this morning. I don't remember exactly when."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("John saw Mary at some time within the contextually relevant interval", .acceptable), ("John saw Mary at some past time", .unacceptable)]
    paperFeatures := [("restriction", "contextual")] }

def all : List Datum := [ex_46a, ex_47, ex_57]

end Ogihara1989.Examples
