module

public import Linglib.Data.Examples.Schema

/-!
# `ShenHuang2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ShenHuang2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ShenHuang2026.Examples`.
-/

@[expose] public section

namespace ShenHuang2026.Examples

def ex3a : Datum :=
  { id := "shenhuang2026_ex3a"
    source := ⟨"shen-huang-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you compose a song about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("object", "indefinite"), ("creation", "yes")] }

def ex3b : Datum :=
  { id := "shenhuang2026_ex3b"
    source := ⟨"shen-huang-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you compose that song about?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("object", "definite"), ("creation", "yes")] }

def ex28_indefinite : Datum :=
  { id := "shenhuang2026_ex28_indefinite"
    source := ⟨"li-1992", "(54)"⟩
    reportedIn := some ⟨"shen-huang-2026", "(28)"⟩
    language := "mand1415"
    primaryText := "Wǒ yǐwéi tā ná-le shénme rén de xiàngpiàn"
    glossedTokens := [("Wǒ", "I"), ("yǐwéi", "mistakenly.believe"), ("tā", "he"), ("ná-le", "take.away-PERF"), ("shénme", "what"), ("rén", "man"), ("de", "DE"), ("xiàngpiàn", "picture")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "binding"), ("object", "indefinite"), ("creation", "no")] }

def ex28_definite : Datum :=
  { id := "shenhuang2026_ex28_definite"
    source := ⟨"li-1992", "(54)"⟩
    reportedIn := some ⟨"shen-huang-2026", "(28)"⟩
    language := "mand1415"
    primaryText := "Wǒ yǐwéi tā ná-le nà-zhāng shénme rén de xiàngpiàn"
    glossedTokens := [("Wǒ", "I"), ("yǐwéi", "mistakenly.believe"), ("tā", "he"), ("ná-le", "take.away-PERF"), ("nà-zhāng", "that-CL"), ("shénme", "what"), ("rén", "man"), ("de", "DE"), ("xiàngpiàn", "picture")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "binding"), ("object", "definite"), ("creation", "no")] }

def all : List Datum := [ex3a, ex3b, ex28_indefinite, ex28_definite]

end ShenHuang2026.Examples
