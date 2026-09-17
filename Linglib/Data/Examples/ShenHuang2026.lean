import Linglib.Data.Examples.Schema

/-!
# `ShenHuang2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ShenHuang2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ShenHuang2026.Examples`.
-/

namespace ShenHuang2026.Examples

open Data.Examples

def ex3a : LinguisticExample :=
  { id := "shenhuang2026_ex3a"
    source := ⟨"shen-huang-2026", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you compose a song about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("object", "indefinite"), ("creation", "yes")]
    comment := "Subextraction from an indefinite object under a verb of creation, the baseline of the verb-of-creation effect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3b : LinguisticExample :=
  { id := "shenhuang2026_ex3b"
    source := ⟨"shen-huang-2026", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "What did you compose that song about?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "movement"), ("object", "definite"), ("creation", "yes")]
    comment := "Davies and Dubinsky observe no contrast with (3a); Experiment 1 finds a smaller but nonzero definite island under verbs of creation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28_indefinite : LinguisticExample :=
  { id := "shenhuang2026_ex28_indefinite"
    source := ⟨"li-1992", "(54)"⟩
    reportedIn := some ⟨"shen-huang-2026", "(28)"⟩
    language := "mand1415"
    primaryText := "Wǒ yǐwéi tā ná-le shénme rén de xiàngpiàn"
    discourseSegments := []
    glossedTokens := [("Wǒ", "I"), ("yǐwéi", "mistakenly.believe"), ("tā", "he"), ("ná-le", "take.away-PERF"), ("shénme", "what"), ("rén", "man"), ("de", "DE"), ("xiàngpiàn", "picture")]
    translation := "I mistakenly thought he took away a picture of someone."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "binding"), ("object", "indefinite"), ("creation", "no")]
    comment := "The wh-indefinite reading, the wh-phrase bound by existential closure, adapted by the paper from Li's example without the demonstrative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28_definite : LinguisticExample :=
  { id := "shenhuang2026_ex28_definite"
    source := ⟨"li-1992", "(54)"⟩
    reportedIn := some ⟨"shen-huang-2026", "(28)"⟩
    language := "mand1415"
    primaryText := "Wǒ yǐwéi tā ná-le nà-zhāng shénme rén de xiàngpiàn"
    discourseSegments := []
    glossedTokens := [("Wǒ", "I"), ("yǐwéi", "mistakenly.believe"), ("tā", "he"), ("ná-le", "take.away-PERF"), ("nà-zhāng", "that-CL"), ("shénme", "what"), ("rén", "man"), ("de", "DE"), ("xiàngpiàn", "picture")]
    translation := "I mistakenly thought he took away that picture of someone."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("dependency", "binding"), ("object", "definite"), ("creation", "no")]
    comment := "The demonstrative blocks the wh-indefinite reading, the contrast Experiment 3 confirms."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex3a, ex3b, ex28_indefinite, ex28_definite]

end ShenHuang2026.Examples
