import Linglib.Data.Examples.Schema

/-!
# `RonderosEtAl2024` — typed example data

Auto-generated from `Linglib/Data/Examples/RonderosEtAl2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RonderosEtAl2024.Examples`.
-/

namespace RonderosEtAl2024.Examples

open Data.Examples

def ronderos2024_1a : LinguisticExample :=
  { id := "ronderos2024_1a"
    source := ⟨"ronderos-etal-2024", "Figure 1 (1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the short pencil"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Display: the target (short pencil), a long pencil, short scissors, and a distractor; three-second preview, then the description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjType", "scalar"), ("condition", "contrast"), ("contrastEffect", "present")]
    comment := "Contrast condition: a same-kind object of the opposite size is present. Results: a significant cluster for scalar adjectives from 260 to 500 ms after noun onset and a significant effect of condition on the target-advantage score."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ronderos2024_1b : LinguisticExample :=
  { id := "ronderos2024_1b"
    source := ⟨"ronderos-etal-2024", "Figure 1 (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the short pencil"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Display: the target (short pencil), short scissors, and two distractors of other kinds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjType", "scalar"), ("condition", "noContrast")]
    comment := "No-contrast condition: the same-kind object is replaced by a distractor. Results: looks to target and competitor over the noun window are lower than for colour and material adjectives, the intercept of the total-looks model."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ronderos2024_2a : LinguisticExample :=
  { id := "ronderos2024_2a"
    source := ⟨"ronderos-etal-2024", "Figure 1 (2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the black lamp"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Display: the target (black lamp), a yellow lamp, a black object of another kind, and a distractor; three-second preview, then the description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjType", "color"), ("condition", "contrast"), ("contrastEffect", "present")]
    comment := "Contrast condition: a same-kind object of another colour is present. Results: a significant cluster for colour adjectives from 240 to 600 ms after noun onset and a significant effect of condition on the target-advantage score."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ronderos2024_2b : LinguisticExample :=
  { id := "ronderos2024_2b"
    source := ⟨"ronderos-etal-2024", "Figure 1 (2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the black lamp"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Display: the target (black lamp), a black object of another kind, and two distractors of other kinds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjType", "color"), ("condition", "noContrast"), ("baselineVsScalar", "higher")]
    comment := "No-contrast condition. Results: significantly more looks to target and competitor than for scalar adjectives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ronderos2024_3a : LinguisticExample :=
  { id := "ronderos2024_3a"
    source := ⟨"ronderos-etal-2024", "Figure 1 (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the leather shoes"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Display: the target (leather shoes), canvas shoes, a leather object of another kind, and a distractor; three-second preview, then the description."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjType", "material"), ("condition", "contrast"), ("contrastEffect", "absent")]
    comment := "Contrast condition: a same-kind object of another material is present. Results: no cluster for material adjectives and no significant effect of condition on the target-advantage score."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ronderos2024_3b : LinguisticExample :=
  { id := "ronderos2024_3b"
    source := ⟨"ronderos-etal-2024", "Figure 1 (3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "the leather shoes"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Display: the target (leather shoes), a leather object of another kind, and two distractors of other kinds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("adjType", "material"), ("condition", "noContrast"), ("baselineVsScalar", "higher")]
    comment := "No-contrast condition. Results: significantly more looks to target and competitor than for scalar adjectives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ronderos2024_1a, ronderos2024_1b, ronderos2024_2a, ronderos2024_2b, ronderos2024_3a, ronderos2024_3b]

end RonderosEtAl2024.Examples
