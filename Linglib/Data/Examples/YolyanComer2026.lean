module

public import Linglib.Data.Examples.Schema

/-!
# `YolyanComer2026` — typed example data

Auto-generated from `Linglib/Data/Examples/YolyanComer2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace YolyanComer2026.Examples`.
-/

@[expose] public section

namespace YolyanComer2026.Examples

open Data.Examples

def ex_5a : LinguisticExample :=
  { id := "yolyancomer2026_5a"
    source := ⟨"yolyan-comer-2026", "(5a)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "esoha-ya"
    discourseSegments := []
    glossedTokens := []
    translation := "He pours"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nasal_spreading", "none")]
    comment := "No nasal, so no spreading. The paper gives translations only, no morpheme glosses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5b : LinguisticExample :=
  { id := "yolyancomer2026_5b"
    source := ⟨"yolyan-comer-2026", "(5b)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "nãõ-ỹã"
    discourseSegments := []
    glossedTokens := []
    translation := "He saw"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nasal_spreading", "to word end")]
    comment := "Nasality spreads rightward from the initial nasal through every following segment. The paper gives translations only, no morpheme glosses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5c : LinguisticExample :=
  { id := "yolyancomer2026_5c"
    source := ⟨"yolyan-comer-2026", "(5c)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "nãõ-te"
    discourseSegments := []
    glossedTokens := []
    translation := "He will come"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nasal_spreading", "blocked by voiceless stop"), ("underlying_form", "/naote/")]
    comment := "The Fig. 4 and Fig. 5 word: spreading from the initial n reaches a and o and is suspended by t. The paper gives translations only, no morpheme glosses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5d : LinguisticExample :=
  { id := "yolyancomer2026_5d"
    source := ⟨"yolyan-comer-2026", "(5d)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "honĩw̃ãku-hae"
    discourseSegments := []
    glossedTokens := []
    translation := "It is a turtle"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nasal_spreading", "blocked by voiceless stop")]
    comment := "Spreading from the n runs through ĩw̃ã and is suspended by k. The paper gives translations only, no morpheme glosses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5e : LinguisticExample :=
  { id := "yolyancomer2026_5e"
    source := ⟨"yolyan-comer-2026", "(5e)"⟩
    reportedIn := some ⟨"osborn-1966", ""⟩
    language := "wara1303"
    primaryText := "panãpanã-h̃ãẽ"
    discourseSegments := []
    glossedTokens := []
    translation := "It is a porpoise"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nasal_spreading", "blocked by voiceless stop")]
    comment := "Each n spreads rightward until the next p; the final h and vowels are nasalized. The paper gives translations only, no morpheme glosses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_5a, ex_5b, ex_5c, ex_5d, ex_5e]

end YolyanComer2026.Examples
