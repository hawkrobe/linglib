import Linglib.Data.Examples.Schema

/-!
# `Asudeh2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Asudeh2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Asudeh2022.Examples`.
-/

namespace Asudeh2022.Examples

open Data.Examples

def ex_6 : LinguisticExample :=
  { id := "asudeh2022_6"
    source := ⟨"asudeh-2022", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex likes Blake."
    discourseSegments := []
    glossedTokens := [("Alex", "Alex"), ("likes", "like.PRS.3SG"), ("Blake", "Blake")]
    translation := "Alex likes Blake."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("premises", "likes, alex, blake")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "asudeh2022_14"
    source := ⟨"asudeh-2022", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody loves somebody."
    discourseSegments := []
    glossedTokens := [("Everybody", "everybody"), ("loves", "love.PRS.3SG"), ("somebody", "somebody")]
    translation := "Everybody loves somebody."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("surface", .acceptable), ("inverse", .acceptable)]
    paperFeatures := [("premises", "love, every, some")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def fig2_finnish : LinguisticExample :=
  { id := "asudeh2022_fig2_finnish"
    source := ⟨"asudeh-2022", "Figure 2, Finnish"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Join vettä."
    discourseSegments := []
    glossedTokens := [("Join", "drink.PST.1SG"), ("vettä", "water.PART")]
    translation := "I drank water."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("premises", "speaker, drink, water")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def fig2_english : LinguisticExample :=
  { id := "asudeh2022_fig2_english"
    source := ⟨"asudeh-2022", "Figure 2, English"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I drank water."
    discourseSegments := []
    glossedTokens := [("I", "1SG"), ("drank", "drink.PST"), ("water", "water")]
    translation := "I drank water."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("premises", "speaker, drink, water")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_6, ex_14, fig2_finnish, fig2_english]

end Asudeh2022.Examples
