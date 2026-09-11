import Linglib.Data.Examples.Schema

/-!
# `Hyman2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Hyman2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hyman2006.Examples`.
-/

namespace Hyman2006.Examples

open Data.Examples

def makura : LinguisticExample :=
  { id := "hyman2006_makura"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "makura ga"
    discourseSegments := []
    glossedTokens := [("makura", "pillow"), ("ga", "NOM")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "mákùrà gà"), ("accent", "initial mora")]
    comment := "Analysed accentually, with a drop after the accented mora, and tonally, with a prelinked H."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kokoro : LinguisticExample :=
  { id := "hyman2006_kokoro"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kokoro ga"
    discourseSegments := []
    glossedTokens := [("kokoro", "heart"), ("ga", "NOM")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "kókórò gà"), ("accent", "second mora")]
    comment := "Analysed accentually, with a drop after the accented mora, and tonally, with a prelinked H."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def atama : LinguisticExample :=
  { id := "hyman2006_atama"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "atama ga"
    discourseSegments := []
    glossedTokens := [("atama", "head"), ("ga", "NOM")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "átámá gà"), ("accent", "final mora")]
    comment := "Analysed accentually, with a drop after the accented mora, and tonally, with a prelinked H."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sakana : LinguisticExample :=
  { id := "hyman2006_sakana"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "sakana ga"
    discourseSegments := []
    glossedTokens := [("sakana", "fish"), ("ga", "NOM")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "sákáná gá"), ("accent", "none"), ("note", "unaccented: no pitch drop")]
    comment := "Analysed accentually, with a drop after the accented mora, and tonally, with a prelinked H."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [makura, kokoro, atama, sakana]

end Hyman2006.Examples
