module

public import Linglib.Data.Examples.Schema

/-!
# `Hyman2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Hyman2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hyman2006.Examples`.
-/

@[expose] public section

namespace Hyman2006.Examples

open Data.Examples

def makura : LinguisticExample :=
  { id := "hyman2006_makura"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "makura ga"
    glossedTokens := [("makura", "pillow"), ("ga", "NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "mákùrà gà"), ("accent", "initial mora")] }

def kokoro : LinguisticExample :=
  { id := "hyman2006_kokoro"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "kokoro ga"
    glossedTokens := [("kokoro", "heart"), ("ga", "NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "kókórò gà"), ("accent", "second mora")] }

def atama : LinguisticExample :=
  { id := "hyman2006_atama"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "atama ga"
    glossedTokens := [("atama", "head"), ("ga", "NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "átámá gà"), ("accent", "final mora")] }

def sakana : LinguisticExample :=
  { id := "hyman2006_sakana"
    source := ⟨"hyman-2006", "(4)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "sakana ga"
    glossedTokens := [("sakana", "fish"), ("ga", "NOM")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("output", "sákáná gá"), ("accent", "none"), ("note", "unaccented: no pitch drop")] }

def all : List LinguisticExample := [makura, kokoro, atama, sakana]

end Hyman2006.Examples
