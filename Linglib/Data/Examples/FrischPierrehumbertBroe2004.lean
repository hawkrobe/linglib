module

public import Linglib.Data.Examples.Schema

/-!
# `FrischPierrehumbertBroe2004` — typed example data

Auto-generated from `Linglib/Data/Examples/FrischPierrehumbertBroe2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FrischPierrehumbertBroe2004.Examples`.
-/

@[expose] public section

namespace FrischPierrehumbertBroe2004.Examples

def fpb2004_dtC : Datum :=
  { id := "fpb2004_dtC"
    source := ⟨"frisch-pierrehumbert-broe-2004", "O/E examples"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "/d t C/"
    glossedTokens := []
    context := "Triconsonantal verbal roots of Standard Arabic with the two consonants in first and second position, counted in the 2,674-root lexicon of Cowan (1979); the expected count is the number of such roots if consonants combined at random."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("c1", "d"), ("c2", "t"), ("observed", "0"), ("expectedTenths", "23"), ("oeHundredths", "0"), ("similarityHundredths", "42")] }

def fpb2004_dsC : Datum :=
  { id := "fpb2004_dsC"
    source := ⟨"frisch-pierrehumbert-broe-2004", "O/E examples"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "/d s C/"
    glossedTokens := []
    context := "Triconsonantal verbal roots of Standard Arabic with the two consonants in first and second position, counted in the 2,674-root lexicon of Cowan (1979); the expected count is the number of such roots if consonants combined at random."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("c1", "d"), ("c2", "s"), ("observed", "2"), ("expectedTenths", "29"), ("oeHundredths", "69"), ("similarityHundredths", "17")] }

def fpb2004_dgC : Datum :=
  { id := "fpb2004_dgC"
    source := ⟨"frisch-pierrehumbert-broe-2004", "O/E examples"⟩
    reportedIn := none
    language := "stan1318"
    primaryText := "/d g C/"
    glossedTokens := []
    context := "Triconsonantal verbal roots of Standard Arabic with the two consonants in first and second position, counted in the 2,674-root lexicon of Cowan (1979); the expected count is the number of such roots if consonants combined at random."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("c1", "d"), ("c2", "g"), ("observed", "4"), ("expectedTenths", "33"), ("oeHundredths", "121"), ("similarityHundredths", "0")] }

def all : List Datum := [fpb2004_dtC, fpb2004_dsC, fpb2004_dgC]

end FrischPierrehumbertBroe2004.Examples
