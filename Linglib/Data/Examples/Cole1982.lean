module

public import Linglib.Data.Examples.Schema

/-!
# `Cole1982` — typed example data

Auto-generated from `Linglib/Data/Examples/Cole1982.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cole1982.Examples`.
-/

@[expose] public section

namespace Cole1982.Examples

def ex_89b : Datum :=
  { id := "cole1982_89b"
    source := ⟨"cole-1982", "p. 30, (89b)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "ari, jatun wasi-ta chari-ni-mi"
    glossedTokens := [("ari", "yes"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-ni-mi", "have-1-validator")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_90 : Datum :=
  { id := "cole1982_90"
    source := ⟨"cole-1982", "p. 30, (90)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "mana jatun wasi-ta chari-ni-chu"
    glossedTokens := [("mana", "not"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-ni-chu", "have-1-neg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("affirmative", "cole1982_89b")] }

def ex_332 : Datum :=
  { id := "cole1982_332"
    source := ⟨"cole-1982", "p. 83, (332)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "ñuka wawki mana jatun wasi-ta chari-n-chu"
    glossedTokens := [("ñuka", "my"), ("wawki", "brother"), ("mana", "not"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-n-chu", "have-3-neg")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_333 : Datum :=
  { id := "cole1982_333"
    source := ⟨"cole-1982", "p. 83, (333)"⟩
    reportedIn := none
    language := "imba1240"
    primaryText := "kan-paj wawki jatun wasi-ta chari-n-chu"
    glossedTokens := [("kan-paj", "you-possessive"), ("wawki", "brother"), ("jatun", "big"), ("wasi-ta", "house-acc"), ("chari-n-chu", "have-3-inter")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_89b, ex_90, ex_332, ex_333]

end Cole1982.Examples
