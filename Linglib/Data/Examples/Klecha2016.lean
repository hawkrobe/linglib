module

public import Linglib.Data.Examples.Schema

/-!
# `Klecha2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Klecha2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Klecha2016.Examples`.
-/

@[expose] public section

namespace Klecha2016.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "klecha2016_ex1"
    source := ⟨"klecha-2016", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Martina thought Carissa was pregnant."
    glossedTokens := []
    context := "Klecha's canonical SOT example. Past matrix (`thought`) + past embedded (`was pregnant`). Both RTs precede speech time; additionally, per the Upper Limit Constraint, the embedded RT (Carissa's pregnancy time) is no later than the matrix RT (Martina's thinking)."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (pregnancy at thinking)", .acceptable), ("shifted (pregnancy before thinking)", .acceptable), ("future-shifted (pregnancy after thinking)", .ungrammatical)]
    paperFeatures := [("verb", "think"), ("past", "available"), ("present", "available"), ("future", "unavailable")] }

def ex2a : LinguisticExample :=
  { id := "klecha2016_ex2a"
    source := ⟨"klecha-2016", "(2a) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He said Sorenstam had no business playing the PGA Tour, he hoped she missed the cut and he'd withdraw if paired with her, the AP reported."
    glossedTokens := []
    context := "Naturally-occurring example showing future-shifted reading of embedded past under `hope`. `She missed the cut` is in past tense morphology but the cut-missing is future-of-the-hoping (Singh hoped, at the time of hoping, that the cut-missing would occur AFTER the hoping)."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (missed-cut after hoping)", .acceptable)]
    paperFeatures := [("verb", "hope"), ("future", "available")] }

def ex2b : LinguisticExample :=
  { id := "klecha2016_ex2b"
    source := ⟨"klecha-2016", "(2b) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He was going to find that Guardian and do what he had to do. But his gut dropped at the thought of killing anyone in cold blood, even to save his brother. He hoped she tried to kill him first. Then he could behead her with a clean conscience."
    glossedTokens := []
    context := "Second naturally-occurring example of future-shifted past under `hope`. The kill-attempt is future of the hoping; the embedded past tense morphology doesn't force temporal precedence."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (try-to-kill after hoping)", .acceptable)]
    paperFeatures := [("verb", "hope"), ("future", "available")] }

def ex3a : LinguisticExample :=
  { id := "klecha2016_ex3a"
    source := ⟨"klecha-2016", "(3a) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There were times when I picked one receiver and prayed he got open."
    glossedTokens := []
    context := "Future-shifted reading under `pray`. `Got open` is past morphology but the getting-open is future-of-the-praying."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (got-open after praying)", .acceptable)]
    paperFeatures := [("verb", "pray"), ("future", "available")] }

def ex3b : LinguisticExample :=
  { id := "klecha2016_ex3b"
    source := ⟨"klecha-2016", "(3b) — COCA corpus"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Thirteen months and she would legally be able to walk out the door and live on her own. Her trust fund would be hers. She would no longer be dependent on her mother and Victor. Thirteen months. She prayed she survived that long."
    glossedTokens := []
    context := "Past morphology `survived` in the embedded clause of `pray`, but the surviving is future-of-the-praying (thirteen months out)."
    judgment := .acceptable
    alternatives := []
    readings := [("future-shifted (survival after praying)", .acceptable)]
    paperFeatures := [("verb", "pray"), ("future", "available")] }

def all : List LinguisticExample := [ex1, ex2a, ex2b, ex3a, ex3b]

end Klecha2016.Examples
