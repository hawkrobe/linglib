module

public import Linglib.Data.Examples.Schema

/-!
# `Svenonius2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Svenonius2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Svenonius2004.Examples`.
-/

@[expose] public section

namespace Svenonius2004.Examples

open Data.Examples

def ex_1a : Datum :=
  { id := "svenonius2004_1a"
    source := ⟨"svenonius-2004", "(1a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Helder za-brosil mjač v vorota angličan."
    glossedTokens := [("Helder", "Helder"), ("za-brosil", "into-threw"), ("mjač", "ball"), ("v", "in"), ("vorota", "goal"), ("angličan", "English")]
    context := "Spatial-resultative za-: the goal is the endpoint of the ball's path."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_1b : Datum :=
  { id := "svenonius2004_1b"
    source := ⟨"svenonius-2004", "(1b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "David sovsem za-brosil futbol."
    glossedTokens := [("David", "David"), ("sovsem", "completely"), ("za-brosil", "into-threw"), ("futbol", "soccer")]
    context := "Idiomatic use of the same lexical za- as in the spatial (1a): idiosyncratic meaning is available to lexical prefixes."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_1c : Datum :=
  { id := "svenonius2004_1c"
    source := ⟨"svenonius-2004", "(1c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Ricardo nervno za-brosal mjač."
    glossedTokens := [("Ricardo", "Ricardo"), ("nervno", "nervously"), ("za-brosal", "incp-threw"), ("mjač", "ball")]
    context := "Inceptive (superlexical) za- on the imperfective stem brosat', versus the lexical za- of (1a)/(1b) on perfective brosit'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_4a : Datum :=
  { id := "svenonius2004_4a"
    source := ⟨"svenonius-2004", "(4a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "po-vy-brasyvatj"
    glossedTokens := [("po-vy-brasyvatj", "dstr-out-throw")]
    context := "Superlexical distributive po- stacked outside lexical vy- on the secondary-imperfective stem brasyvatj."
    judgment := .acceptable
    alternatives := [("vy-po-brasyvatj", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_4c : Datum :=
  { id := "svenonius2004_4c"
    source := ⟨"svenonius-2004", "(4c)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "po-w-chodzili"
    glossedTokens := [("po-w-chodzili", "dstr-in-walk")]
    context := "Polish counterpart of (4a): superlexical distributive po- outside lexical w-."
    judgment := .acceptable
    alternatives := [("w-po-chodzili", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_3a : Datum :=
  { id := "svenonius2004_3a"
    source := ⟨"istratkova-2004", "§4 (kaža table)"⟩
    reportedIn := some ⟨"svenonius-2004", "(3a)"⟩
    language := "bulg1262"
    primaryText := "po-na-razkaža"
    glossedTokens := [("po-na-razkaža", "dlmt-cmlt-narrate")]
    context := "Two superlexical prefixes stacked on the quantized perfective stem razkaža 'narrate'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_3e : Datum :=
  { id := "svenonius2004_3e"
    source := ⟨"istratkova-2004", "§4 (kaža table)"⟩
    reportedIn := some ⟨"svenonius-2004", "(3e)"⟩
    language := "bulg1262"
    primaryText := "iz-po-na-pre-razkaža"
    glossedTokens := [("iz-po-na-pre-razkaža", "cmpl-dstr-cmlt-rpet-narrate")]
    context := "Four superlexical prefixes stacked on the quantized perfective stem razkaža 'narrate'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [] }

def ex_58za : Datum :=
  { id := "svenonius2004_58za"
    source := ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "za-kuritj"
    glossedTokens := [("za-kuritj", "incp-smoke")]
    context := "Inceptive za- almost never forms secondary imperfectives in Russian."
    judgment := .acceptable
    alternatives := [("za-kurivatj", .ungrammatical)]
    readings := []
    paperFeatures := [] }

def ex_58po : Datum :=
  { id := "svenonius2004_58po"
    source := ⟨"svenonius-2004", "§4.1 (58) discussion"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "po-čitatj"
    glossedTokens := [("po-čitatj", "atten-read")]
    context := "Attenuative po- generally resists secondary imperfectivization but sometimes allows it."
    judgment := .acceptable
    alternatives := [("po-čityvatj", .acceptable)]
    readings := []
    paperFeatures := [] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_4a, ex_4c, ex_3a, ex_3e, ex_58za, ex_58po]

end Svenonius2004.Examples
