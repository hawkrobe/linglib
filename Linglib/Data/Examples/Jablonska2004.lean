import Linglib.Data.Examples.Schema

/-!
# `Jablonska2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Jablonska2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jablonska2004.Examples`.
-/

namespace Jablonska2004.Examples

open Data.Examples

def fn21 : LinguisticExample :=
  { id := "jablonska2004_fn21"
    source := ⟨"jablonska-2004", "fn. 21"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "po-siedzieć"
    discourseSegments := []
    glossedTokens := [("po-siedzieć", "PO-sit")]
    translation := "sit for a while"
    context := "Delimitative po- attaching to a stative verb, contra Młynarczyk's claim that it cannot; her fn. 21 also gives po-wisieć 'hang for a while' and po-cierpieć 'suffer for a while'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Delimitative reading of po- on a stative (high-verbalizer) stem."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_54a : LinguisticExample :=
  { id := "jablonska2004_54a"
    source := ⟨"jablonska-2004", "(54a)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "po-kochać"
    discourseSegments := []
    glossedTokens := [("po-kochać", "PO-love")]
    translation := "start loving"
    context := "po- fixing the left boundary of a state: an inceptive reading of the same prefix that yields delimitative readings elsewhere — her verbalizer-sensitivity thesis."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Her (54a); (54b) po-lubić 'start liking' is parallel."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_53 : LinguisticExample :=
  { id := "jablonska2004_53"
    source := ⟨"jablonska-2004", "(53)"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "za-jaś-ni-e-ć"
    discourseSegments := []
    glossedTokens := [("za-jaś-ni-e-ć", "incp-bright-adj-V-inf")]
    translation := "to start being bright"
    context := "Inceptive za- on a low -ej- verbalizer stem: the reading is inchoation of a state, not of a transitional dynamic eventuality."
    judgment := .acceptable
    alternatives := []
    readings := [("inchoation of state ('start being bright')", .acceptable), ("inchoation of becoming ('start becoming bright')", .unacceptable)]
    paperFeatures := []
    comment := "Her (53): the available reading tracks the embedded verbalizer, her central verbalizer-sensitivity claim."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [fn21, ex_54a, ex_53]

end Jablonska2004.Examples
