import Linglib.Data.Examples.Schema

/-!
# `AckermanMalouf2013` — typed example data

Auto-generated from `Linglib/Data/Examples/AckermanMalouf2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AckermanMalouf2013.Examples`.
-/

namespace AckermanMalouf2013.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "ackermanmalouf2013_1"
    source := ⟨"ackerman-malouf-2013", "(1)"⟩
    reportedIn := none
    language := "kala1399"
    primaryText := "ajunngitsuliurviginnittuartuunngilaq"
    discourseSegments := []
    glossedTokens := [("aju-", "be.good"), ("nngit-", "NEG"), ("su-", "PART"), ("liur-", "make"), ("vigi-", "have.as.place.of"), ("nnit-", "ANTIP"), ("tuar-", "all.the.time"), ("tu-", "PART"), ("u-", "be"), ("nngil-", "NEG"), ("aq", "3SG.IND")]
    translation := "He is not (much of) a benefactor."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "polysynthesis"), ("complexity", "enumerative")]
    comment := "West Greenlandic, cited from Fortescue as a word packaging what English expresses phrasally."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1]

end AckermanMalouf2013.Examples
