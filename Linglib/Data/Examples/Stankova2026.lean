import Linglib.Data.Examples.Schema

/-!
# `Stankova2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Stankova2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Stankova2026.Examples`.
-/

namespace Stankova2026.Examples

open Data.Examples

def ex6a : LinguisticExample :=
  { id := "stankova2026_ex6a"
    source := ⟨"stankova-2026", "ex. 6a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Petr si nekoupil žádný časopis?"
    discourseSegments := []
    glossedTokens := [("Petr", "Petr"), ("si", "REFL"), ("nekoupil", "NEG.bought"), ("žádný", "DET.NCI"), ("časopis", "magazine")]
    translation := "Petr didn't buy any magazine?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negation", "inner"), ("diagnostic", "nciLicensed")]
    comment := "Inner negation licenses the NCI žádný (nonV1 word order)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6b : LinguisticExample :=
  { id := "stankova2026_ex6b"
    source := ⟨"stankova-2026", "ex. 6b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nekoupil si Petr žádný časopis?"
    discourseSegments := []
    glossedTokens := [("Nekoupil", "NEG.bought"), ("si", "REFL"), ("Petr", "Petr"), ("žádný", "DET.NCI"), ("časopis", "magazine")]
    translation := "Didn't Petr buy a magazine?"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "nciLicensed")]
    comment := "High (V1) negation anti-licenses NCIs: only the outer reading is available and it cannot license žádný."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7a : LinguisticExample :=
  { id := "stankova2026_ex7a"
    source := ⟨"stankova-2026", "ex. 7a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Eva si neobjednala nějaký burger?"
    discourseSegments := []
    glossedTokens := [("Eva", "Eva"), ("si", "REFL"), ("neobjednala", "NEG.ordered"), ("nějaký", "DET.PPI"), ("burger", "burger")]
    translation := "Eva didn't order some burger?"
    context := "Eva and her colleagues from the office ordered take-out food for lunch. The delivery guy brings only pizzas. One of the colleagues asks."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negation", "medial"), ("diagnostic", "ppiOutscoping")]
    comment := "Medial negation: syntactically low (nonV1) but wide LF scope, letting the PPI nějaký be interpreted under it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7b : LinguisticExample :=
  { id := "stankova2026_ex7b"
    source := ⟨"stankova-2026", "ex. 7b"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neobjednala si Eva nějaký burger?"
    discourseSegments := []
    glossedTokens := [("Neobjednala", "NEG.ordered"), ("si", "REFL"), ("Eva", "Eva"), ("nějaký", "DET.PPI"), ("burger", "burger")]
    translation := "Didn't Eva order some burger?"
    context := "Eva and her colleagues from the office ordered take-out food for lunch. The delivery guy brings only pizzas. One of the colleagues asks."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "ppiOutscoping")]
    comment := "Outer (V1) negation allows the PPI nějaký."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11 : LinguisticExample :=
  { id := "stankova2026_ex11"
    source := ⟨"stankova-2026", "ex. 11"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Nepůjčila si tam Eva náhodou nějakou encyklopedii?"
    discourseSegments := []
    glossedTokens := [("Nepůjčila", "NEG.borrowed"), ("si", "REFL"), ("tam", "there"), ("Eva", "Eva"), ("náhodou", "NÁHODOU"), ("nějakou", "DET.PPI"), ("encyklopedii", "encyclopedia")]
    translation := "Didn't Eva borrow some encyclopedia, by any chance?"
    context := "Eva is doing research for a school presentation. Yesterday she went to the school library. The speaker knows all this from before and asks."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "nahodou")]
    comment := "The paper marks the NCI variant žádnou # in the same frame: náhodou depends on outer negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex15a : LinguisticExample :=
  { id := "stankova2026_ex15a"
    source := ⟨"stankova-2026", "ex. 15a"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Eva fakt neviděla žádný Tarantinův film?"
    discourseSegments := []
    glossedTokens := [("Eva", "Eva"), ("fakt", "FAKT"), ("neviděla", "NEG.saw"), ("žádný", "DET.NCI"), ("Tarantinův", "Tarantino's"), ("film", "film")]
    translation := "Eva really hasn't seen any film by Tarantino?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("negation", "inner"), ("diagnostic", "fakt")]
    comment := "fakt > ¬ > ∃_NCI: fakt over inner negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex15d : LinguisticExample :=
  { id := "stankova2026_ex15d"
    source := ⟨"stankova-2026", "ex. 15d"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "Neviděla Eva fakt nějaký Tarantinův film?"
    discourseSegments := []
    glossedTokens := [("Neviděla", "NEG.saw"), ("Eva", "Eva"), ("fakt", "FAKT"), ("nějaký", "DET.PPI"), ("Tarantinův", "Tarantino's"), ("film", "film")]
    translation := "Is it really not the case that Eva has seen a film by Tarantino?"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("negation", "outer"), ("diagnostic", "fakt")]
    comment := "fakt is repelled by outer negation on its canonical reading; grammatical only on the 'after all' reading (fn. 8)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex6a, ex6b, ex7a, ex7b, ex11, ex15a, ex15d]

end Stankova2026.Examples
