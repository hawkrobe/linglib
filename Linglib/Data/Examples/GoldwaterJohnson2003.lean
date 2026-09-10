import Linglib.Data.Examples.Schema

/-!
# `GoldwaterJohnson2003` — typed example data

Auto-generated from `Linglib/Data/Examples/GoldwaterJohnson2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GoldwaterJohnson2003.Examples`.
-/

namespace GoldwaterJohnson2003.Examples

open Data.Examples

def gj2003_kala : LinguisticExample :=
  { id := "gj2003_kala"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "ká.lo.jen"
    discourseSegments := []
    glossedTokens := []
    translation := "of the fish"
    context := ""
    judgment := .acceptable
    alternatives := [("*ká.loi.den", .ungrammatical)]
    readings := []
    paperFeatures := [("stem", "kala"), ("loser", "ká.loi.den"), ("winnerViolations", "11000001011"), ("loserViolations", "12000001101")]
    comment := "Stem class of kala 'fish': only the weak ending; difference vector 0 1 0 0 0 0 0 0 1 -1 0 (Table 3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gj2003_naapuri : LinguisticExample :=
  { id := "gj2003_naapuri"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "náa.pu.ri.en"
    discourseSegments := []
    glossedTokens := []
    translation := "of the neighbors"
    context := ""
    judgment := .acceptable
    alternatives := [("náa.pu.rèi.den", .acceptable)]
    readings := []
    paperFeatures := [("stem", "naapuri"), ("loser", "náa.pu.rèi.den"), ("winnerViolations", "01000100012"), ("loserViolations", "01100000100")]
    comment := "Stem class of naapuri 'neighbor': both endings occur; difference vector 0 0 1 0 0 -1 0 0 1 -1 -2."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gj2003_ministeri : LinguisticExample :=
  { id := "gj2003_ministeri"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "mí.nis.te.ri.en"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stem", "ministeri"), ("loser", "mí.nis.te.rèi.den"), ("winnerViolations", "12000100013"), ("loserViolations", "12100000101")]
    comment := "Stem class of ministeri: a different violation pattern from naapuri but the same difference vector, so the two classes are one for a learner that sees only differences (Table 3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gj2003_maailma : LinguisticExample :=
  { id := "gj2003_maailma"
    source := ⟨"goldwater-johnson-2003", "Table 2"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "máa.il.mo.jen"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("stem", "maailma"), ("loser", "máa.il.mòi.den"), ("winnerViolations", "02000001102"), ("loserViolations", "02001000300")]
    comment := "Stem class of maailma: difference vector 0 0 0 0 1 0 0 -1 2 0 -2."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [gj2003_kala, gj2003_naapuri, gj2003_ministeri, gj2003_maailma]

end GoldwaterJohnson2003.Examples
