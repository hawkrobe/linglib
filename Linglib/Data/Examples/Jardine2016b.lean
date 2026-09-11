import Linglib.Data.Examples.Schema

/-!
# `Jardine2016b` — typed example data

Auto-generated from `Linglib/Data/Examples/Jardine2016b.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Jardine2016b.Examples`.
-/

namespace Jardine2016b.Examples

open Data.Examples

def ex_7_5_pa : LinguisticExample :=
  { id := "jardine2016b_7_5_pa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "pa → pa"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "pa"), ("output", "pa"), ("in_rvoice", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_5_aaa : LinguisticExample :=
  { id := "jardine2016b_7_5_aaa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "aaa → aaa"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "aaa"), ("output", "aaa"), ("in_rvoice", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_5_apa : LinguisticExample :=
  { id := "jardine2016b_7_5_apa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "apa → aba"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "apa"), ("output", "aba"), ("in_rvoice", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_5_aba : LinguisticExample :=
  { id := "jardine2016b_7_5_aba"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "aba → aba"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "aba"), ("output", "aba"), ("in_rvoice", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_5_appa : LinguisticExample :=
  { id := "jardine2016b_7_5_appa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "appa → appa"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "appa"), ("output", "appa"), ("in_rvoice", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_5_aapaaapa : LinguisticExample :=
  { id := "jardine2016b_7_5_aapaaapa"
    source := ⟨"jardine-2016b", "(7.5)"⟩
    reportedIn := none
    language := ""
    primaryText := "aapaaapa → aabaaaba"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "aapaaapa"), ("output", "aabaaaba"), ("in_rvoice", "yes")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_17_pa_ba : LinguisticExample :=
  { id := "jardine2016b_7_17_pa_ba"
    source := ⟨"jardine-2016b", "(7.17)"⟩
    reportedIn := none
    language := ""
    primaryText := "pa → ba"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "pa"), ("output", "ba"), ("in_rvoice", "no")]
    comment := "A non-intervocalic p voiced, (7.20a): excluded by φ⋊pb."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_17_apa_apa : LinguisticExample :=
  { id := "jardine2016b_7_17_apa_apa"
    source := ⟨"jardine-2016b", "(7.17)"⟩
    reportedIn := none
    language := ""
    primaryText := "apa → apa"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "apa"), ("output", "apa"), ("in_rvoice", "no")]
    comment := "An intervocalic p unvoiced, (7.18b): excluded by φapa."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7_17_appa_abpa : LinguisticExample :=
  { id := "jardine2016b_7_17_appa_abpa"
    source := ⟨"jardine-2016b", "(7.17)"⟩
    reportedIn := none
    language := ""
    primaryText := "appa → abpa"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "7.2"), ("input", "appa"), ("output", "abpa"), ("in_rvoice", "no")]
    comment := "A p voiced before a p, (7.20b): excluded by φpbp."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_7_5_pa, ex_7_5_aaa, ex_7_5_apa, ex_7_5_aba, ex_7_5_appa, ex_7_5_aapaaapa, ex_7_17_pa_ba, ex_7_17_apa_apa, ex_7_17_appa_abpa]

end Jardine2016b.Examples
