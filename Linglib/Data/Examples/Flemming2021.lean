import Linglib.Data.Examples.Schema

/-!
# `Flemming2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Flemming2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Flemming2021.Examples`.
-/

namespace Flemming2021.Examples

open Data.Examples

def ctx1 : LinguisticExample :=
  { id := "flemming2021_ctx1"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn bɔt(ə) ʃinˈwaz"
    discourseSegments := []
    glossedTokens := []
    translation := "a Chinese boot"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "C"), ("following", "disyllable"), ("pSchwa", "9")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ctx2 : LinguisticExample :=
  { id := "flemming2021_ctx2"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn bɔt(ə) ˈʒon"
    discourseSegments := []
    glossedTokens := []
    translation := "a yellow boot"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "C"), ("following", "monosyllable"), ("pSchwa", "12")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ctx3 : LinguisticExample :=
  { id := "flemming2021_ctx3"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn vɛst(ə) ʃinˈwaz"
    discourseSegments := []
    glossedTokens := []
    translation := "a Chinese jacket"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "CC"), ("following", "disyllable"), ("pSchwa", "68")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ctx4 : LinguisticExample :=
  { id := "flemming2021_ctx4"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "yn vɛst(ə) ˈʒon"
    discourseSegments := []
    glossedTokens := []
    translation := "a yellow jacket"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "zero"), ("onset", "CC"), ("following", "monosyllable"), ("pSchwa", "83")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ctx5 : LinguisticExample :=
  { id := "flemming2021_ctx5"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "eva t(ə) ʃɔˈkɛ"
    discourseSegments := []
    glossedTokens := []
    translation := "Eva shocked you"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "C"), ("following", "disyllable"), ("pSchwa", "56")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ctx6 : LinguisticExample :=
  { id := "flemming2021_ctx6"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "eva t(ə) ˈʃɔk"
    discourseSegments := []
    glossedTokens := []
    translation := "Eva shocks you"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "C"), ("following", "monosyllable"), ("pSchwa", "65")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ctx7 : LinguisticExample :=
  { id := "flemming2021_ctx7"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "mɔʁiz t(ə) siˈtɛ"
    discourseSegments := []
    glossedTokens := []
    translation := "Maurice cited you"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "CC"), ("following", "disyllable"), ("pSchwa", "91")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ctx8 : LinguisticExample :=
  { id := "flemming2021_ctx8"
    source := ⟨"smith-pater-2020", "experiment"⟩
    reportedIn := some ⟨"flemming-2021", "(19), Table 2"⟩
    language := "stan1290"
    primaryText := "mɔʁiz t(ə) ˈsit"
    discourseSegments := []
    glossedTokens := []
    translation := "Maurice cites you"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying", "schwa"), ("onset", "CC"), ("following", "monosyllable"), ("pSchwa", "94")]
    comment := "Observed probability of pronouncing the parenthesized schwa, in hundredths."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ctx1, ctx2, ctx3, ctx4, ctx5, ctx6, ctx7, ctx8]

end Flemming2021.Examples
