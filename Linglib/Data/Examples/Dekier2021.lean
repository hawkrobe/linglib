module

public import Linglib.Data.Examples.Schema

/-!
# `Dekier2021` — typed example data

Auto-generated from `Linglib/Data/Examples/Dekier2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dekier2021.Examples`.
-/

@[expose] public section

namespace Dekier2021.Examples

open Data.Examples

def english : LinguisticExample :=
  { id := "dekier2021_english"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "some- / some- / some-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "English"), ("nonSpecific", "some-"), ("specificUnknown", "some-"), ("specificKnown", "some-")] }

def polish : LinguisticExample :=
  { id := "dekier2021_polish"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "poli1260"
    primaryText := "-ś / -ś / -ś"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Polish"), ("nonSpecific", "-ś"), ("specificUnknown", "-ś"), ("specificKnown", "-ś")] }

def japanese : LinguisticExample :=
  { id := "dekier2021_japanese"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "-ka / -ka / -ka"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Japanese"), ("nonSpecific", "-ka"), ("specificUnknown", "-ka"), ("specificKnown", "-ka")] }

def korean : LinguisticExample :=
  { id := "dekier2021_korean"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "-nka / -nka / -nka"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Korean"), ("nonSpecific", "-nka"), ("specificUnknown", "-nka"), ("specificKnown", "-nka")] }

def lezgian : LinguisticExample :=
  { id := "dekier2021_lezgian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "lezg1247"
    primaryText := "-jat'ani / -jat'ani / -jat'ani"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Lezgian"), ("nonSpecific", "-jat'ani"), ("specificUnknown", "-jat'ani"), ("specificKnown", "-jat'ani")] }

def romanian : LinguisticExample :=
  { id := "dekier2021_romanian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "roma1327"
    primaryText := "-va / -va / -va"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Romanian"), ("nonSpecific", "-va"), ("specificUnknown", "-va"), ("specificKnown", "-va")] }

def bulgarian : LinguisticExample :=
  { id := "dekier2021_bulgarian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "nja- / nja- / nja-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Bulgarian"), ("nonSpecific", "nja-"), ("specificUnknown", "nja-"), ("specificKnown", "nja-")] }

def serbocroatian : LinguisticExample :=
  { id := "dekier2021_serbocroatian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "sout1528"
    primaryText := "ne- / ne- / ne-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Serbo-Croatian"), ("nonSpecific", "ne-"), ("specificUnknown", "ne-"), ("specificKnown", "ne-")] }

def czech : LinguisticExample :=
  { id := "dekier2021_czech"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "czec1258"
    primaryText := "ně- / ně- / ně-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Czech"), ("nonSpecific", "ně-"), ("specificUnknown", "ně-"), ("specificKnown", "ně-")] }

def slovak : LinguisticExample :=
  { id := "dekier2021_slovak"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "slov1269"
    primaryText := "nie- / nie- / nie-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Slovak"), ("nonSpecific", "nie-"), ("specificUnknown", "nie-"), ("specificKnown", "nie-")] }

def maltese : LinguisticExample :=
  { id := "dekier2021_maltese"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "malt1254"
    primaryText := "xi- / xi- / xi-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Maltese"), ("nonSpecific", "xi-"), ("specificUnknown", "xi-"), ("specificKnown", "xi-")] }

def hungarian : LinguisticExample :=
  { id := "dekier2021_hungarian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "hung1274"
    primaryText := "vala- / vala- / vala-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Hungarian"), ("nonSpecific", "vala-"), ("specificUnknown", "vala-"), ("specificKnown", "vala-")] }

def hebrew : LinguisticExample :=
  { id := "dekier2021_hebrew"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "-šehu / -šehu / -šehu"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Hebrew"), ("nonSpecific", "-šehu"), ("specificUnknown", "-šehu"), ("specificKnown", "-šehu")] }

def turkish : LinguisticExample :=
  { id := "dekier2021_turkish"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "bir- / bir- / bir-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Turkish"), ("nonSpecific", "bir-"), ("specificUnknown", "bir-"), ("specificKnown", "bir-")] }

def latvian : LinguisticExample :=
  { id := "dekier2021_latvian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "latv1249"
    primaryText := "kaut- / kaut- / kaut-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Latvian"), ("nonSpecific", "kaut-"), ("specificUnknown", "kaut-"), ("specificKnown", "kaut-")] }

def yakut : LinguisticExample :=
  { id := "dekier2021_yakut"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "yaku1245"
    primaryText := "-eme / -ere / -ere"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Yakut"), ("nonSpecific", "-eme"), ("specificUnknown", "-ere"), ("specificKnown", "-ere")] }

def georgian : LinguisticExample :=
  { id := "dekier2021_georgian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "-me / -ɣac / -ɣac"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Georgian"), ("nonSpecific", "-me"), ("specificUnknown", "-ɣac"), ("specificKnown", "-ɣac")] }

def ossetic : LinguisticExample :=
  { id := "dekier2021_ossetic"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "osse1243"
    primaryText := "is- / -dær / -dær"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Ossetic"), ("nonSpecific", "is-"), ("specificUnknown", "-dær"), ("specificKnown", "-dær")] }

def latin : LinguisticExample :=
  { id := "dekier2021_latin"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "ali- / ali- / -dam"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Latin"), ("nonSpecific", "ali-"), ("specificUnknown", "ali-"), ("specificKnown", "-dam")] }

def russian : LinguisticExample :=
  { id := "dekier2021_russian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "-nibud / -to / koe-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Russian"), ("nonSpecific", "-nibud"), ("specificUnknown", "-to"), ("specificKnown", "koe-")] }

def lithuanian : LinguisticExample :=
  { id := "dekier2021_lithuanian"
    source := ⟨"dekier-2021", "Table 7"⟩
    reportedIn := none
    language := "lith1251"
    primaryText := "-nors / kaž- / kai-"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Lithuanian"), ("nonSpecific", "-nors"), ("specificUnknown", "kaž-"), ("specificKnown", "kai-")] }

def kannada : LinguisticExample :=
  { id := "dekier2021_kannada"
    source := ⟨"dekier-2021", "Table 6"⟩
    reportedIn := none
    language := "nucl1305"
    primaryText := "-aadaruu / -oo / –"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Kannada"), ("nonSpecific", "-aadaruu"), ("specificUnknown", "-oo")] }

def quechua : LinguisticExample :=
  { id := "dekier2021_quechua"
    source := ⟨"dekier-2021", "Table 6"⟩
    reportedIn := none
    language := "quec1387"
    primaryText := "-pis/-pas / -chi/-cha / –"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Quechua"), ("nonSpecific", "-pis/-pas"), ("specificUnknown", "-chi/-cha")] }

def mandarinchinese : LinguisticExample :=
  { id := "dekier2021_mandarinchinese"
    source := ⟨"dekier-2021", "Table 6"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "wh-pronoun / – / –"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Mandarin Chinese"), ("nonSpecific", "wh-pronoun")] }

def irish : LinguisticExample :=
  { id := "dekier2021_irish"
    source := ⟨"dekier-2021", "Table 6"⟩
    reportedIn := none
    language := "iris1253"
    primaryText := "– / – / –"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Irish")] }

def swahili : LinguisticExample :=
  { id := "dekier2021_swahili"
    source := ⟨"dekier-2021", "Table 6"⟩
    reportedIn := none
    language := "swah1253"
    primaryText := "– / – / –"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Swahili")] }

def filipino : LinguisticExample :=
  { id := "dekier2021_filipino"
    source := ⟨"dekier-2021", "Table 6"⟩
    reportedIn := none
    language := "taga1270"
    primaryText := "– / – / –"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("language", "Filipino")] }

def all : List LinguisticExample := [english, polish, japanese, korean, lezgian, romanian, bulgarian, serbocroatian, czech, slovak, maltese, hungarian, hebrew, turkish, latvian, yakut, georgian, ossetic, latin, russian, lithuanian, kannada, quechua, mandarinchinese, irish, swahili, filipino]

end Dekier2021.Examples
