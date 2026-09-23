module

public import Linglib.Data.Examples.Schema

/-!
# `Woolford1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Woolford1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Woolford1997.Examples`.
-/

@[expose] public section

namespace Woolford1997.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "woolford1997_1"
    source := ⟨"woolford-1997", "(3)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "'ipí-Ø hi-kú-ye."
    discourseSegments := []
    glossedTokens := [("'ipí-Ø", "he-NOM"), ("hi-kú-ye", "3-go-ASP")]
    translation := "He went."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "nominative"), ("clause", "intransitive")]
    comment := "Rude 1982, (19)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "woolford1997_2"
    source := ⟨"woolford-1997", "(4)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Háama-Ø hi-'wí-ye wewúkiye-Ø."
    discourseSegments := []
    glossedTokens := [("Háama-Ø", "man-NOM"), ("hi-'wí-ye", "3-shoot-ASP"), ("wewúkiye-Ø", "elk-ACC")]
    translation := "The man shot an elk."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "nominative-accusative"), ("clause", "transitive")]
    comment := "Rude 1988, (31). Neither case is overt; only the nominative triggers agreement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "woolford1997_3"
    source := ⟨"woolford-1997", "(5)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Háama-nm pée-'wi-ye wewúkiye-ne."
    discourseSegments := []
    glossedTokens := [("Háama-nm", "man-ERG"), ("pée-'wi-ye", "3/3-shoot-ASP"), ("wewúkiye-ne", "elk-OBJ")]
    translation := "The man shot an elk."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-objective"), ("clause", "transitive")]
    comment := "Rude 1988, (30). The ergative subject triggers subject agreement and the objective object triggers object agreement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "woolford1997_4"
    source := ⟨"woolford-1997", "(6)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "ʔáayat-Ø hi-ʔni-ye tíim'es-Ø háama-Ø."
    discourseSegments := []
    glossedTokens := [("ʔáayat-Ø", "woman-NOM"), ("hi-ʔni-ye", "3-give-PAST"), ("tíim'es-Ø", "book-ACC"), ("háama-Ø", "husband-ACC")]
    translation := "The woman gave her husband a book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "nominative-accusative-accusative"), ("clause", "ditransitive")]
    comment := "Rude, personal communication. Neither object triggers agreement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "woolford1997_5"
    source := ⟨"woolford-1997", "(7)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "ʔáayato-m pée-ʔni-ye tíim'es-Ø háama-na."
    discourseSegments := []
    glossedTokens := [("ʔáayato-m", "woman-ERG"), ("pée-ʔni-ye", "3/3-give-PAST"), ("tíim'es-Ø", "book-ACC"), ("háama-na", "man-OBJ")]
    translation := "The woman gave the man a book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-objective-accusative"), ("clause", "ditransitive")]
    comment := "Rude, personal communication. The goal is objective and triggers object agreement; the theme is accusative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "woolford1997_6"
    source := ⟨"woolford-1997", "(8)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "ʔáayato-m pée-ʔni-ye haswaláya-na háama-na."
    discourseSegments := []
    glossedTokens := [("ʔáayato-m", "woman-ERG"), ("pée-ʔni-ye", "3/3-give-PAST"), ("haswaláya-na", "slave-OBJ"), ("háama-na", "man-DAT")]
    translation := "The woman gave the slave to the man."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-dative-objective"), ("clause", "ditransitive")]
    comment := "Rude, personal communication. With a dative goal the theme gets objective case."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "woolford1997_7"
    source := ⟨"woolford-1997", "(57)"⟩
    reportedIn := none
    language := "kalk1246"
    primaryText := "Maṛapai-tu anʸa-ŋi (ŋai-Ø) piipa-Ø."
    discourseSegments := []
    glossedTokens := [("Maṛapai-tu", "woman-ERG"), ("anʸa-ŋi", "gave-1SG.OBJ"), ("(ŋai-Ø)", "(me-OBJ)"), ("piipa-Ø", "paper-ACC")]
    translation := "The woman gave me paper."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-objective-accusative"), ("clause", "ditransitive")]
    comment := "Blake 1982, (47). Only the goal triggers object agreement; the case labels on the unmarked forms are Woolford's."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7]

end Woolford1997.Examples
