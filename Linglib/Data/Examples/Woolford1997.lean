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
    glossedTokens := [("'ipí-Ø", "he-NOM"), ("hi-kú-ye", "3-go-ASP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "nominative"), ("clause", "intransitive")] }

def ex_2 : LinguisticExample :=
  { id := "woolford1997_2"
    source := ⟨"woolford-1997", "(4)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Háama-Ø hi-'wí-ye wewúkiye-Ø."
    glossedTokens := [("Háama-Ø", "man-NOM"), ("hi-'wí-ye", "3-shoot-ASP"), ("wewúkiye-Ø", "elk-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "nominative-accusative"), ("clause", "transitive")] }

def ex_3 : LinguisticExample :=
  { id := "woolford1997_3"
    source := ⟨"woolford-1997", "(5)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Háama-nm pée-'wi-ye wewúkiye-ne."
    glossedTokens := [("Háama-nm", "man-ERG"), ("pée-'wi-ye", "3/3-shoot-ASP"), ("wewúkiye-ne", "elk-OBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-objective"), ("clause", "transitive")] }

def ex_4 : LinguisticExample :=
  { id := "woolford1997_4"
    source := ⟨"woolford-1997", "(6)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "ʔáayat-Ø hi-ʔni-ye tíim'es-Ø háama-Ø."
    glossedTokens := [("ʔáayat-Ø", "woman-NOM"), ("hi-ʔni-ye", "3-give-PAST"), ("tíim'es-Ø", "book-ACC"), ("háama-Ø", "husband-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "nominative-accusative-accusative"), ("clause", "ditransitive")] }

def ex_5 : LinguisticExample :=
  { id := "woolford1997_5"
    source := ⟨"woolford-1997", "(7)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "ʔáayato-m pée-ʔni-ye tíim'es-Ø háama-na."
    glossedTokens := [("ʔáayato-m", "woman-ERG"), ("pée-ʔni-ye", "3/3-give-PAST"), ("tíim'es-Ø", "book-ACC"), ("háama-na", "man-OBJ")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-objective-accusative"), ("clause", "ditransitive")] }

def ex_6 : LinguisticExample :=
  { id := "woolford1997_6"
    source := ⟨"woolford-1997", "(8)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "ʔáayato-m pée-ʔni-ye haswaláya-na háama-na."
    glossedTokens := [("ʔáayato-m", "woman-ERG"), ("pée-ʔni-ye", "3/3-give-PAST"), ("haswaláya-na", "slave-OBJ"), ("háama-na", "man-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-dative-objective"), ("clause", "ditransitive")] }

def ex_7 : LinguisticExample :=
  { id := "woolford1997_7"
    source := ⟨"woolford-1997", "(57)"⟩
    reportedIn := none
    language := "kalk1246"
    primaryText := "Maṛapai-tu anʸa-ŋi (ŋai-Ø) piipa-Ø."
    glossedTokens := [("Maṛapai-tu", "woman-ERG"), ("anʸa-ŋi", "gave-1SG.OBJ"), ("(ŋai-Ø)", "(me-OBJ)"), ("piipa-Ø", "paper-ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "ergative-objective-accusative"), ("clause", "ditransitive")] }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7]

end Woolford1997.Examples
