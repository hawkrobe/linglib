module

public import Linglib.Data.Examples.Schema

/-!
# `Lechner2004` — typed example data

Auto-generated from `Linglib/Data/Examples/Lechner2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Lechner2004.Examples`.
-/

@[expose] public section

namespace Lechner2004.Examples

open Data.Examples

def ch2_24 : LinguisticExample :=
  { id := "lechner2004_ch2_24"
    source := ⟨"lechner-2004", "(24) of chapter 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is prouder of John_i than he_i is."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "he = John"), ("deletion_site", "d-proud of John")] }

def ch2_25 : LinguisticExample :=
  { id := "lechner2004_ch2_25"
    source := ⟨"lechner-2004", "(25) of chapter 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is prouder of John_i than he_i believes that I am."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "he = John"), ("deletion_site", "d-proud of John")] }

def ch4_83a : LinguisticExample :=
  { id := "lechner2004_ch4_83a"
    source := ⟨"lechner-2004", "(83a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sally introduced him_i to more friends than Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "him = Peter"), ("remnant_case", "NOM")] }

def ch4_85a : LinguisticExample :=
  { id := "lechner2004_ch4_85a"
    source := ⟨"lechner-2004", "(85a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He_i introduced Sally to more friends than Peter_i's sister."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "he = Peter"), ("remnant_case", "ACC")] }

def ch4_87a : LinguisticExample :=
  { id := "lechner2004_ch4_87a"
    source := ⟨"lechner-2004", "(87a) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat ihm_i mehr Leute vorgestellt als Peters_i Schwester."
    glossedTokens := [("Sie", "she"), ("hat", "has"), ("ihm", "him"), ("mehr", "more"), ("Leute", "people"), ("vorgestellt", "introduced"), ("als", "than"), ("Peters", "Peter's"), ("Schwester", "sister")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "ihm = Peter"), ("remnant_case", "NOM")] }

def ch4_87b : LinguisticExample :=
  { id := "lechner2004_ch4_87b"
    source := ⟨"lechner-2004", "(87b) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er_i hat ihr mehr Leute vorgestellt als Peters_i Schwester."
    glossedTokens := [("Er", "he"), ("hat", "has"), ("ihr", "her"), ("mehr", "more"), ("Leute", "people"), ("vorgestellt", "introduced"), ("als", "than"), ("Peters", "Peter's"), ("Schwester", "sister")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "er = Peter"), ("remnant_case", "DAT")] }

def ch4_90a : LinguisticExample :=
  { id := "lechner2004_ch4_90a"
    source := ⟨"lechner-2004", "(90a) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Frau des Präsidenten_j schätzt die Öffentlichkeit mehr als ihn_j."
    glossedTokens := [("Die", "the"), ("Frau", "wife"), ("des", "of.the"), ("Präsidenten", "president"), ("schätzt", "appreciates"), ("die", "the"), ("Öffentlichkeit", "public"), ("mehr", "more"), ("als", "than"), ("ihn", "him")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "ihn = Präsident"), ("remnant_case", "ACC")] }

def ch4_91a : LinguisticExample :=
  { id := "lechner2004_ch4_91a"
    source := ⟨"lechner-2004", "(91a) of chapter 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Öffentlichkeit schätzt die Frau des Präsidenten_i mehr als er_i."
    glossedTokens := [("Die", "the"), ("Öffentlichkeit", "public"), ("schätzt", "appreciates"), ("die", "the"), ("Frau", "wife"), ("des", "of.the"), ("Präsidenten", "president"), ("mehr", "more"), ("als", "than"), ("er", "he")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("coreference", "er = Präsident"), ("remnant_case", "NOM")] }

def all : List LinguisticExample := [ch2_24, ch2_25, ch4_83a, ch4_85a, ch4_87a, ch4_87b, ch4_90a, ch4_91a]

end Lechner2004.Examples
