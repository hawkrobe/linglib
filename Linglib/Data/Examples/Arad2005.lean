import Linglib.Data.Examples.Schema

/-!
# `Arad2005` — typed example data

Auto-generated from `Linglib/Data/Examples/Arad2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Arad2005.Examples`.
-/

namespace Arad2005.Examples

open Data.Examples

def p1 : LinguisticExample :=
  { id := "arad2005_p1"
    source := ⟨"arad-2005", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "lamad"
    discourseSegments := []
    glossedTokens := [("lamad", "learn")]
    translation := "learn"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "lmd"), ("pattern", "1"), ("binyan", "cvcvc"), ("voice", "active")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p2 : LinguisticExample :=
  { id := "arad2005_p2"
    source := ⟨"arad-2005", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "nilmad"
    discourseSegments := []
    glossedTokens := [("nilmad", "learn (passive)")]
    translation := "learn"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "lmd"), ("pattern", "2"), ("binyan", "nvccvc"), ("voice", "active")]
    comment := "Binyan 2 is the passive of binyan 1 by rewriting of the binyan (footnote 13); its own vowels are the [+active] exponent in the context nVCCVC of (25)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p3 : LinguisticExample :=
  { id := "arad2005_p3"
    source := ⟨"arad-2005", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "siper"
    discourseSegments := []
    glossedTokens := [("siper", "tell")]
    translation := "tell"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "spr"), ("pattern", "3"), ("binyan", "cvccvc"), ("voice", "active")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p4 : LinguisticExample :=
  { id := "arad2005_p4"
    source := ⟨"arad-2005", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "supar"
    discourseSegments := []
    glossedTokens := [("supar", "tell (passive)")]
    translation := "tell"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "spr"), ("pattern", "4"), ("binyan", "cvccvc"), ("voice", "passive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p5 : LinguisticExample :=
  { id := "arad2005_p5"
    source := ⟨"arad-2005", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hiqlit"
    discourseSegments := []
    glossedTokens := [("hiqlit", "record")]
    translation := "record"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "qlt"), ("pattern", "5"), ("binyan", "hvccvc"), ("voice", "active")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p6 : LinguisticExample :=
  { id := "arad2005_p6"
    source := ⟨"arad-2005", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "huqlat"
    discourseSegments := []
    glossedTokens := [("huqlat", "record (passive)")]
    translation := "record"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "qlt"), ("pattern", "6"), ("binyan", "hvccvc"), ("voice", "passive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def p7 : LinguisticExample :=
  { id := "arad2005_p7"
    source := ⟨"arad-2005", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hitpalel"
    discourseSegments := []
    glossedTokens := [("hitpalel", "pray")]
    translation := "pray"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "pll"), ("pattern", "7"), ("binyan", "hitcvccvc"), ("voice", "active")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [p1, p2, p3, p4, p5, p6, p7]

end Arad2005.Examples
