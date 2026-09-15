import Linglib.Data.Examples.Schema

/-!
# `Wood2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Wood2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Wood2015.Examples`.
-/

namespace Wood2015.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "wood2015_1"
    source := ⟨"wood-2015", "(75a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust eftir ballið."
    discourseSegments := []
    glossedTokens := [("Jóna", "Jóna.NOM"), ("og", "and"), ("Siggi", "Siggi.NOM"), ("kysstust", "kissed-ST"), ("eftir", "after"), ("ballið", "dance.the")]
    translation := "Jóna and Siggi kissed after the dance."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reciprocal")]
    comment := "A reciprocal use of -st. Numbering follows the 2012 dissertation the book revises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "wood2015_2"
    source := ⟨"wood-2015", "(75b)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jón dulbjóst sem prestur."
    discourseSegments := []
    glossedTokens := [("Jón", "John.NOM"), ("dulbjóst", "disguised-ST"), ("sem", "as"), ("prestur", "priest")]
    translation := "John disguised himself as a priest."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "reflexive")]
    comment := "A reflexive use of -st. Numbering follows the 2012 dissertation the book revises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "wood2015_3"
    source := ⟨"wood-2015", "(75c)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Glugginn opnaðist af sjálfu sér."
    discourseSegments := []
    glossedTokens := [("Glugginn", "window.the.NOM"), ("opnaðist", "opened-ST"), ("af", "by"), ("sjálfu", "self.DAT"), ("sér", "REFL")]
    translation := "The window opened by itself."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anticausative")]
    comment := "An anticausative use of -st. Numbering follows the 2012 dissertation the book revises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "wood2015_4"
    source := ⟨"wood-2015", "(112a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "klæðast"
    discourseSegments := []
    glossedTokens := [("klæðast", "dress-ST")]
    translation := "dress oneself"
    context := ""
    judgment := .acceptable
    alternatives := [("klæða", .acceptable)]
    readings := []
    paperFeatures := [("construction", "figure reflexive")]
    comment := "The alternation between klæða 'dress' and klæðast, analysed as a figure reflexive with -st in SpecpP. Numbering follows the 2012 dissertation the book revises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "wood2015_5"
    source := ⟨"wood-2015", "(182)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Dyrnar opnuðust."
    discourseSegments := []
    glossedTokens := [("Dyrnar", "door.the.NOM"), ("opnuðust", "opened-ST")]
    translation := "The door opened."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "anticausative"), ("verb", "opnast")]
    comment := "The -st anticausative of opna 'open'. Numbering follows the 2012 dissertation the book revises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "wood2015_6"
    source := ⟨"wood-2015", "(383a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Henni leiddist Ólafur."
    discourseSegments := []
    glossedTokens := [("Henni", "her.DAT"), ("leiddist", "bored-ST"), ("Ólafur", "Ólafur.NOM")]
    translation := "She was bored by Ólafur."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "subject experiencer"), ("subject", "dative")]
    comment := "A dative-subject psych verb with -st. Numbering follows the 2012 dissertation the book revises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "wood2015_7"
    source := ⟨"wood-2015", "(426a)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Jóna og Siggi kysstust."
    discourseSegments := []
    glossedTokens := [("Jóna", "Jóna"), ("og", "and"), ("Siggi", "Siggi"), ("kysstust", "kissed-ST")]
    translation := "Jóna and Siggi kissed."
    context := ""
    judgment := .acceptable
    alternatives := [("Jóna kysstist við Sigga.", .ungrammatical)]
    readings := []
    paperFeatures := [("construction", "reciprocal"), ("verb", "kyssast")]
    comment := "The reciprocal -st verb needs a plural subject; the discontinuous variant is out. Numbering follows the 2012 dissertation the book revises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7]

end Wood2015.Examples
