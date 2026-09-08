import Linglib.Data.Examples.Schema

/-!
# `DechaineWiltschko2002` — typed example data

Auto-generated from `Linglib/Data/Examples/DechaineWiltschko2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace DechaineWiltschko2002.Examples`.
-/

namespace DechaineWiltschko2002.Examples

open Data.Examples

def ex32a_1 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex32a_1"
    source := ⟨"dechaine-wiltschko-2002", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "we linguists"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "we"), ("dialect", "A")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32a_2 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex32a_2"
    source := ⟨"dechaine-wiltschko-2002", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "us linguists"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "us"), ("dialect", "A")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32b : LinguisticExample :=
  { id := "dechainewiltschko2002_ex32b"
    source := ⟨"dechaine-wiltschko-2002", "(32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "you linguists"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "you"), ("dialect", "A")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32c_1 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex32c_1"
    source := ⟨"dechaine-wiltschko-2002", "(32c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "they linguists"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "they"), ("dialect", "A")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32c_2 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex32c_2"
    source := ⟨"dechaine-wiltschko-2002", "(32c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "them linguists"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "them"), ("dialect", "A")]
    comment := "Standard American English, dialect A."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34c_1 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex34c_1"
    source := ⟨"dechaine-wiltschko-2002", "(34c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "they linguists"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "they"), ("dialect", "B")]
    comment := "Dialect B, which has no reduced *'ey*."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34c_2 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex34c_2"
    source := ⟨"dechaine-wiltschko-2002", "(34c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "them linguists"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "precedesNoun"), ("pronoun", "them"), ("dialect", "B")]
    comment := "Dialect B, where *them* is the D-morpheme *th-* over the clitic *'em*, (37c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex38"
    source := ⟨"dechaine-wiltschko-2002", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every candidate thinks that he will win."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "he")]
    comment := "Bound-variable construal: for every candidate x, x thinks that x will win."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40 : LinguisticExample :=
  { id := "dechainewiltschko2002_ex40"
    source := ⟨"dechaine-wiltschko-2002", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know that John saw me, and Mary does too."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := [("strict", .acceptable), ("sloppy", .unacceptable)]
    paperFeatures := [("test", "boundVariable"), ("pronoun", "me")]
    comment := "The sloppy reading, on which Mary knows that John saw her, is unavailable: *me* is not construed as a bound variable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30a : LinguisticExample :=
  { id := "dechainewiltschko2002_ex30a"
    source := ⟨"dechaine-wiltschko-2002", "(30a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody thinks one is a genius."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "one")]
    comment := "Intended: for every x, x thinks that x is a genius."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30b : LinguisticExample :=
  { id := "dechainewiltschko2002_ex30b"
    source := ⟨"dechaine-wiltschko-2002", "(30b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Everybody loves one's mother."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "one")]
    comment := "Intended: for every x, x loves x's mother."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex22a : LinguisticExample :=
  { id := "dechainewiltschko2002_ex22a"
    source := ⟨"dechaine-wiltschko-2002", "(22a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Daremo-ga kare-no hahaoya-o aisite-iru."
    discourseSegments := []
    glossedTokens := []
    translation := "Everyone loves his mother."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "boundVariable"), ("pronoun", "kare")]
    comment := "Intended: for every x, x loves x's mother; reported from Noguchi (1997)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex32a_1, ex32a_2, ex32b, ex32c_1, ex32c_2, ex34c_1, ex34c_2, ex38, ex40, ex30a, ex30b, ex22a]

end DechaineWiltschko2002.Examples
