module

public import Linglib.Data.Examples.Schema

/-!
# `LevinRappaportHovav1995` — typed example data

Auto-generated from `Linglib/Data/Examples/LevinRappaportHovav1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LevinRappaportHovav1995.Examples`.
-/

@[expose] public section

namespace LevinRappaportHovav1995.Examples

open Data.Examples

def ex6_1 : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex6_1"
    source := ⟨"levin-hovav-1995", "(1) of chapter 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the distance appeared the towers and spires of a town which greatly resembled Oxford."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "locativeInversion"), ("verb", "appear"), ("class", "48.1.1")]
    comment := "A corpus locative inversion, from Bromfield, The Farm, with a verb of appearance."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6_4a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex6_4a"
    source := ⟨"levin-hovav-1995", "(4a) of chapter 6"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the distance there appeared the towers and spires of a town which greatly resembled Oxford."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "thereInsertion"), ("verb", "appear"), ("class", "48.1.1")]
    comment := "The there-insertion counterpart of (1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_31a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_31a"
    source := ⟨"levin-hovav-1995", "(31a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She arrived a glamorous arrival."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "cognateObject"), ("verb", "arrive"), ("class", "51.1"), ("agentive", "yes")]
    comment := "A verb of inherently directed motion rejects a cognate object, consistent with an unaccusative classification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_32c : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_32c"
    source := ⟨"levin-hovav-1995", "(32c) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She arrived her way to the front of the line."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "arrive"), ("class", "51.1"), ("agentive", "yes")]
    comment := "A verb of inherently directed motion rejects the X's way construction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_50a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_50a"
    source := ⟨"levin-hovav-1995", "(50a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The jogger ran his soles thin."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "run"), ("class", "51.3.2"), ("agentive", "yes")]
    comment := "A run verb in the unergative resultative pattern, the result phrase predicated of a nonsubcategorized object."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_51a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_51a"
    source := ⟨"levin-hovav-1995", "(51a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The jogger ran sore."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "run"), ("class", "51.3.2"), ("agentive", "yes")]
    comment := "A run verb rejects the unaccusative resultative pattern."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_52a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_52a"
    source := ⟨"levin-hovav-1995", "(52a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door rolled open."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnaccusativePattern"), ("verb", "roll"), ("class", "51.3.1"), ("agentive", "no")]
    comment := "A roll verb in the unaccusative resultative pattern, the result phrase predicated of the subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_53a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_53a"
    source := ⟨"levin-hovav-1995", "(53a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The door rolled itself open."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultativeUnergativePattern"), ("verb", "roll"), ("class", "51.3.1"), ("agentive", "no")]
    comment := "A roll verb rejects the unergative resultative pattern with a fake reflexive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_54a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_54a"
    source := ⟨"levin-hovav-1995", "(54a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The jogger ran his way to better health."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "run"), ("class", "51.3.2"), ("agentive", "yes")]
    comment := "A run verb in the X's way construction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4_55a : LinguisticExample :=
  { id := "levinrappaporthovav1995_ex4_55a"
    source := ⟨"levin-hovav-1995", "(55a) of chapter 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pebbles rolled their way into the stream."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "wayConstruction"), ("verb", "roll"), ("class", "51.3.1"), ("agentive", "no")]
    comment := "A roll verb rejects the X's way construction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex6_1, ex6_4a, ex4_31a, ex4_32c, ex4_50a, ex4_51a, ex4_52a, ex4_53a, ex4_54a, ex4_55a]

end LevinRappaportHovav1995.Examples
