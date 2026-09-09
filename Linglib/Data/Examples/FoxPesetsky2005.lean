import Linglib.Data.Examples.Schema

/-!
# `FoxPesetsky2005` — typed example data

Auto-generated from `Linglib/Data/Examples/FoxPesetsky2005.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FoxPesetsky2005.Examples`.
-/

namespace FoxPesetsky2005.Examples

open Data.Examples

def ex19a : LinguisticExample :=
  { id := "foxpesetsky2005_ex19a"
    source := ⟨"fox-pesetsky-2005", "(19a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag kysste henne inte"
    discourseSegments := []
    glossedTokens := [("Jag", "I"), ("kysste", "kissed"), ("henne", "her"), ("inte", "not")]
    translation := "I didn't kiss her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbToC", "yes"), ("aux", "no"), ("intervener", "none"), ("intervenerMoved", "no")]
    comment := "Verb-second: the finite verb moves to C and the pronoun shifts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19b : LinguisticExample :=
  { id := "foxpesetsky2005_ex19b"
    source := ⟨"fox-pesetsky-2005", "(19b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "att jag henne inte kysste"
    discourseSegments := []
    glossedTokens := [("att", "that"), ("jag", "I"), ("henne", "her"), ("inte", "not"), ("kysste", "kissed")]
    translation := "that I didn't kiss her"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verbToC", "no"), ("aux", "no"), ("intervener", "none"), ("intervenerMoved", "no")]
    comment := "Embedded clause: the complementizer blocks verb movement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex19c : LinguisticExample :=
  { id := "foxpesetsky2005_ex19c"
    source := ⟨"fox-pesetsky-2005", "(19c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag har henne inte kysst"
    discourseSegments := []
    glossedTokens := [("Jag", "I"), ("har", "have"), ("henne", "her"), ("inte", "not"), ("kysst", "kissed")]
    translation := "I haven't kissed her."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verbToC", "no"), ("aux", "yes"), ("intervener", "none"), ("intervenerMoved", "no")]
    comment := "The auxiliary moves to C and the participle stays in VP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23a : LinguisticExample :=
  { id := "foxpesetsky2005_ex23a"
    source := ⟨"fox-pesetsky-2005", "(23a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Jag gav den inte Elsa"
    discourseSegments := []
    glossedTokens := [("Jag", "I"), ("gav", "gave"), ("den", "it"), ("inte", "not"), ("Elsa", "Elsa")]
    translation := "I didn't give it to Elsa."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verbToC", "yes"), ("aux", "no"), ("intervener", "firstObject"), ("intervenerMoved", "no")]
    comment := "The first object precedes the shifted object in VP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex23b : LinguisticExample :=
  { id := "foxpesetsky2005_ex23b"
    source := ⟨"fox-pesetsky-2005", "(23b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Dom kastade mej inte ut"
    discourseSegments := []
    glossedTokens := [("Dom", "they"), ("kastade", "threw"), ("mej", "me"), ("inte", "not"), ("ut", "out")]
    translation := "They didn't throw me out."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verbToC", "yes"), ("aux", "no"), ("intervener", "particle"), ("intervenerMoved", "no")]
    comment := "The particle precedes the shifted object in VP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25a : LinguisticExample :=
  { id := "foxpesetsky2005_ex25a"
    source := ⟨"fox-pesetsky-2005", "(25a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Vem gav du den inte"
    discourseSegments := []
    glossedTokens := [("Vem", "who"), ("gav", "gave"), ("du", "you"), ("den", "it"), ("inte", "not")]
    translation := "Who didn't you give it to?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbToC", "yes"), ("aux", "no"), ("intervener", "firstObject"), ("intervenerMoved", "yes")]
    comment := "The first object is wh-moved through the VP edge."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex25b : LinguisticExample :=
  { id := "foxpesetsky2005_ex25b"
    source := ⟨"fox-pesetsky-2005", "(25b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Ut kastade dom mej inte"
    discourseSegments := []
    glossedTokens := [("Ut", "out"), ("kastade", "threw"), ("dom", "they"), ("mej", "me"), ("inte", "not")]
    translation := "Out they didn't throw me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verbToC", "yes"), ("aux", "no"), ("intervener", "particle"), ("intervenerMoved", "yes")]
    comment := "The particle is topicalized through the VP edge."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex19a, ex19b, ex19c, ex23a, ex23b, ex25a, ex25b]

end FoxPesetsky2005.Examples
