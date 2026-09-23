import Linglib.Data.Examples.Schema

/-!
# `RuytenbeekEtAl2017` — typed example data

Auto-generated from `Linglib/Data/Examples/RuytenbeekEtAl2017.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace RuytenbeekEtAl2017.Examples`.
-/

namespace RuytenbeekEtAl2017.Examples

open Data.Examples

def ruytenbeek2017_ex17 : LinguisticExample :=
  { id := "ruytenbeek2017_ex17"
    source := ⟨"ruytenbeek-etal-2017", "(17)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mettez le cercle rouge à gauche du rectangle jaune."
    discourseSegments := []
    glossedTokens := []
    translation := "Move the red circle to the left of the yellow rectangle."
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "imperative")]
    comment := "Control imperative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex18 : LinguisticExample :=
  { id := "ruytenbeek2017_ex18"
    source := ⟨"ruytenbeek-etal-2017", "(18)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Le cercle rouge est-il à gauche du rectangle jaune ?"
    discourseSegments := []
    glossedTokens := []
    translation := "Is the red circle on the left of the yellow rectangle?"
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "controlInterrogative")]
    comment := "Control interrogative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex19 : LinguisticExample :=
  { id := "ruytenbeek2017_ex19"
    source := ⟨"ruytenbeek-etal-2017", "(19)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pouvez-vous mettre le cercle rouge à gauche du rectangle jaune ?"
    discourseSegments := []
    glossedTokens := []
    translation := "Can you move the red circle to the left of the yellow rectangle?"
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "canYou")]
    comment := "Conventionalised indirect request."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex20 : LinguisticExample :=
  { id := "ruytenbeek2017_ex20"
    source := ⟨"ruytenbeek-etal-2017", "(20)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Est-il possible de mettre le cercle rouge à gauche du rectangle jaune ?"
    discourseSegments := []
    glossedTokens := []
    translation := "Is it possible to move the red circle to the left of the yellow rectangle?"
    context := "Study 1: a grid of coloured shapes with yes and no buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "1"), ("construction", "isItPossible")]
    comment := "Non-conventionalised indirect request."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex23 : LinguisticExample :=
  { id := "ruytenbeek2017_ex23"
    source := ⟨"ruytenbeek-etal-2017", "(23)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Vous devez mettre le cercle rouge à gauche du rectangle jaune."
    discourseSegments := []
    glossedTokens := []
    translation := "You must move the red circle to the left of the yellow rectangle."
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "youMust")]
    comment := "Deontic necessity declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex24 : LinguisticExample :=
  { id := "ruytenbeek2017_ex24"
    source := ⟨"ruytenbeek-etal-2017", "(24)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Mettez le cercle rouge à gauche du rectangle jaune."
    discourseSegments := []
    glossedTokens := []
    translation := "Move the red circle to the left of the yellow rectangle."
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "imperative")]
    comment := "Control imperative of Study 2."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex25 : LinguisticExample :=
  { id := "ruytenbeek2017_ex25"
    source := ⟨"ruytenbeek-etal-2017", "(25)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Vous pouvez mettre le cercle rouge à gauche du rectangle jaune."
    discourseSegments := []
    glossedTokens := []
    translation := "You can move the red circle to the left of the yellow rectangle."
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "youCan")]
    comment := "Possibility declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex26 : LinguisticExample :=
  { id := "ruytenbeek2017_ex26"
    source := ⟨"ruytenbeek-etal-2017", "(26)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Il est possible de mettre le cercle rouge à gauche du rectangle jaune."
    discourseSegments := []
    glossedTokens := []
    translation := "It is possible to move the red circle to the left of the yellow rectangle."
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "itIsPossible")]
    comment := "Impersonal possibility declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_ex27 : LinguisticExample :=
  { id := "ruytenbeek2017_ex27"
    source := ⟨"ruytenbeek-etal-2017", "(27)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Le cercle rouge est à gauche du rectangle jaune."
    discourseSegments := []
    glossedTokens := []
    translation := "The red circle is on the left of the yellow rectangle."
    context := "Study 2: a grid of coloured shapes with true and false buttons beneath it; the sentence is heard through headphones and answered either by moving a shape or by clicking a button."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("study", "2"), ("construction", "controlDeclarative")]
    comment := "Control declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_corpus_pouvezvous : LinguisticExample :=
  { id := "ruytenbeek2017_corpus_pouvezvous"
    source := ⟨"ruytenbeek-etal-2017", "(9)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pouvez-vous VP ?"
    discourseSegments := []
    glossedTokens := []
    translation := "Can you VP?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "canYou")]
    comment := "Frantext tokens after 1900 with a singular addressee, coded as indirect request, genuine question or rhetorical question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ruytenbeek2017_corpus_estilpossible : LinguisticExample :=
  { id := "ruytenbeek2017_corpus_estilpossible"
    source := ⟨"ruytenbeek-etal-2017", "(10)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Est-il possible de VP ?"
    discourseSegments := []
    glossedTokens := []
    translation := "Is it possible to VP?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "isItPossible")]
    comment := "Frantext tokens after 1900, coded as indirect request, genuine question or rhetorical question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ruytenbeek2017_ex17, ruytenbeek2017_ex18, ruytenbeek2017_ex19, ruytenbeek2017_ex20, ruytenbeek2017_ex23, ruytenbeek2017_ex24, ruytenbeek2017_ex25, ruytenbeek2017_ex26, ruytenbeek2017_ex27, ruytenbeek2017_corpus_pouvezvous, ruytenbeek2017_corpus_estilpossible]

end RuytenbeekEtAl2017.Examples
