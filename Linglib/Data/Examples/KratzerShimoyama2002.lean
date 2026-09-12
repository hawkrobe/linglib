import Linglib.Data.Examples.Schema

/-!
# `KratzerShimoyama2002` — typed example data

Auto-generated from `Linglib/Data/Examples/KratzerShimoyama2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace KratzerShimoyama2002.Examples`.
-/

namespace KratzerShimoyama2002.Examples

open Data.Examples

def ex23a : LinguisticExample :=
  { id := "kratzershimoyama2002_ex23a"
    source := ⟨"kratzer-shimoyama-2002", "(23a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie nicht WEM gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("nicht", "not"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    translation := "What didn't she show to whom?"
    context := "Multiple question with the second wh-phrase in situ, the intervener preceding it."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nicht"), ("feature", "Neg"), ("order", "intervener-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23b : LinguisticExample :=
  { id := "kratzershimoyama2002_ex23b"
    source := ⟨"kratzer-shimoyama-2002", "(23b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie nie WEM gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("nie", "never"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    translation := "What didn't she show to whom?"
    context := "Multiple question with the second wh-phrase in situ, the intervener preceding it."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nie"), ("feature", "exists"), ("order", "intervener-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23c : LinguisticExample :=
  { id := "kratzershimoyama2002_ex23c"
    source := ⟨"kratzer-shimoyama-2002", "(23c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat niemand WEM gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("niemand", "nobody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    translation := "What did nobody show to whom?"
    context := "Multiple question with the second wh-phrase in situ, the intervener preceding it."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "niemand"), ("feature", "exists"), ("order", "intervener-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23d : LinguisticExample :=
  { id := "kratzershimoyama2002_ex23d"
    source := ⟨"kratzer-shimoyama-2002", "(23d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat fast jeder WEM gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("fast", "almost"), ("jeder", "everybody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    translation := "What did almost everybody show to whom?"
    context := "Multiple question with the second wh-phrase in situ, the intervener preceding it."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "fast jeder"), ("feature", "exists"), ("order", "intervener-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23e : LinguisticExample :=
  { id := "kratzershimoyama2002_ex23e"
    source := ⟨"kratzer-shimoyama-2002", "(23e)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat (irgend)jemand WEM gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("(irgend)jemand", "somebody"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    translation := "What did somebody show to whom?"
    context := "Multiple question with the second wh-phrase in situ, the intervener preceding it."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "(irgend)jemand"), ("feature", "exists"), ("order", "intervener-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23f : LinguisticExample :=
  { id := "kratzershimoyama2002_ex23f"
    source := ⟨"kratzer-shimoyama-2002", "(23f)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat der Hans WEM gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("der", "the"), ("Hans", "Hans"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    translation := "What did Hans show to whom?"
    context := "Multiple question with the second wh-phrase in situ, the intervener preceding it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "der Hans"), ("feature", "none"), ("order", "intervener-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23g : LinguisticExample :=
  { id := "kratzershimoyama2002_ex23g"
    source := ⟨"kratzer-shimoyama-2002", "(23g)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie damals WEM gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("damals", "then"), ("WEM", "to.whom"), ("gezeigt", "shown")]
    translation := "What did she show whom at the time?"
    context := "Multiple question with the second wh-phrase in situ, the intervener preceding it."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "damals"), ("feature", "none"), ("order", "intervener-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex24a : LinguisticExample :=
  { id := "kratzershimoyama2002_ex24a"
    source := ⟨"kratzer-shimoyama-2002", "(24a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie WEM nicht gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("WEM", "to.whom"), ("nicht", "not"), ("gezeigt", "shown")]
    translation := "What didn't she show to whom?"
    context := "The in-situ wh-phrase scrambled over the intervener."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nicht"), ("feature", "Neg"), ("order", "wh-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex24b : LinguisticExample :=
  { id := "kratzershimoyama2002_ex24b"
    source := ⟨"kratzer-shimoyama-2002", "(24b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat sie WEM nie gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("sie", "she"), ("WEM", "to.whom"), ("nie", "never"), ("gezeigt", "shown")]
    translation := "What didn't she show to whom?"
    context := "The in-situ wh-phrase scrambled over the intervener."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "nie"), ("feature", "exists"), ("order", "wh-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex24c : LinguisticExample :=
  { id := "kratzershimoyama2002_ex24c"
    source := ⟨"kratzer-shimoyama-2002", "(24c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM niemand gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("niemand", "nobody"), ("gezeigt", "shown")]
    translation := "What did nobody show to whom?"
    context := "The in-situ wh-phrase scrambled over the intervener."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "niemand"), ("feature", "exists"), ("order", "wh-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex24d : LinguisticExample :=
  { id := "kratzershimoyama2002_ex24d"
    source := ⟨"kratzer-shimoyama-2002", "(24d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM fast jeder gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("fast", "almost"), ("jeder", "everybody"), ("gezeigt", "shown")]
    translation := "What did almost everybody show to whom?"
    context := "The in-situ wh-phrase scrambled over the intervener."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "fast jeder"), ("feature", "exists"), ("order", "wh-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex24e : LinguisticExample :=
  { id := "kratzershimoyama2002_ex24e"
    source := ⟨"kratzer-shimoyama-2002", "(24e)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Was hat WEM (irgend)jemand gezeigt?"
    discourseSegments := []
    glossedTokens := [("Was", "what"), ("hat", "has"), ("WEM", "to.whom"), ("(irgend)jemand", "somebody"), ("gezeigt", "shown")]
    translation := "What did somebody show to whom?"
    context := "The in-situ wh-phrase scrambled over the intervener."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intervener", "(irgend)jemand"), ("feature", "exists"), ("order", "wh-first")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex23a, ex23b, ex23c, ex23d, ex23e, ex23f, ex23g, ex24a, ex24b, ex24c, ex24d, ex24e]

end KratzerShimoyama2002.Examples
