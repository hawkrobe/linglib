import Linglib.Data.Examples.Schema

/-!
# `TurkHirsch2026` — typed example data

Auto-generated from `Linglib/Data/Examples/TurkHirsch2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TurkHirsch2026.Examples`.
-/

namespace TurkHirsch2026.Examples

open Data.Examples

def ex_4 : LinguisticExample :=
  { id := "turkhirsch2026_4"
    source := ⟨"turk-hirsch-2026", "(4)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali uyudu mu?"
    discourseSegments := []
    glossedTokens := [("Ali", "Ali[NOM]"), ("uyu-du=mu", "sleep-PST.3SG=FM")]
    translation := "Did Ali sleep?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "default"), ("focus", "sigma")]
    comment := "The focus clitic in its default rightmost position attaches to the covert polarity head; answerable by evet or hayır."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "turkhirsch2026_5"
    source := ⟨"turk-hirsch-2026", "(5)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "ALİ mi uyudu?"
    discourseSegments := []
    glossedTokens := [("Ali=mi", "Ali[NOM]=FM"), ("uyu-du", "sleep-PST.3SG")]
    translation := "Was it Ali who slept?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "subject"), ("focus", "subject")]
    comment := "The clitic on the stressed subject; the Hamblin set is the set of propositions that x slept, as for a wh-question, and a bare negative answer is incomplete, (6)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6a : LinguisticExample :=
  { id := "turkhirsch2026_6a"
    source := ⟨"turk-hirsch-2026", "(6a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Hayır."
    discourseSegments := []
    glossedTokens := [("Hayır", "no")]
    translation := "No."
    context := "Answer to (5)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "negative particle"), ("complete", "no")]
    comment := "Not a complete answer to (5): the response particle is anaphoric to the ordinary value of the TP, but a true member of the Hamblin set must still be supplied."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6b : LinguisticExample :=
  { id := "turkhirsch2026_6b"
    source := ⟨"turk-hirsch-2026", "(6b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Hayır, Veli uyudu."
    discourseSegments := []
    glossedTokens := [("Hayır", "no"), ("Veli", "Veli[NOM]"), ("uyu-du", "sleep-PST.3SG")]
    translation := "No, Veli slept."
    context := "Answer to (5)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "negative particle with continuation"), ("complete", "yes")]
    comment := "A complete answer to (5), naming the true member of the Hamblin set."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "turkhirsch2026_14"
    source := ⟨"turk-hirsch-2026", "(14)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Yannis Ali uyudu mu diye merak etti."
    discourseSegments := []
    glossedTokens := [("Yannis", "Yannis[NOM]"), ("Ali", "Ali[NOM]"), ("uyu-du=mu", "sleep-PST=FM"), ("diye", "that"), ("meraket-ti", "wonder-PST")]
    translation := "Yannis wondered whether Ali slept."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "below diye"), ("matrix", "declarative")]
    comment := "The clitic below the complementizer: the highest focus is in the embedded clause, whose alternatives are used up by the embedded question head, so the matrix clause is a declarative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "turkhirsch2026_18"
    source := ⟨"turk-hirsch-2026", "(18)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Yannis Ali uyudu diye mi merak etti?"
    discourseSegments := []
    glossedTokens := [("Yannis", "Yannis[NOM]"), ("Ali", "Ali[NOM]"), ("uyu-du", "sleep-PST"), ("diye=mi", "that=FM"), ("meraket-ti", "wonder-PST")]
    translation := "Is it whether Ali slept that Yannis wondered?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic_site", "above diye"), ("matrix", "question")]
    comment := "The clitic above the complementizer: the embedded clause is focused as a whole, its alternatives propagate to the matrix question head, and the matrix clause is a question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35a : LinguisticExample :=
  { id := "turkhirsch2026_35a"
    source := ⟨"turk-hirsch-2026", "(35a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Evet, Ali uyudu."
    discourseSegments := []
    glossedTokens := [("Evet", "yes"), ("Ali", "Ali[NOM]"), ("uyu-du", "sleep-PST.3SG")]
    translation := "Yes, Ali slept."
    context := "Answer to (22) at a world where Ali had to sleep and did sleep."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "positive"), ("complete", "yes")]
    comment := "The complete answer; the type-theoretic Hamblin set wrongly makes it partial."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35b : LinguisticExample :=
  { id := "turkhirsch2026_35b"
    source := ⟨"turk-hirsch-2026", "(35b)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Evet, Ali uyumak zorundaydı ve uyudu."
    discourseSegments := []
    glossedTokens := [("Evet", "yes"), ("Ali", "Ali[NOM]"), ("uyu-mak", "sleep-INF"), ("zorunda-ydı", "obligation-PST.3SG"), ("ve", "and"), ("uyu-du", "sleep-PST.3SG")]
    translation := "Yes, Ali had to sleep and he slept."
    context := "Answer to (22) at a world where Ali had to sleep and did sleep."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "modal conjunction"), ("complete", "over-informative")]
    comment := "Over-informative: the answer the type-theoretic Hamblin set predicts to be complete, (34)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_41 : LinguisticExample :=
  { id := "turkhirsch2026_41"
    source := ⟨"turk-hirsch-2026", "(41)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali uyumak zorundaydı."
    discourseSegments := []
    glossedTokens := [("Ali", "Ali[NOM]"), ("uyu-mak", "sleep-INF"), ("zorunda-y-dı", "obliged-COP-PST.3SG")]
    translation := "Ali had to sleep."
    context := "(39): Ali injured himself and went to the doctor for instructions; his partner tells us he slept for several hours after the appointment; we ask (22)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "modal"), ("complete", "no")]
    comment := "Not a licit answer to (22) even in a context supporting the modalized Hamblin set (38); the answer would have to be that Ali did sleep."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_4, ex_5, ex_6a, ex_6b, ex_14, ex_18, ex_35a, ex_35b, ex_41]

end TurkHirsch2026.Examples
