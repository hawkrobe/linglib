module

public import Linglib.Data.Examples.Schema

/-!
# `Imanishi2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Imanishi2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Imanishi2014.Examples`.
-/

@[expose] public section

namespace Imanishi2014.Examples

open Data.Examples

def s89 : LinguisticExample :=
  { id := "imanishi2014_s89"
    source := ⟨"imanishi-2014", "(89)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i katastrofi tis polis apo tus varvarus mesa se tris meres"
    glossedTokens := [("i", "the"), ("katastrofi", "destruction"), ("tis", "the"), ("polis", "city-GEN"), ("apo", "by"), ("tus", "the"), ("varvarus", "barbarians"), ("mesa", "within"), ("se", "in"), ("tris", "three"), ("meres", "days")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("source", "Alexiadou 2001:76"), ("nominalization", "external argument introduced by a preposition")] }

def s91 : LinguisticExample :=
  { id := "imanishi2014_s91"
    source := ⟨"imanishi-2014", "(91)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-k'at-ïk ri tinamit [ri x-ø-b'än ri a Juan] x-ø-xib'i-n."
    glossedTokens := [("ri", "DET"), ("ru-k'at-ïk", "ERG3S-burn-NOML"), ("ri", "DET"), ("tinamit", "city"), ("ri", "DET"), ("x-ø-b'än", "PRFV-ABS3S-do"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PRFV-ABS3S-scare-AP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("nominalization", "only the internal argument inside; the agent in a relative clause")] }

def s92 : LinguisticExample :=
  { id := "imanishi2014_s92"
    source := ⟨"imanishi-2014", "(92)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ru-k'at-ïk ri a Juan x-ø-xib'i-n."
    glossedTokens := [("ru-k'at-ïk", "ERG3S-burn-NOML"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PRFV-ABS3S-scare-AP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("nominalization", "a sole argument is the internal argument")] }

def s93a : LinguisticExample :=
  { id := "imanishi2014_s93a"
    source := ⟨"imanishi-2014", "(93a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [ki-k'ul-ik ak'wal-a']."
    glossedTokens := [("y-in-ajin", "IMPF-ABS1S-PROG"), ("che", "PREP"), ("ki-k'ul-ik", "ERG3P-meet.PAS-NOML"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("alignment", "S/A=ABS on ajin, O=ERG on the nominalized verb")] }

def s93b : LinguisticExample :=
  { id := "imanishi2014_s93b"
    source := ⟨"imanishi-2014", "(93b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [atin-ïk]."
    glossedTokens := [("y-in-ajin", "IMPF-ABS1S-PROG"), ("che", "PREP"), ("atin-ïk", "bathe-NOML")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("alignment", "S=ABS on ajin")] }

def s94a : LinguisticExample :=
  { id := "imanishi2014_s94a"
    source := ⟨"imanishi-2014", "(94a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "roj x-ø-qa-chäp [ki-k'ul-ik rje']."
    glossedTokens := [("roj", "we"), ("x-ø-qa-chäp", "PRFV-ABS3S-ERG1P-begin"), ("ki-k'ul-ik", "ERG3P-meet.PAS-NOML"), ("rje'", "they")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("construction", "embedding verb chäp 'begin'")] }

def s99b : LinguisticExample :=
  { id := "imanishi2014_s99b"
    source := ⟨"imanishi-2014", "(99b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-oj-ajin che ru-tik-ik jun k'otz'i'j."
    glossedTokens := [("y-oj-ajin", "IMPF-ABS1P-PROG"), ("che", "PREP"), ("ru-tik-ik", "ERG3S-plant.PAS-NOML"), ("jun", "one"), ("k'otz'i'j", "flower")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "tensed vowel of the root transitive under nominalization")] }

def s100b : LinguisticExample :=
  { id := "imanishi2014_s100b"
    source := ⟨"imanishi-2014", "(100b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "rje' y-e-ajin che ru-tuk-ik sopa."
    glossedTokens := [("rje'", "they"), ("y-e-ajin", "IMPF-ABS3P-PROG"), ("che", "PREP"), ("ru-tuk-ik", "ERG3S-stir.PAS-NOML"), ("sopa", "soup")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "tensed vowel of the root transitive under nominalization")] }

def s102b : LinguisticExample :=
  { id := "imanishi2014_s102b"
    source := ⟨"imanishi-2014", "(102b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "roj y-oj-ajin che ki-q'ete-x-ïk ri ak'wal-a'."
    glossedTokens := [("roj", "we"), ("y-oj-ajin", "IMPF-ABS1P-PROG"), ("che", "PREP"), ("ki-q'ete-x-ïk", "ERG3P-hug-PAS-NOML"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "the passive suffix -x on the derived transitive under nominalization")] }

def s137a : LinguisticExample :=
  { id := "imanishi2014_s137a"
    source := ⟨"imanishi-2014", "(137a)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-jats'-oñ]."
    glossedTokens := [("Choñkol-ø", "PROG-ABS3S"), ("i-jats'-oñ", "ERG3S-hit-ABS1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Coon 2013a:11"), ("alignment", "A=ERG, O=ABS inside the nominalized clause")] }

def s137b : LinguisticExample :=
  { id := "imanishi2014_s137b"
    source := ⟨"imanishi-2014", "(137b)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-majl-el]."
    glossedTokens := [("Choñkol-ø", "PROG-ABS3S"), ("i-majl-el", "ERG3S-go-NOML")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Coon 2013a:11"), ("alignment", "S=ERG")] }

def s138a : LinguisticExample :=
  { id := "imanishi2014_s138a"
    source := ⟨"imanishi-2014", "(138a)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [hach w-il-on-i]."
    glossedTokens := [("lanan-ø", "PROG-ABS3S"), ("hach", "ABS2S"), ("w-il-on-i", "ERG1S-see-DM-ITV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Mateo Pedro 2009"), ("alignment", "A=ERG, O=ABS, the suffix -on supplying object Case")] }

def s138b : LinguisticExample :=
  { id := "imanishi2014_s138b"
    source := ⟨"imanishi-2014", "(138b)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [ha-way-i]."
    glossedTokens := [("lanan-ø", "PROG-ABS3S"), ("ha-way-i", "ERG2S-sleep-ITV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Mateo Pedro 2009"), ("alignment", "S=ERG")] }

def s181 : LinguisticExample :=
  { id := "imanishi2014_s181"
    source := ⟨"imanishi-2014", "(181)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "at-s txab'an siich' ok q-ook-a juu7n priim."
    glossedTokens := [("at-s", "LOC-ABS3S"), ("txab'an", "bit"), ("siich'", "cigarette"), ("ok", "when"), ("q-ook-a", "ERG1P-enter-1P"), ("juu7n", "each"), ("priim", "early")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.4"), ("source", "England 1983b:265"), ("alignment", "S=ERG in an aspectless temporal clause")] }

def s182 : LinguisticExample :=
  { id := "imanishi2014_s182"
    source := ⟨"imanishi-2014", "(182)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ok qo tzaalaj-al ok t-q-il u7j t-e yool t-e I7tzal"
    glossedTokens := [("ok", "POT"), ("qo", "ABS1P"), ("tzaalaj-al", "be.happy-POT"), ("ok", "when"), ("t-q-il", "ERG3S-ERG1P-see"), ("u7j", "book"), ("t-e", "ERG3S-RN"), ("yool", "word"), ("t-e", "ERG3S-RN"), ("I7tzal", "Ixtahuacán")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.4"), ("source", "England 1983b:260"), ("alignment", "double ergative: A and O both ERG")] }

def t178_kaqchikel : LinguisticExample :=
  { id := "imanishi2014_t178_kaqchikel"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Kaqchikel: non-perfective alignment S/A=ABS, O=ERG"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "+"), ("alignment", "S/A=ABS, O=ERG")] }

def t178_tojolabal : LinguisticExample :=
  { id := "imanishi2014_t178_tojolabal"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "tojo1241"
    primaryText := "Tojolabal: non-perfective alignment S/A=ABS, O=ERG"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "+"), ("alignment", "S/A=ABS, O=ERG")] }

def t178_chol : LinguisticExample :=
  { id := "imanishi2014_t178_chol"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Chol: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_qanjobal : LinguisticExample :=
  { id := "imanishi2014_t178_qanjobal"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "Q'anjob'al: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_chuj : LinguisticExample :=
  { id := "imanishi2014_t178_chuj"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "chuj1250"
    primaryText := "Chuj: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_ixil : LinguisticExample :=
  { id := "imanishi2014_t178_ixil"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "ixil1251"
    primaryText := "Ixil: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def t178_yucatec : LinguisticExample :=
  { id := "imanishi2014_t178_yucatec"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "Yucatec: non-perfective alignment S/A=ERG, O=ABS"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")] }

def all : List LinguisticExample := [s89, s91, s92, s93a, s93b, s94a, s99b, s100b, s102b, s137a, s137b, s138a, s138b, s181, s182, t178_kaqchikel, t178_tojolabal, t178_chol, t178_qanjobal, t178_chuj, t178_ixil, t178_yucatec]

end Imanishi2014.Examples
