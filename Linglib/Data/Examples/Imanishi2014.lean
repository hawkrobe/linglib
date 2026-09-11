import Linglib.Data.Examples.Schema

/-!
# `Imanishi2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Imanishi2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Imanishi2014.Examples`.
-/

namespace Imanishi2014.Examples

open Data.Examples

def s89 : LinguisticExample :=
  { id := "imanishi2014_s89"
    source := ⟨"imanishi-2014", "(89)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "i katastrofi tis polis apo tus varvarus mesa se tris meres"
    discourseSegments := []
    glossedTokens := [("i", "the"), ("katastrofi", "destruction"), ("tis", "the"), ("polis", "city-GEN"), ("apo", "by"), ("tus", "the"), ("varvarus", "barbarians"), ("mesa", "within"), ("se", "in"), ("tris", "three"), ("meres", "days")]
    translation := "The destruction of the city by the barbarians within three days"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("source", "Alexiadou 2001:76"), ("nominalization", "external argument introduced by a preposition")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s91 : LinguisticExample :=
  { id := "imanishi2014_s91"
    source := ⟨"imanishi-2014", "(91)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ri ru-k'at-ïk ri tinamit [ri x-ø-b'än ri a Juan] x-ø-xib'i-n."
    discourseSegments := []
    glossedTokens := [("ri", "DET"), ("ru-k'at-ïk", "ERG3S-burn-NOML"), ("ri", "DET"), ("tinamit", "city"), ("ri", "DET"), ("x-ø-b'än", "PRFV-ABS3S-do"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PRFV-ABS3S-scare-AP")]
    translation := "Juan's burning of the city was scary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("nominalization", "only the internal argument inside; the agent in a relative clause")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s92 : LinguisticExample :=
  { id := "imanishi2014_s92"
    source := ⟨"imanishi-2014", "(92)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "ru-k'at-ïk ri a Juan x-ø-xib'i-n."
    discourseSegments := []
    glossedTokens := [("ru-k'at-ïk", "ERG3S-burn-NOML"), ("ri", "DET"), ("a", "CL"), ("Juan", "Juan"), ("x-ø-xib'i-n", "PRFV-ABS3S-scare-AP")]
    translation := "Juan's burning was scary. (Juan was burned; not: Juan burned something.)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("nominalization", "a sole argument is the internal argument")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s93a : LinguisticExample :=
  { id := "imanishi2014_s93a"
    source := ⟨"imanishi-2014", "(93a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [ki-k'ul-ik ak'wal-a']."
    discourseSegments := []
    glossedTokens := [("y-in-ajin", "IMPF-ABS1S-PROG"), ("che", "PREP"), ("ki-k'ul-ik", "ERG3P-meet.PAS-NOML"), ("ak'wal-a'", "child-PL")]
    translation := "I am meeting children."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("alignment", "S/A=ABS on ajin, O=ERG on the nominalized verb")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s93b : LinguisticExample :=
  { id := "imanishi2014_s93b"
    source := ⟨"imanishi-2014", "(93b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-in-ajin che [atin-ïk]."
    discourseSegments := []
    glossedTokens := [("y-in-ajin", "IMPF-ABS1S-PROG"), ("che", "PREP"), ("atin-ïk", "bathe-NOML")]
    translation := "I am bathing."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("alignment", "S=ABS on ajin")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s94a : LinguisticExample :=
  { id := "imanishi2014_s94a"
    source := ⟨"imanishi-2014", "(94a)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "roj x-ø-qa-chäp [ki-k'ul-ik rje']."
    discourseSegments := []
    glossedTokens := [("roj", "we"), ("x-ø-qa-chäp", "PRFV-ABS3S-ERG1P-begin"), ("ki-k'ul-ik", "ERG3P-meet.PAS-NOML"), ("rje'", "they")]
    translation := "We began to meet them."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("construction", "embedding verb chäp 'begin'")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s99b : LinguisticExample :=
  { id := "imanishi2014_s99b"
    source := ⟨"imanishi-2014", "(99b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "y-oj-ajin che ru-tik-ik jun k'otz'i'j."
    discourseSegments := []
    glossedTokens := [("y-oj-ajin", "IMPF-ABS1P-PROG"), ("che", "PREP"), ("ru-tik-ik", "ERG3S-plant.PAS-NOML"), ("jun", "one"), ("k'otz'i'j", "flower")]
    translation := "We are planting one flower."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "tensed vowel of the root transitive under nominalization")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s100b : LinguisticExample :=
  { id := "imanishi2014_s100b"
    source := ⟨"imanishi-2014", "(100b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "rje' y-e-ajin che ru-tuk-ik sopa."
    discourseSegments := []
    glossedTokens := [("rje'", "they"), ("y-e-ajin", "IMPF-ABS3P-PROG"), ("che", "PREP"), ("ru-tuk-ik", "ERG3S-stir.PAS-NOML"), ("sopa", "soup")]
    translation := "They are stirring soup."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "tensed vowel of the root transitive under nominalization")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s102b : LinguisticExample :=
  { id := "imanishi2014_s102b"
    source := ⟨"imanishi-2014", "(102b)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "roj y-oj-ajin che ki-q'ete-x-ïk ri ak'wal-a'."
    discourseSegments := []
    glossedTokens := [("roj", "we"), ("y-oj-ajin", "IMPF-ABS1P-PROG"), ("che", "PREP"), ("ki-q'ete-x-ïk", "ERG3P-hug-PAS-NOML"), ("ri", "DET"), ("ak'wal-a'", "child-PL")]
    translation := "We are hugging the children."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.1"), ("passivization", "the passive suffix -x on the derived transitive under nominalization")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s137a : LinguisticExample :=
  { id := "imanishi2014_s137a"
    source := ⟨"imanishi-2014", "(137a)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-jats'-oñ]."
    discourseSegments := []
    glossedTokens := [("Choñkol-ø", "PROG-ABS3S"), ("i-jats'-oñ", "ERG3S-hit-ABS1S")]
    translation := "She's hitting me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Coon 2013a:11"), ("alignment", "A=ERG, O=ABS inside the nominalized clause")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s137b : LinguisticExample :=
  { id := "imanishi2014_s137b"
    source := ⟨"imanishi-2014", "(137b)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Choñkol-ø [i-majl-el]."
    discourseSegments := []
    glossedTokens := [("Choñkol-ø", "PROG-ABS3S"), ("i-majl-el", "ERG3S-go-NOML")]
    translation := "She's going."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Coon 2013a:11"), ("alignment", "S=ERG")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s138a : LinguisticExample :=
  { id := "imanishi2014_s138a"
    source := ⟨"imanishi-2014", "(138a)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [hach w-il-on-i]."
    discourseSegments := []
    glossedTokens := [("lanan-ø", "PROG-ABS3S"), ("hach", "ABS2S"), ("w-il-on-i", "ERG1S-see-DM-ITV")]
    translation := "I am seeing you."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Mateo Pedro 2009"), ("alignment", "A=ERG, O=ABS, the suffix -on supplying object Case")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s138b : LinguisticExample :=
  { id := "imanishi2014_s138b"
    source := ⟨"imanishi-2014", "(138b)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "lanan-ø [ha-way-i]."
    discourseSegments := []
    glossedTokens := [("lanan-ø", "PROG-ABS3S"), ("ha-way-i", "ERG2S-sleep-ITV")]
    translation := "You are sleeping."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3.3"), ("source", "Mateo Pedro 2009"), ("alignment", "S=ERG")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s181 : LinguisticExample :=
  { id := "imanishi2014_s181"
    source := ⟨"imanishi-2014", "(181)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "at-s txab'an siich' ok q-ook-a juu7n priim."
    discourseSegments := []
    glossedTokens := [("at-s", "LOC-ABS3S"), ("txab'an", "bit"), ("siich'", "cigarette"), ("ok", "when"), ("q-ook-a", "ERG1P-enter-1P"), ("juu7n", "each"), ("priim", "early")]
    translation := "There are bits of cigarette there when we go by in the morning."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.4"), ("source", "England 1983b:265"), ("alignment", "S=ERG in an aspectless temporal clause")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s182 : LinguisticExample :=
  { id := "imanishi2014_s182"
    source := ⟨"imanishi-2014", "(182)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ok qo tzaalaj-al ok t-q-il u7j t-e yool t-e I7tzal"
    discourseSegments := []
    glossedTokens := [("ok", "POT"), ("qo", "ABS1P"), ("tzaalaj-al", "be.happy-POT"), ("ok", "when"), ("t-q-il", "ERG3S-ERG1P-see"), ("u7j", "book"), ("t-e", "ERG3S-RN"), ("yool", "word"), ("t-e", "ERG3S-RN"), ("I7tzal", "Ixtahuacán")]
    translation := "We will be happy when we see the Ixtahuacán dictionary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.4"), ("source", "England 1983b:260"), ("alignment", "double ergative: A and O both ERG")]
    comment := "An apparent counterexample to phase head ergative Case; attributed to a second, covert phase head."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t178_kaqchikel : LinguisticExample :=
  { id := "imanishi2014_t178_kaqchikel"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "kaqc1270"
    primaryText := "Kaqchikel: non-perfective alignment S/A=ABS, O=ERG"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "+"), ("alignment", "S/A=ABS, O=ERG")]
    comment := "Summary of the nominative-accusative alignment in non-perfective clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t178_tojolabal : LinguisticExample :=
  { id := "imanishi2014_t178_tojolabal"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "tojo1241"
    primaryText := "Tojolabal: non-perfective alignment S/A=ABS, O=ERG"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "+"), ("alignment", "S/A=ABS, O=ERG")]
    comment := "Summary of the nominative-accusative alignment in non-perfective clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t178_chol : LinguisticExample :=
  { id := "imanishi2014_t178_chol"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "chol1282"
    primaryText := "Chol: non-perfective alignment S/A=ERG, O=ABS"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")]
    comment := "Summary of the nominative-accusative alignment in non-perfective clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t178_qanjobal : LinguisticExample :=
  { id := "imanishi2014_t178_qanjobal"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "qanj1241"
    primaryText := "Q'anjob'al: non-perfective alignment S/A=ERG, O=ABS"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")]
    comment := "Summary of the nominative-accusative alignment in non-perfective clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t178_chuj : LinguisticExample :=
  { id := "imanishi2014_t178_chuj"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "chuj1250"
    primaryText := "Chuj: non-perfective alignment S/A=ERG, O=ABS"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "high"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")]
    comment := "Summary of the nominative-accusative alignment in non-perfective clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t178_ixil : LinguisticExample :=
  { id := "imanishi2014_t178_ixil"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "ixil1251"
    primaryText := "Ixil: non-perfective alignment S/A=ERG, O=ABS"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")]
    comment := "Summary of the nominative-accusative alignment in non-perfective clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def t178_yucatec : LinguisticExample :=
  { id := "imanishi2014_t178_yucatec"
    source := ⟨"imanishi-2014", "(178)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "Yucatec: non-perfective alignment S/A=ERG, O=ABS"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("absolutive", "low"), ("urn", "-"), ("alignment", "S/A=ERG, O=ABS")]
    comment := "Summary of the nominative-accusative alignment in non-perfective clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [s89, s91, s92, s93a, s93b, s94a, s99b, s100b, s102b, s137a, s137b, s138a, s138b, s181, s182, t178_kaqchikel, t178_tojolabal, t178_chol, t178_qanjobal, t178_chuj, t178_ixil, t178_yucatec]

end Imanishi2014.Examples
