import Linglib.Data.Examples.Schema

/-!
# `Benz2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Benz2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Benz2025.Examples`.
-/

namespace Benz2025.Examples

open Data.Examples

def ex32a : LinguisticExample :=
  { id := "benz2025_ex32a"
    source := ⟨"benz-2025", "(32a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Beobachtung des Nachthimmels dauerte drei Stunden"
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Beobacht-ung", "observe-NMLZ"), ("des", "the.GEN"), ("Nachthimmels", "night.sky"), ("dauerte", "took"), ("drei", "three"), ("Stunden", "hours")]
    translation := "The observation of the night sky took three hours."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "Event"), ("duration_predicate", "yes"), ("plural", "no"), ("cp_complement", "no")]
    comment := "The Event member of the three-way ambiguity; the duration predicate diagnoses the complex event reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32b : LinguisticExample :=
  { id := "benz2025_ex32b"
    source := ⟨"benz-2025", "(32b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Beobachtungen der Astronomin sind für immer verloren"
    discourseSegments := []
    glossedTokens := [("Die", "the"), ("Beobacht-ung-en", "observe-NMLZ-PL"), ("der", "the.GEN"), ("Astronomin", "astronomer"), ("sind", "are"), ("für", "for"), ("immer", "ever"), ("verloren", "lost")]
    translation := "The astronomer's observations are lost forever."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("concrete object", .acceptable), ("result", .acceptable), ("content", .acceptable)]
    paperFeatures := [("reading", "RN"), ("duration_predicate", "no"), ("plural", "yes"), ("cp_complement", "no")]
    comment := "The RN member; in this context the pluralized nominalization can refer to concrete objects, to results, or in principle to contents."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex32c : LinguisticExample :=
  { id := "benz2025_ex32c"
    source := ⟨"benz-2025", "(32c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Seine Beobachtung, dass Planeten sich bewegen, veränderte die Wissenschaft"
    discourseSegments := []
    glossedTokens := [("Seine", "his"), ("Beobacht-ung", "observe-NMLZ"), ("dass", "COMP"), ("Planeten", "planets"), ("sich", "REFL"), ("bewegen", "move"), ("veränderte", "changed"), ("die", "the"), ("Wissenschaft", "science")]
    translation := "His observation that planets move changed the science."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "Content"), ("duration_predicate", "no"), ("plural", "no"), ("cp_complement", "yes")]
    comment := "The Content member; the CP complement specifies the content the noun refers to."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex89a : LinguisticExample :=
  { id := "benz2025_ex89a"
    source := ⟨"benz-2025", "(89a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er hämmerte das Metall platt"
    discourseSegments := []
    glossedTokens := [("Er", "he"), ("hämmerte", "hammered"), ("das", "the.ACC"), ("Metall", "metal"), ("platt", "flat")]
    translation := "He hammered the metal flat."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "transitive"), ("m_predicate", "hämmern"), ("r_predicate", "platt")]
    comment := "V2 order with the RSP in clause-final base position."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex89b : LinguisticExample :=
  { id := "benz2025_ex89b"
    source := ⟨"benz-2025", "(89b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er schießt seinen Gegner tot"
    discourseSegments := []
    glossedTokens := [("Er", "he"), ("schießt", "shoots"), ("seinen", "his.ACC"), ("Gegner", "opponent"), ("tot", "dead")]
    translation := "He shoots his opponent dead."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "transitive"), ("m_predicate", "schießen"), ("r_predicate", "tot")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex115a : LinguisticExample :=
  { id := "benz2025_ex115a"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115a)"⟩
    language := "stan1295"
    primaryText := "Hans hat den Stock kaputt gebrochen"
    discourseSegments := []
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("den", "the.ACC"), ("Stock", "stick"), ("kaputt", "broken"), ("gebrochen", "broken.PTCP")]
    translation := "Hans broke the stick."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "obligatorily transitive"), ("m_predicate", "brechen"), ("r_predicate", "kaputt")]
    comment := "An RSP is in fact obligatory on most uses of brechen ((116))."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex115e : LinguisticExample :=
  { id := "benz2025_ex115e"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115e)"⟩
    language := "stan1295"
    primaryText := "Das Wasser fror fest"
    discourseSegments := []
    glossedTokens := [("Das", "the.NOM"), ("Wasser", "water"), ("fror", "froze"), ("fest", "solid")]
    translation := "The water froze solid."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "unaccusative"), ("m_predicate", "frieren"), ("r_predicate", "fest")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex115f : LinguisticExample :=
  { id := "benz2025_ex115f"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115f)"⟩
    language := "stan1295"
    primaryText := "Sie haben sich krank/tot geschämt"
    discourseSegments := []
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("sich", "REFL"), ("krank/tot", "sick/dead"), ("geschämt", "shamed.PTCP")]
    translation := "They were embarrassed sick/dead."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "inherently reflexive"), ("m_predicate", "schämen"), ("r_predicate", "krank/tot")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex87ab : LinguisticExample :=
  { id := "benz2025_ex87ab"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87a-b)"⟩
    language := "stan1295"
    primaryText := "Sie haben uns arm geraubt"
    discourseSegments := []
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("uns", "us.ACC"), ("arm", "poor"), ("geraubt", "robbed.PTCP")]
    translation := "They robbed us poor."
    context := ""
    judgment := .acceptable
    alternatives := [("Sie haben uns arm be-raubt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "be-"), ("r_predicate", "arm")]
    comment := "The ge- of the grammatical form is participial, not a prefix in the relevant sense."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex87cd : LinguisticExample :=
  { id := "benz2025_ex87cd"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87c-d)"⟩
    language := "stan1295"
    primaryText := "Sie haben ihn tot geschossen"
    discourseSegments := []
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("ihn", "him.ACC"), ("tot", "dead"), ("geschossen", "shot.PTCP")]
    translation := "They shot him dead."
    context := ""
    judgment := .acceptable
    alternatives := [("Sie haben ihn tot er-schossen", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "er-"), ("r_predicate", "tot")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex87ef : LinguisticExample :=
  { id := "benz2025_ex87ef"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87e-f)"⟩
    language := "stan1295"
    primaryText := "Hans hat den Stock kaputt gebrochen"
    discourseSegments := []
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("den", "the.ACC"), ("Stock", "stick"), ("kaputt", "broken.ADJ"), ("gebrochen", "broken.PTCP")]
    translation := "Hans broke the stick broken."
    context := ""
    judgment := .acceptable
    alternatives := [("Hans hat den Stock kaputt zer-brochen", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "zer-"), ("r_predicate", "kaputt")]
    comment := "Same grammatical baseline as (115a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex88ab : LinguisticExample :=
  { id := "benz2025_ex88ab"
    source := ⟨"benz-2025", "(88a-b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat den Tisch trocken gewischt"
    discourseSegments := []
    glossedTokens := [("Sie", "she"), ("hat", "has"), ("den", "the.ACC"), ("Tisch", "table"), ("trocken", "dry"), ("gewischt", "wiped.PTCP")]
    translation := "She wiped the table dry."
    context := ""
    judgment := .acceptable
    alternatives := [("Sie hat den Tisch trocken ab-gewischt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "particle"), ("blocker", "ab-"), ("r_predicate", "trocken")]
    comment := "The starred form is grammatical only under an adverbial reading of trocken, not the intended resultative one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex88cd : LinguisticExample :=
  { id := "benz2025_ex88cd"
    source := ⟨"benz-2025", "(88c-d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Baby hat mich nass gespuckt"
    discourseSegments := []
    glossedTokens := [("Das", "the"), ("Baby", "baby"), ("hat", "has"), ("mich", "me.ACC"), ("nass", "wet"), ("gespuckt", "spit.PTCP")]
    translation := "The baby spat up on me."
    context := ""
    judgment := .acceptable
    alternatives := [("Das Baby hat mich nass an-gespuckt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "particle"), ("blocker", "an-"), ("r_predicate", "nass")]
    comment := "an- is not characterizable as a resultative particle, yet still blocks the RSP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex32a, ex32b, ex32c, ex89a, ex89b, ex115a, ex115e, ex115f, ex87ab, ex87cd, ex87ef, ex88ab, ex88cd]

end Benz2025.Examples
