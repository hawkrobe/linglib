module

public import Linglib.Data.Examples.Schema

/-!
# `Benz2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Benz2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Benz2025.Examples`.
-/

@[expose] public section

namespace Benz2025.Examples

open Data.Examples

def ex32a : LinguisticExample :=
  { id := "benz2025_ex32a"
    source := ⟨"benz-2025", "(32a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Beobachtung des Nachthimmels dauerte drei Stunden"
    glossedTokens := [("Die", "the"), ("Beobacht-ung", "observe-NMLZ"), ("des", "the.GEN"), ("Nachthimmels", "night.sky"), ("dauerte", "took"), ("drei", "three"), ("Stunden", "hours")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "Event"), ("duration_predicate", "yes"), ("plural", "no"), ("cp_complement", "no")] }

def ex32b : LinguisticExample :=
  { id := "benz2025_ex32b"
    source := ⟨"benz-2025", "(32b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Die Beobachtungen der Astronomin sind für immer verloren"
    glossedTokens := [("Die", "the"), ("Beobacht-ung-en", "observe-NMLZ-PL"), ("der", "the.GEN"), ("Astronomin", "astronomer"), ("sind", "are"), ("für", "for"), ("immer", "ever"), ("verloren", "lost")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("concrete object", .acceptable), ("result", .acceptable), ("content", .acceptable)]
    paperFeatures := [("reading", "RN"), ("duration_predicate", "no"), ("plural", "yes"), ("cp_complement", "no")] }

def ex32c : LinguisticExample :=
  { id := "benz2025_ex32c"
    source := ⟨"benz-2025", "(32c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Seine Beobachtung, dass Planeten sich bewegen, veränderte die Wissenschaft"
    glossedTokens := [("Seine", "his"), ("Beobacht-ung", "observe-NMLZ"), ("dass", "COMP"), ("Planeten", "planets"), ("sich", "REFL"), ("bewegen", "move"), ("veränderte", "changed"), ("die", "the"), ("Wissenschaft", "science")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("reading", "Content"), ("duration_predicate", "no"), ("plural", "no"), ("cp_complement", "yes")] }

def ex89a : LinguisticExample :=
  { id := "benz2025_ex89a"
    source := ⟨"benz-2025", "(89a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er hämmerte das Metall platt"
    glossedTokens := [("Er", "he"), ("hämmerte", "hammered"), ("das", "the.ACC"), ("Metall", "metal"), ("platt", "flat")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "transitive"), ("m_predicate", "hämmern"), ("r_predicate", "platt")] }

def ex89b : LinguisticExample :=
  { id := "benz2025_ex89b"
    source := ⟨"benz-2025", "(89b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Er schießt seinen Gegner tot"
    glossedTokens := [("Er", "he"), ("schießt", "shoots"), ("seinen", "his.ACC"), ("Gegner", "opponent"), ("tot", "dead")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "transitive"), ("m_predicate", "schießen"), ("r_predicate", "tot")] }

def ex115a : LinguisticExample :=
  { id := "benz2025_ex115a"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115a)"⟩
    language := "stan1295"
    primaryText := "Hans hat den Stock kaputt gebrochen"
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("den", "the.ACC"), ("Stock", "stick"), ("kaputt", "broken"), ("gebrochen", "broken.PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "obligatorily transitive"), ("m_predicate", "brechen"), ("r_predicate", "kaputt")] }

def ex115e : LinguisticExample :=
  { id := "benz2025_ex115e"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115e)"⟩
    language := "stan1295"
    primaryText := "Das Wasser fror fest"
    glossedTokens := [("Das", "the.NOM"), ("Wasser", "water"), ("fror", "froze"), ("fest", "solid")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "unaccusative"), ("m_predicate", "frieren"), ("r_predicate", "fest")] }

def ex115f : LinguisticExample :=
  { id := "benz2025_ex115f"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(115f)"⟩
    language := "stan1295"
    primaryText := "Sie haben sich krank/tot geschämt"
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("sich", "REFL"), ("krank/tot", "sick/dead"), ("geschämt", "shamed.PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "inherently reflexive"), ("m_predicate", "schämen"), ("r_predicate", "krank/tot")] }

def ex87ab : LinguisticExample :=
  { id := "benz2025_ex87ab"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87a-b)"⟩
    language := "stan1295"
    primaryText := "Sie haben uns arm geraubt"
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("uns", "us.ACC"), ("arm", "poor"), ("geraubt", "robbed.PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := [("Sie haben uns arm be-raubt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "be-"), ("r_predicate", "arm"), ("outer", "rsp"), ("inner", "pfx")] }

def ex87cd : LinguisticExample :=
  { id := "benz2025_ex87cd"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87c-d)"⟩
    language := "stan1295"
    primaryText := "Sie haben ihn tot geschossen"
    glossedTokens := [("Sie", "they"), ("haben", "have"), ("ihn", "him.ACC"), ("tot", "dead"), ("geschossen", "shot.PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := [("Sie haben ihn tot er-schossen", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "er-"), ("r_predicate", "tot"), ("outer", "rsp"), ("inner", "pfx")] }

def ex87ef : LinguisticExample :=
  { id := "benz2025_ex87ef"
    source := ⟨"creemers-2020", ""⟩
    reportedIn := some ⟨"benz-2025", "(87e-f)"⟩
    language := "stan1295"
    primaryText := "Hans hat den Stock kaputt gebrochen"
    glossedTokens := [("Hans", "Hans"), ("hat", "has"), ("den", "the.ACC"), ("Stock", "stick"), ("kaputt", "broken.ADJ"), ("gebrochen", "broken.PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := [("Hans hat den Stock kaputt zer-brochen", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "prefix"), ("blocker", "zer-"), ("r_predicate", "kaputt"), ("outer", "rsp"), ("inner", "pfx")] }

def ex88ab : LinguisticExample :=
  { id := "benz2025_ex88ab"
    source := ⟨"benz-2025", "(88a-b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat den Tisch trocken gewischt"
    glossedTokens := [("Sie", "she"), ("hat", "has"), ("den", "the.ACC"), ("Tisch", "table"), ("trocken", "dry"), ("gewischt", "wiped.PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := [("Sie hat den Tisch trocken ab-gewischt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "particle"), ("blocker", "ab-"), ("r_predicate", "trocken"), ("outer", "rsp"), ("inner", "prt")] }

def ex88cd : LinguisticExample :=
  { id := "benz2025_ex88cd"
    source := ⟨"benz-2025", "(88c-d)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Baby hat mich nass gespuckt"
    glossedTokens := [("Das", "the"), ("Baby", "baby"), ("hat", "has"), ("mich", "me.ACC"), ("nass", "wet"), ("gespuckt", "spit.PTCP")]
    context := ""
    judgment := .acceptable
    alternatives := [("Das Baby hat mich nass an-gespuckt", .ungrammatical)]
    readings := []
    paperFeatures := [("blocker_type", "particle"), ("blocker", "an-"), ("r_predicate", "nass"), ("outer", "rsp"), ("inner", "prt")] }

def ex81a : LinguisticExample :=
  { id := "benz2025_ex81a"
    source := ⟨"benz-2025", "(81a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "ent-ver-trauen"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("outer", "pfx"), ("inner", "pfx")] }

def ex82a : LinguisticExample :=
  { id := "benz2025_ex82a"
    source := ⟨"benz-2025", "(82a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "rad-ein-fahren"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("outer", "prt"), ("inner", "prt")] }

def ex83a : LinguisticExample :=
  { id := "benz2025_ex83a"
    source := ⟨"benz-2025", "(83a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "zer-ab-schneiden"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("outer", "pfx"), ("inner", "prt")] }

def ex84a : LinguisticExample :=
  { id := "benz2025_ex84a"
    source := ⟨"benz-2025", "(84a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "aus-er-wählen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("outer", "prt"), ("inner", "pfx")] }

def ex86b : LinguisticExample :=
  { id := "benz2025_ex86b"
    source := ⟨"benz-2025", "(86b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Sie hat sich kaputt müde gearbeitet"
    glossedTokens := [("Sie", "she"), ("hat", "has"), ("sich", "REFL"), ("kaputt", "broken"), ("müde", "tired"), ("gearbeitet", "worked.PTCP")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("outer", "rsp"), ("inner", "rsp")] }

def ex193a : LinguisticExample :=
  { id := "benz2025_ex193a"
    source := ⟨"benz-2025", "(193a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Ver-kaufen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "infinitive"), ("element", "pfx"), ("verb", "verkaufen")] }

def ex193b : LinguisticExample :=
  { id := "benz2025_ex193b"
    source := ⟨"benz-2025", "(193b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Ein-führen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "infinitive"), ("element", "prt"), ("verb", "einführen")] }

def ex193c : LinguisticExample :=
  { id := "benz2025_ex193c"
    source := ⟨"benz-2025", "(193c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Wach-küssen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "infinitive"), ("element", "rsp"), ("verb", "küssen")] }

def ex197a : LinguisticExample :=
  { id := "benz2025_ex197a"
    source := ⟨"benz-2025", "(197a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ein-führ-ung"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "prt"), ("verb", "einführen")] }

def ex198c : LinguisticExample :=
  { id := "benz2025_ex198c"
    source := ⟨"benz-2025", "(198c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Be-mal-ung"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "pfx"), ("verb", "bemalen")] }

def ex198c_base : LinguisticExample :=
  { id := "benz2025_ex198c_base"
    source := ⟨"benz-2025", "(198c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Mal-ung"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "none"), ("verb", "malen")] }

def ex204a : LinguisticExample :=
  { id := "benz2025_ex204a"
    source := ⟨"benz-2025", "(204a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Platt-hämmer-ung"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "rsp"), ("verb", "hämmern")] }

def ex204c : LinguisticExample :=
  { id := "benz2025_ex204c"
    source := ⟨"benz-2025", "(204c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wach-küss-ung"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "ung"), ("element", "rsp"), ("verb", "küssen")] }

def ex212a : LinguisticExample :=
  { id := "benz2025_ex212a"
    source := ⟨"benz-2025", "(212a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Herum-ge-renn-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "prt"), ("verb", "rennen")] }

def ex216a : LinguisticExample :=
  { id := "benz2025_ex216a"
    source := ⟨"benz-2025", "(216a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Wach-ge-küss-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "rsp"), ("verb", "küssen")] }

def ex216b : LinguisticExample :=
  { id := "benz2025_ex216b"
    source := ⟨"benz-2025", "(216b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "das Platt-ge-hämmer-e"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "rsp"), ("verb", "hämmern")] }

def ex218c : LinguisticExample :=
  { id := "benz2025_ex218c"
    source := ⟨"benz-2025", "(218c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Ge-be-mal-e"
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("nominalization", "geE"), ("element", "pfx"), ("verb", "bemalen")] }

def all : List LinguisticExample := [ex32a, ex32b, ex32c, ex89a, ex89b, ex115a, ex115e, ex115f, ex87ab, ex87cd, ex87ef, ex88ab, ex88cd, ex81a, ex82a, ex83a, ex84a, ex86b, ex193a, ex193b, ex193c, ex197a, ex198c, ex198c_base, ex204a, ex204c, ex212a, ex216a, ex216b, ex218c]

end Benz2025.Examples
