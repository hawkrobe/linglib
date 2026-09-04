import Linglib.Data.Examples.Schema

/-!
# `ColeHermon2008` — typed example data

Auto-generated from `Linglib/Data/Examples/ColeHermon2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ColeHermon2008.Examples`.
-/

namespace ColeHermon2008.Examples

open Data.Examples

def ex7a : LinguisticExample :=
  { id := "colehermon2008_ex7a"
    source := ⟨"cole-hermon-2008", "(7a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Aha si-John mang-alean tu si-Mary?"
    discourseSegments := []
    glossedTokens := [("Aha", "what"), ("si-John", "hon-John"), ("mang-alean", "act-give"), ("tu", "to"), ("si-Mary", "hon-Mary")]
    translation := "What did John give to Mary?"
    context := "The wh-object of an active ditransitive fronted; the subject precedes the verb."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "SVO"), ("transitivity", "ditransitive"), ("extracted", "patient"), ("wh", "fronted")]
    comment := "Repeated as (86) in the argument for the VOS Hypothesis."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7b : LinguisticExample :=
  { id := "colehermon2008_ex7b"
    source := ⟨"cole-hermon-2008", "(7b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-allang aha do dakdanak-i?"
    discourseSegments := []
    glossedTokens := [("Mang-allang", "act-eat"), ("aha", "what"), ("do", "foc"), ("dakdanak-i", "child-def")]
    translation := "What did the child eat?"
    context := "The wh-object of an active clause in situ, immediately after the verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "monotransitive"), ("extracted", "patient"), ("wh", "inSitu")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8a : LinguisticExample :=
  { id := "colehermon2008_ex8a"
    source := ⟨"cole-hermon-2008", "(8a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Ise di-lean buku tu si-Mary?"
    discourseSegments := []
    glossedTokens := [("Ise", "who"), ("di-lean", "pass-give"), ("buku", "book"), ("tu", "to"), ("si-Mary", "hon-Mary")]
    translation := "Who was a book given to Mary by?"
    context := "The wh-agent of a passive ditransitive fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "agent"), ("wh", "fronted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8b : LinguisticExample :=
  { id := "colehermon2008_ex8b"
    source := ⟨"cole-hermon-2008", "(8b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-lean ise do tu si-Mary sada bunga?"
    discourseSegments := []
    glossedTokens := [("Di-lean", "pass-give"), ("ise", "who"), ("do", "foc"), ("tu", "to"), ("si-Mary", "hon-Mary"), ("sada", "some"), ("bunga", "flower")]
    translation := "Who were some flowers given to Mary by?"
    context := "The wh-agent of a passive ditransitive in situ, immediately after the verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "agent"), ("wh", "inSitu")]
    comment := "The goal precedes the pivot: the marked V-Ag-IO-S order of (14)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9 : LinguisticExample :=
  { id := "colehermon2008_ex9"
    source := ⟨"cole-hermon-2008", "(9)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Tu ise mang-alean buku si-John?"
    discourseSegments := []
    glossedTokens := [("Tu", "to"), ("ise", "who"), ("mang-alean", "act-give"), ("buku", "book"), ("si-John", "hon-John")]
    translation := "To whom did John give a book?"
    context := "The wh-goal PP of an active ditransitive fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "goal"), ("wh", "fronted")]
    comment := "Repeated as (45)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10 : LinguisticExample :=
  { id := "colehermon2008_ex10"
    source := ⟨"cole-hermon-2008", "(10)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Tu ise do di-lean si-John buku?"
    discourseSegments := []
    glossedTokens := [("Tu", "to"), ("ise", "who"), ("do", "foc"), ("di-lean", "pass-give"), ("si-John", "hon-John"), ("buku", "book")]
    translation := "To whom was the book given by John?"
    context := "The wh-goal PP of a passive ditransitive fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "goal"), ("wh", "fronted")]
    comment := "Repeated as (46)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17 : LinguisticExample :=
  { id := "colehermon2008_ex17"
    source := ⟨"cole-hermon-2008", "(17)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-Bunga mang-ida dirina sandiri."
    discourseSegments := []
    glossedTokens := [("Si-Bunga", "hon-Bunga"), ("mang-ida", "act-see"), ("dirina sandiri", "herself")]
    translation := "Bunga saw herself."
    context := "Active clause in SVO order; the subject antecedes a reflexive direct object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "SVO"), ("antecedent", "agent"), ("reflexive", "patient"), ("tableOne", "A")]
    comment := "Table 1, Type A: fully acceptable for all speakers."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21 : LinguisticExample :=
  { id := "colehermon2008_ex21"
    source := ⟨"cole-hermon-2008", "(21)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dirina sandiri pa-ias-hon dakdanak-i."
    discourseSegments := []
    glossedTokens := [("Dirina sandiri", "self"), ("pa-ias-hon", "make-clean-caus"), ("dakdanak-i", "child-def")]
    translation := "Himself cleaned the child."
    context := "Active clause in SVO order; the direct object would antecede a reflexive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "SVO"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "C")]
    comment := "Table 1, Type C: not acceptable for any speakers. The active prefix is null on this verb (fn. 5)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex37 : LinguisticExample :=
  { id := "colehermon2008_ex37"
    source := ⟨"cole-hermon-2008", "(37)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-Bunga di-ida dirina sandiri."
    discourseSegments := []
    glossedTokens := [("Si-Bunga", "hon-Bunga"), ("di-ida", "pass-see"), ("dirina sandiri", "self")]
    translation := "Bunga was seen by herself."
    context := "Passive clause in SVO order; the passive subject antecedes a reflexive passive agent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("order", "SVO"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "B")]
    comment := "Table 1, Type B: acceptable, not the most usual way to express the sentence; marked ungrammatical by Schachter and Sugamoto."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex43 : LinguisticExample :=
  { id := "colehermon2008_ex43"
    source := ⟨"cole-hermon-2008", "(43)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Aha mang-atuk si-John?"
    discourseSegments := []
    glossedTokens := [("Aha", "what"), ("mang-atuk", "act-hit"), ("si-John", "hon-John")]
    translation := "What did John hit?"
    context := "The wh-object of an active monotransitive fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "monotransitive"), ("extracted", "patient"), ("wh", "fronted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44 : LinguisticExample :=
  { id := "colehermon2008_ex44"
    source := ⟨"cole-hermon-2008", "(44)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-atuk aha si-John?"
    discourseSegments := []
    glossedTokens := [("Mang-atuk", "act-hit"), ("aha", "what"), ("si-John", "hon-John")]
    translation := "What did John hit?"
    context := "The wh-object of an active monotransitive in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "monotransitive"), ("extracted", "patient"), ("wh", "inSitu")]
    comment := "The paper's gloss line reads act-see; the translation and (43) have 'hit'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex62 : LinguisticExample :=
  { id := "colehermon2008_ex62"
    source := ⟨"cole-hermon-2008", "(62)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-ida dirina sandiri si-Bunga."
    discourseSegments := []
    glossedTokens := [("Mang-ida", "act-see"), ("dirina sandiri", "herself"), ("si-Bunga", "hon-Bunga")]
    translation := "Bunga saw herself."
    context := "Active clause in VOS order; the subject antecedes a reflexive direct object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "VOS"), ("antecedent", "agent"), ("reflexive", "patient"), ("tableOne", "A")]
    comment := "Derived in (63)–(65)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex66 : LinguisticExample :=
  { id := "colehermon2008_ex66"
    source := ⟨"cole-hermon-2008", "(66)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dirina sandiri mang-ida si-Bunga."
    discourseSegments := []
    glossedTokens := [("Dirina sandiri", "herself"), ("mang-ida", "act-see"), ("si-Bunga", "hon-Bunga")]
    translation := "Herself saw si Bunga."
    context := "Active clause in SVO order; the direct object would antecede a reflexive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "SVO"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "C")]
    comment := "A Condition A violation, not the apparent Condition C violation (fn. 29)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex67 : LinguisticExample :=
  { id := "colehermon2008_ex67"
    source := ⟨"cole-hermon-2008", "(67)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-ida si-Torus dirina sandiri."
    discourseSegments := []
    glossedTokens := [("Di-ida", "pass-see"), ("si-Torus", "hon-Torus"), ("dirina sandiri", "himself")]
    translation := "Himself was seen by Torus."
    context := "Passive clause in VOS order; the passive agent antecedes a reflexive passive subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("order", "VOS"), ("antecedent", "agent"), ("reflexive", "patient"), ("tableOne", "A")]
    comment := "(27) and (36) in simplified form; derived in (72)–(74). The two reflexive forms do not differ here (fn. 30)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex68 : LinguisticExample :=
  { id := "colehermon2008_ex68"
    source := ⟨"cole-hermon-2008", "(68)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-ida dirina sandiri si-John."
    discourseSegments := []
    glossedTokens := [("Di-ida", "pass-see"), ("dirina sandiri", "self"), ("si-John", "hon-John")]
    translation := "John was seen by himself."
    context := "Passive clause in VOS order; the passive subject antecedes a reflexive passive agent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("order", "VOS"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "B")]
    comment := "(38) in simplified form; derived in (75)–(77). Table 1, Type B."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex85 : LinguisticExample :=
  { id := "colehermon2008_ex85"
    source := ⟨"cole-hermon-2008", "(85)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-John mang-alean aha tu si-Mary?"
    discourseSegments := []
    glossedTokens := [("Si-John", "hon-John"), ("mang-alean", "act-give"), ("aha", "what"), ("tu", "to"), ("si-Mary", "hon-Mary")]
    translation := "What did John give to Mary?"
    context := "The wh-object of an active ditransitive in SVO order in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "SVO"), ("transitivity", "ditransitive"), ("extracted", "patient"), ("wh", "inSitu")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex87 : LinguisticExample :=
  { id := "colehermon2008_ex87"
    source := ⟨"cole-hermon-2008", "(87)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Biang-i di-atuk ise?"
    discourseSegments := []
    glossedTokens := [("Biang-i", "dog-def"), ("di-atuk", "pass-hit"), ("ise", "who")]
    translation := "Who was the dog hit by?"
    context := "The wh-agent of a passive clause in SVO order in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "SVO"), ("transitivity", "monotransitive"), ("extracted", "agent"), ("wh", "inSitu")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex88 : LinguisticExample :=
  { id := "colehermon2008_ex88"
    source := ⟨"cole-hermon-2008", "(88)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Ise biang-i di-atuk?"
    discourseSegments := []
    glossedTokens := [("Ise", "who"), ("biang-i", "dog-def"), ("di-atuk", "pass-hit")]
    translation := "Who was the dog hit by?"
    context := "The wh-agent of a passive clause in SVO order fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "SVO"), ("transitivity", "monotransitive"), ("extracted", "agent"), ("wh", "fronted")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex95 : LinguisticExample :=
  { id := "colehermon2008_ex95"
    source := ⟨"cole-hermon-2008", "(95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The findings of the court were that the boy was injured by himself, and not by someone else."
    discourseSegments := []
    glossedTokens := []
    translation := "The findings of the court were that the boy was injured by himself, and not by someone else."
    context := "English passive; the passive subject antecedes a reflexive in the by-phrase."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("antecedent", "patient"), ("reflexive", "agent")]
    comment := "Repeats (25); derived in (97)–(98)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex96 : LinguisticExample :=
  { id := "colehermon2008_ex96"
    source := ⟨"cole-hermon-2008", "(96)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The findings of the court were that himself was injured by the boy, and not by someone else."
    discourseSegments := []
    glossedTokens := []
    translation := "The findings of the court were that himself was injured by the boy, and not by someone else."
    context := "English passive; the by-phrase agent would antecede a reflexive passive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("antecedent", "agent"), ("reflexive", "patient")]
    comment := "Repeats (26); derived in (99)–(100)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex7a, ex7b, ex8a, ex8b, ex9, ex10, ex17, ex21, ex37, ex43, ex44, ex62, ex66, ex67, ex68, ex85, ex87, ex88, ex95, ex96]

end ColeHermon2008.Examples
