module

public import Linglib.Data.Examples.Schema

/-!
# `ColeHermon2008` — typed example data

Auto-generated from `Linglib/Data/Examples/ColeHermon2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ColeHermon2008.Examples`.
-/

@[expose] public section

namespace ColeHermon2008.Examples

def ex7a : Datum :=
  { id := "colehermon2008_ex7a"
    source := ⟨"cole-hermon-2008", "(7a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Aha si-John mang-alean tu si-Mary?"
    glossedTokens := [("Aha", "what"), ("si-John", "hon-John"), ("mang-alean", "act-give"), ("tu", "to"), ("si-Mary", "hon-Mary")]
    context := "The wh-object of an active ditransitive fronted; the subject precedes the verb."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "SVO"), ("transitivity", "ditransitive"), ("extracted", "patient"), ("wh", "fronted")] }

def ex7b : Datum :=
  { id := "colehermon2008_ex7b"
    source := ⟨"cole-hermon-2008", "(7b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-allang aha do dakdanak-i?"
    glossedTokens := [("Mang-allang", "act-eat"), ("aha", "what"), ("do", "foc"), ("dakdanak-i", "child-def")]
    context := "The wh-object of an active clause in situ, immediately after the verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "monotransitive"), ("extracted", "patient"), ("wh", "inSitu")] }

def ex8a : Datum :=
  { id := "colehermon2008_ex8a"
    source := ⟨"cole-hermon-2008", "(8a)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Ise di-lean buku tu si-Mary?"
    glossedTokens := [("Ise", "who"), ("di-lean", "pass-give"), ("buku", "book"), ("tu", "to"), ("si-Mary", "hon-Mary")]
    context := "The wh-agent of a passive ditransitive fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "agent"), ("wh", "fronted")] }

def ex8b : Datum :=
  { id := "colehermon2008_ex8b"
    source := ⟨"cole-hermon-2008", "(8b)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-lean ise do tu si-Mary sada bunga?"
    glossedTokens := [("Di-lean", "pass-give"), ("ise", "who"), ("do", "foc"), ("tu", "to"), ("si-Mary", "hon-Mary"), ("sada", "some"), ("bunga", "flower")]
    context := "The wh-agent of a passive ditransitive in situ, immediately after the verb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "agent"), ("wh", "inSitu")] }

def ex9 : Datum :=
  { id := "colehermon2008_ex9"
    source := ⟨"cole-hermon-2008", "(9)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Tu ise mang-alean buku si-John?"
    glossedTokens := [("Tu", "to"), ("ise", "who"), ("mang-alean", "act-give"), ("buku", "book"), ("si-John", "hon-John")]
    context := "The wh-goal PP of an active ditransitive fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "goal"), ("wh", "fronted")] }

def ex10 : Datum :=
  { id := "colehermon2008_ex10"
    source := ⟨"cole-hermon-2008", "(10)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Tu ise do di-lean si-John buku?"
    glossedTokens := [("Tu", "to"), ("ise", "who"), ("do", "foc"), ("di-lean", "pass-give"), ("si-John", "hon-John"), ("buku", "book")]
    context := "The wh-goal PP of a passive ditransitive fronted."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "VOS"), ("transitivity", "ditransitive"), ("extracted", "goal"), ("wh", "fronted")] }

def ex17 : Datum :=
  { id := "colehermon2008_ex17"
    source := ⟨"cole-hermon-2008", "(17)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-Bunga mang-ida dirina sandiri."
    glossedTokens := [("Si-Bunga", "hon-Bunga"), ("mang-ida", "act-see"), ("dirina sandiri", "herself")]
    context := "Active clause in SVO order; the subject antecedes a reflexive direct object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "SVO"), ("antecedent", "agent"), ("reflexive", "patient"), ("tableOne", "A")] }

def ex21 : Datum :=
  { id := "colehermon2008_ex21"
    source := ⟨"cole-hermon-2008", "(21)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dirina sandiri pa-ias-hon dakdanak-i."
    glossedTokens := [("Dirina sandiri", "self"), ("pa-ias-hon", "make-clean-caus"), ("dakdanak-i", "child-def")]
    context := "Active clause in SVO order; the direct object would antecede a reflexive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "SVO"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "C")] }

def ex37 : Datum :=
  { id := "colehermon2008_ex37"
    source := ⟨"cole-hermon-2008", "(37)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-Bunga di-ida dirina sandiri."
    glossedTokens := [("Si-Bunga", "hon-Bunga"), ("di-ida", "pass-see"), ("dirina sandiri", "self")]
    context := "Passive clause in SVO order; the passive subject antecedes a reflexive passive agent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("order", "SVO"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "B")] }

def ex43 : Datum :=
  { id := "colehermon2008_ex43"
    source := ⟨"cole-hermon-2008", "(43)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Aha mang-atuk si-John?"
    glossedTokens := [("Aha", "what"), ("mang-atuk", "act-hit"), ("si-John", "hon-John")]
    context := "The wh-object of an active monotransitive fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "monotransitive"), ("extracted", "patient"), ("wh", "fronted")] }

def ex44 : Datum :=
  { id := "colehermon2008_ex44"
    source := ⟨"cole-hermon-2008", "(44)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-atuk aha si-John?"
    glossedTokens := [("Mang-atuk", "act-hit"), ("aha", "what"), ("si-John", "hon-John")]
    context := "The wh-object of an active monotransitive in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "VOS"), ("transitivity", "monotransitive"), ("extracted", "patient"), ("wh", "inSitu")] }

def ex62 : Datum :=
  { id := "colehermon2008_ex62"
    source := ⟨"cole-hermon-2008", "(62)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Mang-ida dirina sandiri si-Bunga."
    glossedTokens := [("Mang-ida", "act-see"), ("dirina sandiri", "herself"), ("si-Bunga", "hon-Bunga")]
    context := "Active clause in VOS order; the subject antecedes a reflexive direct object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "VOS"), ("antecedent", "agent"), ("reflexive", "patient"), ("tableOne", "A")] }

def ex66 : Datum :=
  { id := "colehermon2008_ex66"
    source := ⟨"cole-hermon-2008", "(66)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Dirina sandiri mang-ida si-Bunga."
    glossedTokens := [("Dirina sandiri", "herself"), ("mang-ida", "act-see"), ("si-Bunga", "hon-Bunga")]
    context := "Active clause in SVO order; the direct object would antecede a reflexive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "active"), ("order", "SVO"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "C")] }

def ex67 : Datum :=
  { id := "colehermon2008_ex67"
    source := ⟨"cole-hermon-2008", "(67)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-ida si-Torus dirina sandiri."
    glossedTokens := [("Di-ida", "pass-see"), ("si-Torus", "hon-Torus"), ("dirina sandiri", "himself")]
    context := "Passive clause in VOS order; the passive agent antecedes a reflexive passive subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("order", "VOS"), ("antecedent", "agent"), ("reflexive", "patient"), ("tableOne", "A")] }

def ex68 : Datum :=
  { id := "colehermon2008_ex68"
    source := ⟨"cole-hermon-2008", "(68)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Di-ida dirina sandiri si-John."
    glossedTokens := [("Di-ida", "pass-see"), ("dirina sandiri", "self"), ("si-John", "hon-John")]
    context := "Passive clause in VOS order; the passive subject antecedes a reflexive passive agent."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("order", "VOS"), ("antecedent", "patient"), ("reflexive", "agent"), ("tableOne", "B")] }

def ex85 : Datum :=
  { id := "colehermon2008_ex85"
    source := ⟨"cole-hermon-2008", "(85)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Si-John mang-alean aha tu si-Mary?"
    glossedTokens := [("Si-John", "hon-John"), ("mang-alean", "act-give"), ("aha", "what"), ("tu", "to"), ("si-Mary", "hon-Mary")]
    context := "The wh-object of an active ditransitive in SVO order in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "active"), ("order", "SVO"), ("transitivity", "ditransitive"), ("extracted", "patient"), ("wh", "inSitu")] }

def ex87 : Datum :=
  { id := "colehermon2008_ex87"
    source := ⟨"cole-hermon-2008", "(87)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Biang-i di-atuk ise?"
    glossedTokens := [("Biang-i", "dog-def"), ("di-atuk", "pass-hit"), ("ise", "who")]
    context := "The wh-agent of a passive clause in SVO order in situ."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "SVO"), ("transitivity", "monotransitive"), ("extracted", "agent"), ("wh", "inSitu")] }

def ex88 : Datum :=
  { id := "colehermon2008_ex88"
    source := ⟨"cole-hermon-2008", "(88)"⟩
    reportedIn := none
    language := "bata1289"
    primaryText := "Ise biang-i di-atuk?"
    glossedTokens := [("Ise", "who"), ("biang-i", "dog-def"), ("di-atuk", "pass-hit")]
    context := "The wh-agent of a passive clause in SVO order fronted."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "extraction"), ("voice", "passive"), ("order", "SVO"), ("transitivity", "monotransitive"), ("extracted", "agent"), ("wh", "fronted")] }

def ex95 : Datum :=
  { id := "colehermon2008_ex95"
    source := ⟨"cole-hermon-2008", "(95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The findings of the court were that the boy was injured by himself, and not by someone else."
    glossedTokens := []
    context := "English passive; the passive subject antecedes a reflexive in the by-phrase."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("antecedent", "patient"), ("reflexive", "agent")] }

def ex96 : Datum :=
  { id := "colehermon2008_ex96"
    source := ⟨"cole-hermon-2008", "(96)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The findings of the court were that himself was injured by the boy, and not by someone else."
    glossedTokens := []
    context := "English passive; the by-phrase agent would antecede a reflexive passive subject."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "binding"), ("voice", "passive"), ("antecedent", "agent"), ("reflexive", "patient")] }

def all : List Datum := [ex7a, ex7b, ex8a, ex8b, ex9, ex10, ex17, ex21, ex37, ex43, ex44, ex62, ex66, ex67, ex68, ex85, ex87, ex88, ex95, ex96]

end ColeHermon2008.Examples
