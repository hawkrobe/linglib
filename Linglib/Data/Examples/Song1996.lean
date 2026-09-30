module

public import Linglib.Data.Examples.Schema

/-!
# `Song1996` — typed example data

Auto-generated from `Linglib/Data/Examples/Song1996.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Song1996.Examples`.
-/

@[expose] public section

namespace Song1996.Examples

open Data.Examples

def ex_1b : LinguisticExample :=
  { id := "song1996_1b"
    source := ⟨"song-1996", "(1.b), p. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The policewoman killed the terrorist."
    discourseSegments := []
    glossedTokens := []
    translation := "The policewoman killed the terrorist."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "fused")]
    comment := "The lexical causative: kill and the basic verb die of (1.a) share no form; the COMPACT type at maximal fusion (pp. 3, 9)." }

def ex_6 : LinguisticExample :=
  { id := "song1996_6"
    source := ⟨"song-1996", "(6), p. 12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The policewoman killed the terrorist, but he didn't die."
    discourseSegments := []
    glossedTokens := []
    translation := "The policewoman killed the terrorist, but he didn't die."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "fused"), ("effect", "negated")]
    comment := "Song's diagnostic of implicativity: kill entails the death of the terrorist, so its denial is contradictory (p. 12, citing Karttunen 1971a)." }

def ex_2b : LinguisticExample :=
  { id := "song1996_2b"
    source := ⟨"song-1996", "(2.b), p. 3"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali Hasan-ı öl-dür-dü"
    discourseSegments := []
    glossedTokens := [("Ali", "Ali"), ("Hasan-ı", "Hasan-DO"), ("öl-dür-dü", "die-CS-PST")]
    translation := "Ali killed Hasan."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound")]
    comment := "The morphological causative: the suffix -dür attached to the basic verb öl- 'die' of (2.a) (p. 3)." }

def ex_3b : LinguisticExample :=
  { id := "song1996_3b"
    source := ⟨"song-1996", "(3.b), p. 3"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka wus-ke ha-əss-ta"
    discourseSegments := []
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("wus-ke", "smile-COMP"), ("ha-əss-ta", "cause-PST-IND")]
    translation := "Keeho caused Jinee to smile."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "PURP"), ("order", "effect-cause")]
    comment := "Glossed COMP here after the traditional analysis of -ke as a complementizer; Song identifies it as purposive and glosses it PURP from (7) on (pp. 10, 12)." }

def ex_4a : LinguisticExample :=
  { id := "song1996_4a"
    source := ⟨"song-1996", "(4.a), p. 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako ga Ziroo o ik-ase-ta"
    discourseSegments := []
    glossedTokens := [("Hanako", "Hanako"), ("ga", "NOM"), ("Ziroo", "Ziroo"), ("o", "ACC"), ("ik-ase-ta", "go-CS-PST")]
    translation := "Hanako made Ziroo go."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound")]
    comment := "The morphological causative in -ase, the causee in the accusative; the dative version (4.b) is 'Hanako got Ziroo to go' (pp. 5, 9)." }

def ex_5 : LinguisticExample :=
  { id := "song1996_5"
    source := ⟨"song-1996", "(5), p. 10"⟩
    reportedIn := none
    language := "lako1244"
    primaryText := "ǹ gbā le yÒ-Ò lī"
    discourseSegments := []
    glossedTokens := [("ǹ", "I"), ("gbā", "speak"), ("le", "CONJ"), ("yÒ-Ò", "child-DEF"), ("lī", "eat")]
    translation := "I make the child eat."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "AND"), ("order", "cause-effect")]
    comment := "The AND type: the clause of cause and the clause of effect coordinated by le, in that order; Song's source is Koopman (1984: 24-25) (pp. 10, 36). The glottocode is WALS's for Koopman's Vata." }

def ex_7 : LinguisticExample :=
  { id := "song1996_7"
    source := ⟨"song-1996", "(7), p. 13"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka wus-ke ha-əss-ɨna cini-ka wus-ci=an-əss-ta"
    discourseSegments := []
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("wus-ke", "smile-PURP"), ("ha-əss-ɨna", "cause-PST-but"), ("cini-ka", "Jinee-NOM"), ("wus-ci=an-əss-ta", "smile-NEG-PST-IND")]
    translation := "Keeho caused Jinee to smile, but she didn't smile."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("effect", "negated")]
    comment := "The PURP causative of (3.b) with its effect denied: fully grammatical, so the prototypical PURP type is nonimplicative (pp. 12-13)." }

def ex_24 : LinguisticExample :=
  { id := "song1996_24"
    source := ⟨"song-1996", "(24), p. 33"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je ferai lire le livre à Nicole"
    discourseSegments := []
    glossedTokens := [("Je", "I"), ("ferai", "make + FUT"), ("lire", "read"), ("le", "the"), ("livre", "book (ACC)"), ("à", "DAT"), ("Nicole", "Nicole")]
    translation := "I'll make Nicole read the book."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "free")]
    comment := "The COMPACT type with [Vcause] a free morpheme: faire and the verb of effect adjacent (§2.3.2). Song glosses à Nicole jointly as 'Nicole (DAT)'." }

def ex_104 : LinguisticExample :=
  { id := "song1996_104"
    source := ⟨"song-1996", "(104), p. 68"⟩
    reportedIn := none
    language := "khmu1256"
    primaryText := "kə̀ə p-ŋ̀mɔ́ɔŋ nàa, nàa pə́ə mɔ́ɔŋ"
    discourseSegments := []
    glossedTokens := [("kə̀ə", "he"), ("p-ŋ̀mɔ́ɔŋ", "CP-sad"), ("nàa,", "she"), ("nàa", "she"), ("pə́ə", "not"), ("mɔ́ɔŋ", "sad")]
    translation := "He tried to make her sad, but she didn't become sad."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound"), ("effect", "negated")]
    comment := "A COMPACT causative in p- that is fully nonimplicative; Song's source is Svantesson (1983: 106), and the translation's 'tried' is added because the literal one is ungrammatical in English (p. 68, note 21; repeated as (35.a), p. 103)." }

def all : List LinguisticExample := [ex_1b, ex_6, ex_2b, ex_3b, ex_4a, ex_5, ex_7, ex_24, ex_104]

end Song1996.Examples
