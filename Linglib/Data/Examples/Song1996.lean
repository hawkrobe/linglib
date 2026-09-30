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

def ex_1b : Datum :=
  { id := "song1996_1b"
    source := ⟨"song-1996", "(1.b), p. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The policewoman killed the terrorist."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "fused")] }

def ex_6 : Datum :=
  { id := "song1996_6"
    source := ⟨"song-1996", "(6), p. 12"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The policewoman killed the terrorist, but he didn't die."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "fused"), ("effect", "negated")] }

def ex_2b : Datum :=
  { id := "song1996_2b"
    source := ⟨"song-1996", "(2.b), p. 3"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali Hasan-ı öl-dür-dü"
    glossedTokens := [("Ali", "Ali"), ("Hasan-ı", "Hasan-DO"), ("öl-dür-dü", "die-CS-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound")] }

def ex_3b : Datum :=
  { id := "song1996_3b"
    source := ⟨"song-1996", "(3.b), p. 3"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka wus-ke ha-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("wus-ke", "smile-COMP"), ("ha-əss-ta", "cause-PST-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "PURP"), ("order", "effect-cause")] }

def ex_4a : Datum :=
  { id := "song1996_4a"
    source := ⟨"song-1996", "(4.a), p. 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako ga Ziroo o ik-ase-ta"
    glossedTokens := [("Hanako", "Hanako"), ("ga", "NOM"), ("Ziroo", "Ziroo"), ("o", "ACC"), ("ik-ase-ta", "go-CS-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound")] }

def ex_5 : Datum :=
  { id := "song1996_5"
    source := ⟨"song-1996", "(5), p. 10"⟩
    reportedIn := none
    language := "lako1244"
    primaryText := "ǹ gbā le yÒ-Ò lī"
    glossedTokens := [("ǹ", "I"), ("gbā", "speak"), ("le", "CONJ"), ("yÒ-Ò", "child-DEF"), ("lī", "eat")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "AND"), ("order", "cause-effect")] }

def ex_7 : Datum :=
  { id := "song1996_7"
    source := ⟨"song-1996", "(7), p. 13"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "kiho-ka cini-ka wus-ke ha-əss-ɨna cini-ka wus-ci=an-əss-ta"
    glossedTokens := [("kiho-ka", "Keeho-NOM"), ("cini-ka", "Jinee-NOM"), ("wus-ke", "smile-PURP"), ("ha-əss-ɨna", "cause-PST-but"), ("cini-ka", "Jinee-NOM"), ("wus-ci=an-əss-ta", "smile-NEG-PST-IND")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "two"), ("link", "PURP"), ("order", "effect-cause"), ("effect", "negated")] }

def ex_24 : Datum :=
  { id := "song1996_24"
    source := ⟨"song-1996", "(24), p. 33"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je ferai lire le livre à Nicole"
    glossedTokens := [("Je", "I"), ("ferai", "make + FUT"), ("lire", "read"), ("le", "the"), ("livre", "book (ACC)"), ("à", "DAT"), ("Nicole", "Nicole")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "free")] }

def ex_104 : Datum :=
  { id := "song1996_104"
    source := ⟨"song-1996", "(104), p. 68"⟩
    reportedIn := none
    language := "khmu1256"
    primaryText := "kə̀ə p-ŋ̀mɔ́ɔŋ nàa, nàa pə́ə mɔ́ɔŋ"
    glossedTokens := [("kə̀ə", "he"), ("p-ŋ̀mɔ́ɔŋ", "CP-sad"), ("nàa,", "she"), ("nàa", "she"), ("pə́ə", "not"), ("mɔ́ɔŋ", "sad")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauses", "one"), ("vcause", "bound"), ("effect", "negated")] }

def all : List Datum := [ex_1b, ex_6, ex_2b, ex_3b, ex_4a, ex_5, ex_7, ex_24, ex_104]

end Song1996.Examples
