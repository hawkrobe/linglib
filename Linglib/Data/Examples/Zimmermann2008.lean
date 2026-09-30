module

public import Linglib.Data.Examples.Schema

/-!
# `Zimmermann2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Zimmermann2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zimmermann2008.Examples`.
-/

@[expose] public section

namespace Zimmermann2008.Examples

open Data.Examples

def ex_11a : LinguisticExample :=
  { id := "zimmermann2008_11a"
    source := ⟨"zimmermann-2008", "(11a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Audù bà-i sàyi hùulaa à kàasuwaa ba"
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG"), ("sàyi", "buy"), ("hùulaa", "cap"), ("à", "at"), ("kàasuwaa", "market"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")] }

def ex_12a : LinguisticExample :=
  { id := "zimmermann2008_12a"
    source := ⟨"zimmermann-2008", "(12a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "manòomii bà-i zoo ba"
    glossedTokens := [("manòomii", "farmer"), ("bà-i", "NEG-3SG"), ("zoo", "come"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")] }

def ex_13a : LinguisticExample :=
  { id := "zimmermann2008_13a"
    source := ⟨"zimmermann-2008", "(13a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "mutàanee bà sù tàfi kàasuwaa ba"
    glossedTokens := [("mutàanee", "people"), ("bà", "NEG"), ("sù", "3PL"), ("tàfi", "go"), ("kàasuwaa", "market"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "bare"), ("scope", "NEG > ∃")] }

def ex_63a : LinguisticExample :=
  { id := "zimmermann2008_63a"
    source := ⟨"zimmermann-2008", "(63a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "sai wani yaaròo yaa cêe"
    glossedTokens := [("sai", "then"), ("wani", "some"), ("yaaròo", "boy"), ("yaa", "3SG.PERF"), ("cêe", "say")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("function", "discourse-introducing")] }

def ex_64 : LinguisticExample :=
  { id := "zimmermann2008_64"
    source := ⟨"zimmermann-2008", "(64)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "wasu sun zoo, wasu bà sù zoo ba"
    glossedTokens := [("wasu", "some"), ("sun", "3PL.PERF"), ("zoo", "come"), ("wasu", "some"), ("bà", "NEG"), ("sù", "3PL.SUBJ"), ("zoo", "come"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wasu"), ("reading", "partitive")] }

def ex_65a : LinguisticExample :=
  { id := "zimmermann2008_65a"
    source := ⟨"zimmermann-2008", "(65a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Wani yaa zoo?"
    glossedTokens := [("Wani", "some/any"), ("yaa", "3SG.PERF"), ("zoo", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("clause", "polar question")] }

def ex_69a : LinguisticExample :=
  { id := "zimmermann2008_69a"
    source := ⟨"zimmermann-2008", "(69a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n ga wani ba"
    glossedTokens := [("bà-n", "NEG-1SG.SUBJ"), ("ga", "see"), ("wani", "someone"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("position", "object"), ("scope", "ambiguous")] }

def ex_69b : LinguisticExample :=
  { id := "zimmermann2008_69b"
    source := ⟨"zimmermann-2008", "(69b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "Muusaa bà-i kiraa wani àbookii lìyaafaa ba"
    glossedTokens := [("Muusaa", "Musa"), ("bà-i", "NEG-3SG.SUBJ"), ("kiraa", "invite"), ("wani", "some"), ("àbookii", "friend"), ("lìyaafaa", "ceremony"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wani"), ("position", "object"), ("scope", "ambiguous")] }

def ex_70 : LinguisticExample :=
  { id := "zimmermann2008_70"
    source := ⟨"zimmermann-2008", "(70)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "wasu bà sù zoo ba"
    glossedTokens := [("wasu", "some.PL"), ("bà", "NEG"), ("sù", "3PL"), ("zoo", "come"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "wasu"), ("position", "subject"), ("scope", "∃ > NEG only")] }

def ex_71 : LinguisticExample :=
  { id := "zimmermann2008_71"
    source := ⟨"zimmermann-2008", "(71)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "baabù wan dà ya zoo"
    glossedTokens := [("baabù", "not.exist"), ("wan", "someone"), ("dà", "REL"), ("ya", "3SG.PERF.REL"), ("zoo", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "negative existential relative")] }

def ex_73 : LinguisticExample :=
  { id := "zimmermann2008_73"
    source := ⟨"zimmermann-2008", "(73)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n ga koo-waa ba"
    glossedTokens := [("bà-n", "NEG-1SG.SUBJ"), ("ga", "see"), ("koo-waa", "DISJ-who"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("negation", "VP"), ("scope", "negative existential only")] }

def ex_74a : LinguisticExample :=
  { id := "zimmermann2008_74a"
    source := ⟨"zimmermann-2008", "(74a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bàa koo-waa kèe sô-n wannàn jàriidàa ba"
    glossedTokens := [("bàa", "NEG"), ("koo-waa", "DISJ-who"), ("kèe", "PROG.REL"), ("sô-n", "like-LINK"), ("wannàn", "this"), ("jàriidàa", "newspaper"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("negation", "sentential"), ("scope", "negative universal only")] }

def ex_75 : LinguisticExample :=
  { id := "zimmermann2008_75"
    source := ⟨"zimmermann-2008", "(75)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-waa bà-i ci jarràbâawaa ba"
    glossedTokens := [("koo-waa", "DISJ-who"), ("bà-i", "NEG-3SG.SUBJ"), ("ci", "eat"), ("jarràbâawaa", "exam"), ("ba", "NEG")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("position", "subject")] }

def ex_78 : LinguisticExample :=
  { id := "zimmermann2008_78"
    source := ⟨"zimmermann-2008", "(78)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-wànè ɗàalìbii nèe bà-i ci jarràbâawaa ba"
    glossedTokens := [("koo-wànè", "DISJ-which"), ("ɗàalìbii", "student"), ("nèe", "PRT"), ("bà-i", "NEG-3SG"), ("ci", "eat"), ("jarràbâawaa", "exam"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("position", "subject"), ("focus", "yes")] }

def ex_85a : LinguisticExample :=
  { id := "zimmermann2008_85a"
    source := ⟨"zimmermann-2008", "(85a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "duk faasinjoojî-n"
    glossedTokens := [("duk", "all"), ("faasinjoojî-n", "passengers-DEF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("order", "prenominal")] }

def ex_86 : LinguisticExample :=
  { id := "zimmermann2008_86"
    source := ⟨"zimmermann-2008", "(86)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "naa ga duk ɗàalìbii"
    glossedTokens := [("naa", "1SG.PERF"), ("ga", "see"), ("duk", "all"), ("ɗàalìbii", "student")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("restrictor", "singular")] }

def ex_89a : LinguisticExample :=
  { id := "zimmermann2008_89a"
    source := ⟨"zimmermann-2008", "(89a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "koo-wànè ɗàalìbii yáa tàaru à gàba-n makarantaa"
    glossedTokens := [("koo-wànè", "DISJ-which"), ("ɗàalìbii", "student"), ("yáa", "3SG.PERF"), ("tàaru", "gather"), ("à", "at"), ("gàba-n", "front-LINK"), ("makarantaa", "school")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "koo+wh"), ("predicate", "collective")] }

def ex_90a : LinguisticExample :=
  { id := "zimmermann2008_90a"
    source := ⟨"zimmermann-2008", "(90a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "duk ɗàalìbâ-n sun tàaru à gàba-n makarantaa"
    glossedTokens := [("duk", "all"), ("ɗàalìbâ-n", "students-DEF"), ("sun", "3PL.PERF"), ("tàaru", "gather"), ("à", "at"), ("gàba-n", "front-LINK"), ("makarantaa", "school")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("predicate", "collective")] }

def ex_91a : LinguisticExample :=
  { id := "zimmermann2008_91a"
    source := ⟨"zimmermann-2008", "(91a)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bà-n karàntà duk lìttàttàafâ-n ba"
    glossedTokens := [("bà-n", "NEG-1SG"), ("karàntà", "read"), ("duk", "all"), ("lìttàttàafâ-n", "books-DEF"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("negation", "VP"), ("scope", "negative universal")] }

def ex_91b : LinguisticExample :=
  { id := "zimmermann2008_91b"
    source := ⟨"zimmermann-2008", "(91b)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "bàa duk bàaƙii su-kà zoo ba"
    glossedTokens := [("bàa", "NEG"), ("duk", "all"), ("bàaƙii", "guests"), ("su-kà", "3PL-PERF.REL"), ("zoo", "come"), ("ba", "NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("quantifier", "duk"), ("negation", "sentential"), ("scope", "negative universal")] }

def all : List LinguisticExample := [ex_11a, ex_12a, ex_13a, ex_63a, ex_64, ex_65a, ex_69a, ex_69b, ex_70, ex_71, ex_73, ex_74a, ex_75, ex_78, ex_85a, ex_86, ex_89a, ex_90a, ex_91a, ex_91b]

end Zimmermann2008.Examples
