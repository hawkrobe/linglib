module

public import Linglib.Data.Examples.Schema

/-!
# `AissenPolian2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AissenPolian2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AissenPolian2025.Examples`.
-/

@[expose] public section

namespace AissenPolian2025.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "aissenpolian2025_ex1"
    source := ⟨"aissen-polian-2025", "(1)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Bejk'aj x-nich'an te Xun=e."
    glossedTokens := [("Bejk'aj", "CP.be.born"), ("x-nich'an", "A3-child.of.male"), ("te", "DET"), ("Xun=e", "Juan=ENC")]
    context := "Declarative with a possessed theme, Oxchuc Tseltal."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative")] }

def ex2a : LinguisticExample :=
  { id := "aissenpolian2025_ex2a"
    source := ⟨"aissen-polian-2025", "(2a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a x-nich'an] bejk'aj?"
    glossedTokens := [("Mach'a", "who"), ("x-nich'an", "A3-child.of.male"), ("bejk'aj", "CP.be.born")]
    context := "Pied-piping: the question is about a particular child whose existence is presupposed."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative")] }

def ex2b : LinguisticExample :=
  { id := "aissenpolian2025_ex2b"
    source := ⟨"aissen-polian-2025", "(2b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a bejk'aj x-nich'an?"
    glossedTokens := [("Mach'a", "who"), ("bejk'aj", "CP.be.born"), ("x-nich'an", "A3-child.of.male")]
    context := "Stranding: no child is presupposed to exist."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative"), ("table4", "T-none-unaccusative")] }

def ex4 : LinguisticExample :=
  { id := "aissenpolian2025_ex4"
    source := ⟨"aissen-polian-2025", "(4)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a x-bajt s-karo?"
    glossedTokens := [("Mach'a", "who"), ("x-bajt", "ICP-go"), ("s-karo", "A3-car")]
    context := "A group of men planning a community work project ask how they will get to the site; no particular car is presupposed, and 'nobody' is a felicitous answer."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("table4", "T-none-unaccusative")] }

def ex5 : LinguisticExample :=
  { id := "aissenpolian2025_ex5"
    source := ⟨"aissen-polian-2025", "(5)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a x-wakax] la s-mil-ik?"
    glossedTokens := [("Mach'a", "who"), ("x-wakax", "A3-cow"), ("la", "CP"), ("s-mil-ik", "A3-kill-PL")]
    context := "In a kitchen where meat that was obviously not purchased is being cooked; the cow is contextually salient and a 'nobody' answer is nonsensical."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex20a : LinguisticExample :=
  { id := "aissenpolian2025_ex20a"
    source := ⟨"little-2020b", "(11)"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(20a)"⟩
    language := "chol1282"
    primaryText := "[Majki i-wakax] ta' yajl-i?"
    glossedTokens := [("Majki", "who"), ("i-wakax", "A3-cow"), ("ta'", "PFV"), ("yajl-i", "fall-INTR")]
    context := "Ch'ol possessive S_O."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none")] }

def ex20b : LinguisticExample :=
  { id := "aissenpolian2025_ex20b"
    source := ⟨"little-2020b", "(11)"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(20b)"⟩
    language := "chol1282"
    primaryText := "Majki ta' yajl-i [i-wakax]?"
    glossedTokens := [("Majki", "who"), ("ta'", "PFV"), ("yajl-i", "fall-INTR"), ("i-wakax", "A3-cow")]
    context := "Ch'ol possessive S_O, stranded."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("table4", "T-none-unaccusative")] }

def ex22a : LinguisticExample :=
  { id := "aissenpolian2025_ex22a"
    source := ⟨"little-2020b", "(13)"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(22a)"⟩
    language := "chol1282"
    primaryText := "[Majki i-chich] ta' a-k'el-e?"
    glossedTokens := [("Majki", "who"), ("i-chich", "A3-sister"), ("ta'", "PFV"), ("a-k'el-e", "A2-see-TR")]
    context := "Ch'ol possessive O in a monotransitive clause."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex22b : LinguisticExample :=
  { id := "aissenpolian2025_ex22b"
    source := ⟨"little-2020b", "(13)"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(22b)"⟩
    language := "chol1282"
    primaryText := "Majki ta' a-k'el-e [i-chich]?"
    glossedTokens := [("Majki", "who"), ("ta'", "PFV"), ("a-k'el-e", "A2-see-TR"), ("i-chich", "A3-sister")]
    context := "Ch'ol possessive O, stranded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex26b : LinguisticExample :=
  { id := "aissenpolian2025_ex26b"
    source := ⟨"little-2020b", "fn. 10"⟩
    reportedIn := some ⟨"aissen-polian-2025", "(26b)"⟩
    language := "chol1282"
    primaryText := "Majki ta' a-k'el-be [i-chich]?"
    glossedTokens := [("Majki", "who"), ("ta'", "PFV"), ("a-k'el-be", "A2-see-APPL"), ("i-chich", "A3-sister")]
    context := "Ch'ol ditransitive applicative with the possessor as applied object."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveRaising"), ("intervener", "none"), ("probe", "Appl"), ("table4", "Appl-none-ditransitive")] }

def ex23a : LinguisticExample :=
  { id := "aissenpolian2025_ex23a"
    source := ⟨"aissen-polian-2025", "(23a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u s-tseb] av-il ta ch'ivit?"
    glossedTokens := [("Much'u", "who"), ("s-tseb", "A3-girl"), ("av-il", "A2-see"), ("ta", "P"), ("ch'ivit", "market")]
    context := "Possessive O in a monotransitive clause."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex23b : LinguisticExample :=
  { id := "aissenpolian2025_ex23b"
    source := ⟨"aissen-polian-2025", "(23b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u av-il [s-tseb] ta ch'ivit?"
    glossedTokens := [("Much'u", "who"), ("av-il", "A2-see"), ("s-tseb", "A3-girl"), ("ta", "P"), ("ch'ivit", "market")]
    context := "Possessive O, stranded."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex24 : LinguisticExample :=
  { id := "aissenpolian2025_ex24"
    source := ⟨"aissen-polian-2025", "(24)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "I-j-man tal [s-lok'obbail [li Nwéva York xchi'uk li k'elob osil=e]]."
    glossedTokens := [("I-j-man", "CP-A1-buy"), ("tal", "DIR"), ("s-lok'obbail", "A3-representation"), ("li", "DET"), ("Nwéva", "New"), ("York", "York"), ("xchi'uk", "and"), ("li", "DET"), ("k'elob", "lookout"), ("osil=e", "ground=ENC")]
    context := "Text description of a visit to the Empire State Building; nothing in the context implies the existence of pictures."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("construction", "lexicalTransitive"), ("possessum", "nonSpecific")] }

def ex25 : LinguisticExample :=
  { id := "aissenpolian2025_ex25"
    source := ⟨"aissen-polian-2025", "(25)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "K'usi a-man tal [s-lok'obbail]?"
    glossedTokens := [("K'usi", "what"), ("a-man", "A2-buy"), ("tal", "DIR"), ("s-lok'obbail", "A3-representation")]
    context := "Stranding from a non-specific possessive O."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex27 : LinguisticExample :=
  { id := "aissenpolian2025_ex27"
    source := ⟨"aissen-polian-2025", "(27)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "K'usi a-man-be tal [s-lok'obbail]?"
    glossedTokens := [("K'usi", "what"), ("a-man-be", "A2-buy-APPL"), ("tal", "DIR"), ("s-lok'obbail", "A3-representation")]
    context := "The applicative suffix makes (25) grammatical."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveRaising"), ("intervener", "none"), ("probe", "Appl"), ("table4", "Appl-none-ditransitive")] }

def ex28b : LinguisticExample :=
  { id := "aissenpolian2025_ex28b"
    source := ⟨"aissen-polian-2025", "(28b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a la a-man-bey tal [s-lok'ombail]?"
    glossedTokens := [("Mach'a", "who"), ("la", "CP"), ("a-man-bey", "A2-buy-APPL"), ("tal", "DIR"), ("s-lok'ombail", "A3-representation")]
    context := "Tenango Tseltal applicative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveRaising"), ("intervener", "none"), ("probe", "Appl"), ("table4", "Appl-none-ditransitive")] }

def ex28c : LinguisticExample :=
  { id := "aissenpolian2025_ex28c"
    source := ⟨"aissen-polian-2025", "(28c)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a la a-man tal [s-lok'ombail]?"
    glossedTokens := [("Mach'a", "who"), ("la", "CP"), ("a-man", "A2-buy"), ("tal", "DIR"), ("s-lok'ombail", "A3-representation")]
    context := "Tenango Tseltal monotransitive."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive")] }

def ex30 : LinguisticExample :=
  { id := "aissenpolian2025_ex30"
    source := ⟨"aissen-polian-2025", "(30)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u ch-av-al-b-on [s-lo'iltael]?"
    glossedTokens := [("Much'u", "who"), ("ch-av-al-b-on", "ICP-A2-say-APPL-B1SG"), ("s-lo'iltael", "A3-talk")]
    context := "Ditransitive with a first-person thematic applied object filling Spec,ApplP."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveThematic"), ("intervener", "goal"), ("probe", "Appl"), ("table4", "Appl-goal-ditransitive")] }

def ex31 : LinguisticExample :=
  { id := "aissenpolian2025_ex31"
    source := ⟨"aissen-polian-2025", "(31)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Bin ya aw-ak'-b-on [s-tojol]?"
    glossedTokens := [("Bin", "what"), ("ya", "ICP"), ("aw-ak'-b-on", "A2-give-APPL-B1SG"), ("s-tojol", "A3-payment")]
    context := "Tenango Tseltal ditransitive with a thematic applied object."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "O"), ("possessum", "nonSpecific"), ("clause", "ditransitiveThematic"), ("intervener", "goal"), ("probe", "Appl"), ("table4", "Appl-goal-ditransitive")] }

def ex32 : LinguisticExample :=
  { id := "aissenpolian2025_ex32"
    source := ⟨"aissen-polian-2025", "(32)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "I te l-i-k'elan-b-otikotik [s-lok'obbail li jch'ulme'tik=e]."
    glossedTokens := [("I", "and"), ("te", "then"), ("l-i-k'elan-b-otikotik", "CP-B1-present-APPL.PASS-B1EXCL"), ("s-lok'obbail", "A3-representation"), ("li", "DET"), ("jch'ulme'tik=e", "our.holy.mother=ENC")]
    context := "Text: initial mention of the picture; Spec,ApplP is filled by the first-person goal."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "ditransitiveThematic"), ("construction", "lexicalTransitive"), ("possessum", "nonSpecific")] }

def ex35 : LinguisticExample :=
  { id := "aissenpolian2025_ex35"
    source := ⟨"aissen-polian-2025", "(35)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Oy j-librotak."
    glossedTokens := [("Oy", "EXIS"), ("j-librotak", "A1-books")]
    context := "Predicative possession on the existential construction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex36 : LinguisticExample :=
  { id := "aissenpolian2025_ex36"
    source := ⟨"aissen-polian-2025", "(36)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Kap-em j-jol."
    glossedTokens := [("Kap-em", "mixed.up-PRF"), ("j-jol", "A1-head")]
    context := "Experiential collocation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "experientialCollocation")] }

def ex37 : LinguisticExample :=
  { id := "aissenpolian2025_ex37"
    source := ⟨"aissen-polian-2025", "(37)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay j-tak'in."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("j-tak'in", "A1-money")]
    context := "Lexical unaccusative with a non-specific possessive S_O."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative"), ("possessum", "nonSpecific")] }

def ex43 : LinguisticExample :=
  { id := "aissenpolian2025_ex43"
    source := ⟨"aissen-polian-2025", "(43)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "May-uk j-kerem."
    glossedTokens := [("May-uk", "NEG+EXIS-IRR"), ("j-kerem", "A1-boy")]
    context := "Predicative possession under negation: the possessum takes narrow scope."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession"), ("possessum", "nonSpecific")] }

def ex45a : LinguisticExample :=
  { id := "aissenpolian2025_ex45a"
    source := ⟨"aissen-polian-2025", "(45a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Oy [s-na] ta Jobel li Xun=e."
    glossedTokens := [("Oy", "EXIS"), ("s-na", "A3-house"), ("ta", "in"), ("Jobel", "SC"), ("li", "DET"), ("Xun=e", "Juan=ENC")]
    context := "Preferred order: the locative separates possessum and possessor."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex45b : LinguisticExample :=
  { id := "aissenpolian2025_ex45b"
    source := ⟨"aissen-polian-2025", "(45b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Oy [s-na] li Xun ta Jobel=e."
    glossedTokens := [("Oy", "EXIS"), ("s-na", "A3-house"), ("li", "DET"), ("Xun", "Juan"), ("ta", "in"), ("Jobel=e", "SC=ENC")]
    context := "Locative after the possessor."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex46 : LinguisticExample :=
  { id := "aissenpolian2025_ex46"
    source := ⟨"aissen-polian-2025", "(46)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Te oy ta Jobel [s-na li Xun=e]."
    glossedTokens := [("Te", "there"), ("oy", "EXIS"), ("ta", "in"), ("Jobel", "SC"), ("s-na", "A3-house"), ("li", "DET"), ("Xun=e", "Juan=ENC")]
    context := "The whole possessive follows the PP and is definite."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "locativeCopula"), ("possessum", "specific")] }

def ex47 : LinguisticExample :=
  { id := "aissenpolian2025_ex47"
    source := ⟨"aissen-polian-2025", "(47)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Oy s-vix] [oy y-ixlel] ti vinik un=e."
    glossedTokens := [("Oy", "EXIS"), ("s-vix", "A3-older.sis"), ("oy", "EXIS"), ("y-ixlel", "A3-younger.sis"), ("ti", "DET"), ("vinik", "man"), ("un=e", "PAR=ENC")]
    context := "Coordinated existentials with one sentence-final possessor and no prosodic break."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "predicativePossession")] }

def ex48a : LinguisticExample :=
  { id := "aissenpolian2025_ex48a"
    source := ⟨"aissen-polian-2025", "(48a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u oy [x-chitom]?"
    glossedTokens := [("Much'u", "who"), ("oy", "EXIS"), ("x-chitom", "A3-pig")]
    context := "Predicative possession."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession"), ("table4", "T-none-unaccusative")] }

def ex48b : LinguisticExample :=
  { id := "aissenpolian2025_ex48b"
    source := ⟨"aissen-polian-2025", "(48b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u x-chitom] oy?"
    glossedTokens := [("Much'u", "who"), ("x-chitom", "A3-pig"), ("oy", "EXIS")]
    context := "Predicative possession, pied-piped."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession")] }

def ex49a : LinguisticExample :=
  { id := "aissenpolian2025_ex49a"
    source := ⟨"aissen-polian-2025", "(49a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ay [s-tak'in]?"
    glossedTokens := [("Mach'a", "who"), ("ay", "EXIS"), ("s-tak'in", "A3-money")]
    context := "Tenejapa Tseltal predicative possession."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession"), ("table4", "T-none-unaccusative")] }

def ex49b : LinguisticExample :=
  { id := "aissenpolian2025_ex49b"
    source := ⟨"aissen-polian-2025", "(49b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a s-tak'in] ay?"
    glossedTokens := [("Mach'a", "who"), ("s-tak'in", "A3-money"), ("ay", "EXIS")]
    context := "Tenejapa Tseltal, pied-piped."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "predicativePossession")] }

def ex50a : LinguisticExample :=
  { id := "aissenpolian2025_ex50a"
    source := ⟨"aissen-polian-2025", "(50a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Kap-em s-jol li ants=e."
    glossedTokens := [("Kap-em", "mixed.up-PRF"), ("s-jol", "A3-head"), ("li", "DET"), ("ants=e", "woman=ENC")]
    context := "Experiential collocation kap -jol."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "experientialCollocation")] }

def ex51 : LinguisticExample :=
  { id := "aissenpolian2025_ex51"
    source := ⟨"aissen-polian-2025", "(51)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Kap-em-on j-jol."
    glossedTokens := [("Kap-em-on", "mixed.up-PRF-B1SG"), ("j-jol", "A1-head")]
    context := "Experiencer indexed on the verb."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "experientialCollocation")] }

def ex55a : LinguisticExample :=
  { id := "aissenpolian2025_ex55a"
    source := ⟨"aissen-polian-2025", "(55a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u kap-em [s-jol]?"
    glossedTokens := [("Much'u", "who"), ("kap-em", "mix.up-PRF"), ("s-jol", "A3-head")]
    context := "Experiential collocation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "experientialCollocation"), ("table4", "T-none-unaccusative")] }

def ex55b : LinguisticExample :=
  { id := "aissenpolian2025_ex55b"
    source := ⟨"aissen-polian-2025", "(55b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u s-jol] kap-em?"
    glossedTokens := [("Much'u", "who"), ("s-jol", "A3-head"), ("kap-em", "mix.up-PRF")]
    context := "Experiential collocation, pied-piped."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "experientialCollocation")] }

def ex57b : LinguisticExample :=
  { id := "aissenpolian2025_ex57b"
    source := ⟨"aissen-polian-2025", "(57b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u i-yul [x-ch'ulel] ta ak'ubaltik?"
    glossedTokens := [("Much'u", "who"), ("i-yul", "CP-arrive"), ("x-ch'ulel", "A3-soul"), ("ta", "P"), ("ak'ubaltik", "night")]
    context := "yul -ch'ulel is ambiguous between the idiom 'x awakes' and the literal 'x's soul arrives'."
    judgment := .acceptable
    alternatives := []
    readings := [("x woke up", .acceptable), ("x's soul arrived", .unacceptable)]
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "experientialCollocation"), ("table4", "T-none-unaccusative")] }

def ex58b : LinguisticExample :=
  { id := "aissenpolian2025_ex58b"
    source := ⟨"aissen-polian-2025", "(58b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u x-ch'ulel] i-yul ta ak'ubaltik?"
    glossedTokens := [("Much'u", "who"), ("x-ch'ulel", "A3-soul"), ("i-yul", "CP-arrive"), ("ta", "P"), ("ak'ubaltik", "night")]
    context := "The same string with pied-piping."
    judgment := .acceptable
    alternatives := []
    readings := [("whose soul arrived", .acceptable), ("who woke up", .unacceptable)]
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative")] }

def ex59 : LinguisticExample :=
  { id := "aissenpolian2025_ex59"
    source := ⟨"aissen-polian-2025", "(59)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay s-tak'in te x-Mal=e."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("s-tak'in", "A3-money"), ("te", "DET"), ("x-Mal=e", "CLF-Maria=ENC")]
    context := "Ambiguous between a definite and a non-specific possessum; intransitive under both."
    judgment := .acceptable
    alternatives := []
    readings := [("Maria's money was lost", .acceptable), ("Maria lost some money", .acceptable)]
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative")] }

def ex60 : LinguisticExample :=
  { id := "aissenpolian2025_ex60"
    source := ⟨"aissen-polian-2025", "(60)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay ajk'ube s-tak'in te x-Mal=e."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("ajk'ube", "yesterday"), ("s-tak'in", "A3-money"), ("te", "DET"), ("x-Mal=e", "CLF-Maria=ENC")]
    context := "The whole possessive follows the adverb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative"), ("possessum", "specific")] }

def ex61 : LinguisticExample :=
  { id := "aissenpolian2025_ex61"
    source := ⟨"aissen-polian-2025", "(61)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Ch'ay s-tak'in ajk'ube te x-Mal=e."
    glossedTokens := [("Ch'ay", "lost.INTR"), ("s-tak'in", "A3-money"), ("ajk'ube", "yesterday"), ("te", "DET"), ("x-Mal=e", "CLF-Maria=ENC")]
    context := "The adverb separates possessum and possessor."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "lexicalUnaccusative"), ("possessum", "nonSpecific")] }

def ex62a : LinguisticExample :=
  { id := "aissenpolian2025_ex62a"
    source := ⟨"aissen-polian-2025", "(62a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a s-tak'in] ch'ay?"
    glossedTokens := [("Mach'a", "who"), ("s-tak'in", "A3-money"), ("ch'ay", "lost.INTR")]
    context := "About some specific money known to have been lost."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "S_O"), ("possessum", "specific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative")] }

def ex62b : LinguisticExample :=
  { id := "aissenpolian2025_ex62b"
    source := ⟨"aissen-polian-2025", "(62b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ch'ay [s-tak'in]?"
    glossedTokens := [("Mach'a", "who"), ("ch'ay", "lost.INTR"), ("s-tak'in", "A3-money")]
    context := "Who lost some non-specific money."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "S_O"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "lexicalUnaccusative"), ("table4", "T-none-unaccusative")] }

def ex65 : LinguisticExample :=
  { id := "aissenpolian2025_ex65"
    source := ⟨"aissen-polian-2025", "(65)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u ta s-na] ch-av-ikta komel a-bolsa?"
    glossedTokens := [("Much'u", "who"), ("ta", "P"), ("s-na", "A3-house"), ("ch-av-ikta", "ICP-A2-leave"), ("komel", "DIR"), ("a-bolsa", "A2-bag")]
    context := "Psr-OP pied-piped with the PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "OP"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex66 : LinguisticExample :=
  { id := "aissenpolian2025_ex66"
    source := ⟨"aissen-polian-2025", "(66)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "[Mach'a (ta) s-nah] ya x-'a'tej-at?"
    glossedTokens := [("Mach'a", "who"), ("ta", "P"), ("s-nah", "A3-house"), ("ya", "ICP"), ("x-'a'tej-at", "ICP-work-B2")]
    context := "Petalcingo Tseltal unergative with a locative PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "OP"), ("possessum", "specific"), ("clause", "unergative"), ("intervener", "none")] }

def ex67 : LinguisticExample :=
  { id := "aissenpolian2025_ex67"
    source := ⟨"aissen-polian-2025", "(67)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u ch-av-ikta komel a-bolsa [ta s-na]?"
    glossedTokens := [("Much'u", "who"), ("ch-av-ikta", "ICP-A2-leave"), ("komel", "DIR"), ("a-bolsa", "A2-bag"), ("ta", "P"), ("s-na", "A3-house")]
    context := "Transitive clause with a specific external argument."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "A"), ("table4", "T-A-transitive-OP")] }

def ex68 : LinguisticExample :=
  { id := "aissenpolian2025_ex68"
    source := ⟨"aissen-polian-2025", "(68)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ya x-'a'tej-at [ta s-nah]?"
    glossedTokens := [("Mach'a", "who"), ("ya", "ICP"), ("x-'a'tej-at", "ICP-work-B2"), ("ta", "P"), ("s-nah", "A3-house")]
    context := "Unergative with a specific (second-person) S_A."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unergative"), ("intervener", "S_A"), ("table4", "T-SA-unergative")] }

def ex69 : LinguisticExample :=
  { id := "aissenpolian2025_ex69"
    source := ⟨"aissen-polian-2025", "(69)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a x-'a'tej alaletik ta s-nah?"
    glossedTokens := [("Mach'a", "who"), ("x-'a'tej", "ICP-work"), ("alaletik", "children"), ("ta", "P"), ("s-nah", "A3-house")]
    context := "Unergative with a non-specific S_A."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unergative"), ("intervener", "none"), ("table4", "T-SA-unergative")] }

def ex70 : LinguisticExample :=
  { id := "aissenpolian2025_ex70"
    source := ⟨"aissen-polian-2025", "(70)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Buch'i i-s-mil li Xun=e?"
    glossedTokens := [("Buch'i", "who"), ("i-s-mil", "CP-A3-kill"), ("li", "DET"), ("Xun=e", "Juan=ENC")]
    context := "Ambiguous transitive question."
    judgment := .acceptable
    alternatives := []
    readings := [("who killed Juan", .acceptable), ("who did Juan kill", .acceptable)]
    paperFeatures := [("clause", "transitive")] }

def ex74 : LinguisticExample :=
  { id := "aissenpolian2025_ex74"
    source := ⟨"aissen-polian-2025", "(74)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Och wakax ta s-na te j-Xun=e."
    glossedTokens := [("Och", "CP.enter"), ("wakax", "cow"), ("ta", "in"), ("s-na", "A3-house"), ("te", "DET"), ("j-Xun=e", "M-Juan=ENC")]
    context := "Path verb with a non-specific theme and a locative PP."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "unaccusative"), ("construction", "pathVerb")] }

def ex75a : LinguisticExample :=
  { id := "aissenpolian2025_ex75a"
    source := ⟨"aissen-polian-2025", "(75a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a och wakax [ta s-na]?"
    glossedTokens := [("Mach'a", "who"), ("och", "CP.enter"), ("wakax", "cow"), ("ta", "P"), ("s-na", "A3-house")]
    context := "Path verb, non-specific theme."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "pathVerb"), ("table4", "T-SO-unaccusative")] }

def ex75b : LinguisticExample :=
  { id := "aissenpolian2025_ex75b"
    source := ⟨"aissen-polian-2025", "(75b)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a och-at [ta s-na]?"
    glossedTokens := [("Mach'a", "who"), ("och-at", "CP.enter-B2SG"), ("ta", "P"), ("s-na", "A3-house")]
    context := "Path verb, specific (second-person) theme."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "S_O"), ("construction", "pathVerb"), ("table4", "T-SO-unaccusative")] }

def ex77b : LinguisticExample :=
  { id := "aissenpolian2025_ex77b"
    source := ⟨"aissen-polian-2025", "(77b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u oy ixim [ta s-na]?"
    glossedTokens := [("Much'u", "who"), ("oy", "EXIS"), ("ixim", "corn"), ("ta", "P"), ("s-na", "A3-house")]
    context := "Locative existential with a non-specific theme."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "locativeExistential"), ("table4", "T-none-locativeExistential")] }

def ex78a : LinguisticExample :=
  { id := "aissenpolian2025_ex78a"
    source := ⟨"aissen-polian-2025", "(78a)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a ay-at [ta s-nah]?"
    glossedTokens := [("Mach'a", "who"), ("ay-at", "EXIS-B2"), ("ta", "P"), ("s-nah", "A3-house")]
    context := "Locative copula with a specific theme, Petalcingo Tseltal."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "S_O"), ("construction", "locativeCopula"), ("table4", "T-SO-locativeCopula")] }

def ex78b : LinguisticExample :=
  { id := "aissenpolian2025_ex78b"
    source := ⟨"aissen-polian-2025", "(78b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u oy-ot [ta s-na]?"
    glossedTokens := [("Much'u", "who"), ("oy-ot", "EXIS-B2"), ("ta", "P"), ("s-na", "A3-house")]
    context := "Locative copula with a specific theme."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "S_O"), ("construction", "locativeCopula"), ("table4", "T-SO-locativeCopula")] }

def ex81 : LinguisticExample :=
  { id := "aissenpolian2025_ex81"
    source := ⟨"aissen-polian-2025", "(81)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'u k'ux-at [ta y-o'tan]?"
    glossedTokens := [("Mach'u", "who"), ("k'ux-at", "painful-B2"), ("ta", "P"), ("y-o'tan", "A3-heart")]
    context := "Two-argument experiential collocation with a specific (second-person) theme."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "twoArgExperiential"), ("table4", "T-none-experiential")] }

def ex82 : LinguisticExample :=
  { id := "aissenpolian2025_ex82"
    source := ⟨"aissen-polian-2025", "(82)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u i-yul [ta s-jol] [(ta) s-man-el kantela]?"
    glossedTokens := [("Much'u", "who"), ("i-yul", "CP-arrive"), ("ta", "P"), ("s-jol", "A3-head"), ("ta", "P"), ("s-man-el", "A3-buy-NMLZ"), ("kantela", "candle")]
    context := "Two-argument experiential collocation yul ta -jol."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "OP"), ("possessum", "nonSpecific"), ("clause", "unaccusative"), ("intervener", "none"), ("construction", "twoArgExperiential"), ("table4", "T-none-experiential")] }

def ex85a : LinguisticExample :=
  { id := "aissenpolian2025_ex85a"
    source := ⟨"aissen-polian-2025", "(85a)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "[Much'u x-ch'amal] i-y-elk'an chij?"
    glossedTokens := [("Much'u", "who"), ("x-ch'amal", "A3-child.of.male"), ("i-y-elk'an", "CP-A3-steal"), ("chij", "sheep")]
    context := "Possessive A."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "piedPiping"), ("possessorOf", "A"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex85b : LinguisticExample :=
  { id := "aissenpolian2025_ex85b"
    source := ⟨"aissen-polian-2025", "(85b)"⟩
    reportedIn := none
    language := "tzot1259"
    primaryText := "Much'u i-y-elk'an chij x-ch'amal?"
    glossedTokens := [("Much'u", "who"), ("i-y-elk'an", "CP-A3-steal"), ("chij", "sheep"), ("x-ch'amal", "A3-child.of.male")]
    context := "Possessive A, stranded; the A is specific."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "A"), ("possessum", "specific"), ("clause", "transitive"), ("intervener", "none")] }

def ex86 : LinguisticExample :=
  { id := "aissenpolian2025_ex86"
    source := ⟨"aissen-polian-2025", "(86)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "Mach'a la s-wilunta-on [x-ch'akul]?"
    glossedTokens := [("Mach'a", "who"), ("la", "CP"), ("s-wilunta-on", "A3-fly.onto-B1"), ("x-ch'akul", "A3-flea")]
    context := "Transitive with a non-specific possessive A whose possessor is a plausible ψ-subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("strategy", "stranding"), ("possessorOf", "A"), ("possessum", "nonSpecific"), ("clause", "transitive"), ("intervener", "none")] }

def ex87 : LinguisticExample :=
  { id := "aissenpolian2025_ex87"
    source := ⟨"aissen-polian-2025", "(87)"⟩
    reportedIn := none
    language := "tzel1254"
    primaryText := "La s-wilunta-on [x-ch'akul] ajk'ube [te ts'i'=e]."
    glossedTokens := [("La", "CP"), ("s-wilunta-on", "A3-fly.onto-B1"), ("x-ch'akul", "A3-flea"), ("ajk'ube", "last.night"), ("te", "DET"), ("ts'i'=e", "dog=ENC")]
    context := "Possessor and possessum separated by an adverb."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "transitive"), ("construction", "lexicalTransitive"), ("possessum", "nonSpecific")] }

def all : List LinguisticExample := [ex1, ex2a, ex2b, ex4, ex5, ex20a, ex20b, ex22a, ex22b, ex26b, ex23a, ex23b, ex24, ex25, ex27, ex28b, ex28c, ex30, ex31, ex32, ex35, ex36, ex37, ex43, ex45a, ex45b, ex46, ex47, ex48a, ex48b, ex49a, ex49b, ex50a, ex51, ex55a, ex55b, ex57b, ex58b, ex59, ex60, ex61, ex62a, ex62b, ex65, ex66, ex67, ex68, ex69, ex70, ex74, ex75a, ex75b, ex77b, ex78a, ex78b, ex81, ex82, ex85a, ex85b, ex86, ex87]

end AissenPolian2025.Examples
