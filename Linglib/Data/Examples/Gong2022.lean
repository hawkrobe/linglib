module

public import Linglib.Data.Examples.Schema

/-!
# `Gong2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Gong2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gong2022.Examples`.
-/

@[expose] public section

namespace Gong2022.Examples

def ex_18b : Datum :=
  { id := "gong2022_18b"
    source := ⟨"gong-2022", "(18b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Bagš [Čemeg-in nom-ig] tüün-d ög-sön."
    glossedTokens := [("Bagš", "teacher.NOM"), ("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("tüün-d", "3SG-DAT"), ("ög-sön", "give-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "SS"), ("binder", "IO"), ("mover", "DP")] }

def ex_19b : Datum :=
  { id := "gong2022_19b"
    source := ⟨"gong-2022", "(19b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in nom-ig] bagš tüün-d ög-sön."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("bagš", "teacher.NOM"), ("tüün-d", "3SG-DAT"), ("ög-sön", "give-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IS"), ("binder", "IO"), ("mover", "DP")] }

def ex_20b : Datum :=
  { id := "gong2022_20b"
    source := ⟨"gong-2022", "(20b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in nom-ig] ter ura-san."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("ter", "3SG.NOM"), ("ura-san", "tear-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IS"), ("binder", "subject"), ("mover", "DP")] }

def ex_21b : Datum :=
  { id := "gong2022_21b"
    source := ⟨"gong-2022", "(21b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in nom-ig] ter Bat-ad ög-sön."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("nom-ig", "book-ACC"), ("ter", "3SG.NOM"), ("Bat-ad", "Bat-DAT"), ("ög-sön", "give-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IS"), ("binder", "subject"), ("mover", "DP")] }

def ex_32b : Datum :=
  { id := "gong2022_32b"
    source := ⟨"gong-2022", "(32b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in eej-iig] bi tüün-d [sain khün gej] khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("eej-iig", "mother-ACC"), ("bi", "1SG.NOM"), ("tüün-d", "3SG-DAT"), ("sain", "good"), ("khün", "person"), ("gej", "C"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "ACC-SUBJ"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_33 : Datum :=
  { id := "gong2022_33"
    source := ⟨"gong-2022", "(33)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Baatar-in zokhiol-iig] ter [maš sain gej] khel-sen."
    glossedTokens := [("Baatar-in", "Baatar-GEN"), ("zokhiol-iig", "article-ACC"), ("ter", "3SG.NOM"), ("maš", "very"), ("sain", "good"), ("gej", "C"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "ACC-SUBJ"), ("binder", "matrix subject"), ("mover", "DP")] }

def ex_40 : Datum :=
  { id := "gong2022_40"
    source := ⟨"gong-2022", "(40)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in esee-g] ter [bagš-iig unš-san gej] khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("esee-g", "essay-ACC"), ("ter", "3SG.NOM"), ("bagš-iig", "teacher-ACC"), ("unš-san", "read-PST"), ("gej", "C"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "matrix subject"), ("mover", "DP")] }

def ex_41 : Datum :=
  { id := "gong2022_41"
    source := ⟨"gong-2022", "(41)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in esee-g] Zaya tüün-d [bagš-iig unš-san gej] khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("esee-g", "essay-ACC"), ("Zaya", "Zaya.NOM"), ("tüün-d", "3SG-DAT"), ("bagš-iig", "teacher-ACC"), ("unš-san", "read-PST"), ("gej", "C"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_58a : Datum :=
  { id := "gong2022_58a"
    source := ⟨"gong-2022", "(58a)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Bi [Bat-in eej-iig] tüün-d [sain khün gej] khel-sen."
    glossedTokens := [("Bi", "1SG.NOM"), ("Bat-in", "Bat-GEN"), ("eej-iig", "mother-ACC"), ("tüün-d", "3SG-DAT"), ("sain", "good"), ("khün", "person"), ("gej", "C"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "ACC-SUBJ intermediate"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_58b : Datum :=
  { id := "gong2022_58b"
    source := ⟨"gong-2022", "(58b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Zaya [Bat-in esee-g] tüün-d [bagš-iig-aa unš-san gej] khel-sen."
    glossedTokens := [("Zaya", "Zaya.NOM"), ("Bat-in", "Bat-GEN"), ("esee-g", "essay-ACC"), ("tüün-d", "3SG-DAT"), ("bagš-iig-aa", "teacher-ACC-REFL.POSS"), ("unš-san", "read-PST"), ("gej", "C"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS intermediate"), ("binder", "matrix DAT"), ("mover", "DP")] }

def ex_61 : Datum :=
  { id := "gong2022_61"
    source := ⟨"gong-2022", "(61)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in em-iig] emč [tüün-iig uu-gaagüi gej] uurla-san."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("em-iig", "medicine-ACC"), ("emč", "doctor.NOM"), ("tüün-iig", "3SG-ACC"), ("uu-gaagüi", "drink-PST.NEG"), ("gej", "C"), ("uurla-san", "become.angry-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "embedded subject"), ("mover", "DP")] }

def ex_79 : Datum :=
  { id := "gong2022_79"
    source := ⟨"gong-2022", "(79)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Čemeg-in eej-id] ter nom ög-sön."
    glossedTokens := [("Čemeg-in", "Čemeg-GEN"), ("eej-id", "mother-DAT"), ("ter", "3SG.NOM"), ("nom", "book"), ("ög-sön", "give-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "IO"), ("binder", "subject"), ("mover", "DP-lexical")] }

def ex_85b : Datum :=
  { id := "gong2022_85b"
    source := ⟨"gong-2022", "(85b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in nom] bagš-aar tüün-d ögö-gd-sön."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("nom", "book.NOM"), ("bagš-aar", "teacher-INST"), ("tüün-d", "3SG-DAT"), ("ögö-gd-sön", "give-PASS-PST")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "passive"), ("binder", "IO"), ("mover", "DP")] }

def ex_86 : Datum :=
  { id := "gong2022_86"
    source := ⟨"gong-2022", "(86)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Zorig-iin emee-d] bi [tüün-iig tusal-dag bai-san gej] bodo-j bai-na."
    glossedTokens := [("Zorig-iin", "Zorig-GEN"), ("emee-d", "grandmother-DAT"), ("bi", "1SG.NOM"), ("tüün-iig", "3SG-ACC"), ("tusal-dag", "help-HABIT"), ("bai-san", "COP-PST"), ("gej", "C"), ("bodo-j", "think-CVB"), ("bai-na", "COP-NPST")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "LDS"), ("binder", "embedded subject"), ("mover", "DP-lexical")] }

def ex_93b : Datum :=
  { id := "gong2022_93b"
    source := ⟨"gong-2022", "(93b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-in dontolt-in esreg] emč [tüün-iig kheden jil-iin turš temtse-j bai-san gej] nadad khel-sen."
    glossedTokens := [("Bat-in", "Bat-GEN"), ("dontolt-in", "addiction-GEN"), ("esreg", "against"), ("emč", "doctor"), ("tüün-iig", "3SG-ACC"), ("kheden", "some"), ("jil-iin", "year-GEN"), ("turš", "during"), ("temtse-j", "fight-CVB"), ("bai-san", "COP-PST"), ("gej", "C"), ("nadad", "1SG.DAT"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "PP-LDS"), ("binder", "embedded subject"), ("mover", "PP")] }

def ex_94b : Datum :=
  { id := "gong2022_94b"
    source := ⟨"gong-2022", "(94b)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Zorig-iin öwčin-ii esreg] Zaya tüün-d [emč nar-ig čadakh bükhn-eer-ee temtse-j bol-no gej] khel-sen."
    glossedTokens := [("Zorig-iin", "Zorig-GEN"), ("öwčin-ii", "disease-GEN"), ("esreg", "against"), ("Zaya", "Zaya.NOM"), ("tüün-d", "3SG-DAT"), ("emč", "doctor"), ("nar-ig", "PL-ACC"), ("čadakh", "ability"), ("bükhn-eer-ee", "all-INST-REFL.POSS"), ("temtse-j", "fight-CVB"), ("bol-no", "be-NPST"), ("gej", "C"), ("khel-sen", "say-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "scrambling"), ("construction", "PP-LDS"), ("binder", "matrix DAT"), ("mover", "PP")] }

def ex_47 : Datum :=
  { id := "gong2022_47"
    source := ⟨"gong-2022", "(47)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Emč [Bat-ig em-ee uu-gaagüi gej] uurla-san."
    glossedTokens := [("Emč", "doctor.NOM"), ("Bat-ig", "Bat-ACC"), ("em-ee", "medicine-REFL.POSS"), ("uu-gaagüi", "drink-PST.NEG"), ("gej", "C"), ("uurla-san", "become.angry-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "NOM")] }

def ex_48 : Datum :=
  { id := "gong2022_48"
    source := ⟨"gong-2022", "(48)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Bi [Čang-iig amid bai-gaa gedeg]-t itgeltei bai-na."
    glossedTokens := [("Bi", "1SG.NOM"), ("Čang-iig", "Čang-ACC"), ("amid", "alive"), ("bai-gaa", "COP-NPST.PTCP"), ("gedeg-t", "C-DAT"), ("itgeltei", "believe"), ("bai-na", "COP-NPST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "NOM")] }

def ex_63 : Datum :=
  { id := "gong2022_63"
    source := ⟨"gong-2022", "(63)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "[Bat-ig ger-iin daalgawr-aa khiikh ni] čukhal."
    glossedTokens := [("Bat-ig", "Bat-ACC"), ("ger-iin", "home-GEN"), ("daalgawr-aa", "assignment-REFL.POSS"), ("khiikh", "do.INF"), ("ni", "3SG.POSS"), ("čukhal", "important")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "none")] }

def ex_64 : Datum :=
  { id := "gong2022_64"
    source := ⟨"gong-2022", "(64)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Saruul [Jon-ig šine mašin aw-san gej] uurla-san."
    glossedTokens := [("Saruul", "Saruul.NOM"), ("Jon-ig", "Jon-ACC"), ("šine", "new"), ("mašin", "car"), ("aw-san", "buy-PST"), ("gej", "C"), ("uurla-san", "become.angry-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "NOM")] }

def ex_65 : Datum :=
  { id := "gong2022_65"
    source := ⟨"gong-2022", "(65)"⟩
    reportedIn := none
    language := "halh1238"
    primaryText := "Saruul-d [Jon-ig šine mašin aw-san gej] sanagda-j bai-san."
    glossedTokens := [("Saruul-d", "Saruul-DAT"), ("Jon-ig", "Jon-ACC"), ("šine", "new"), ("mašin", "car"), ("aw-san", "buy-PST"), ("gej", "C"), ("sanagda-j", "seem-CVB"), ("bai-san", "COP-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("kind", "accusative subject"), ("competitor", "DAT")] }

def all : List Datum := [ex_18b, ex_19b, ex_20b, ex_21b, ex_32b, ex_33, ex_40, ex_41, ex_58a, ex_58b, ex_61, ex_79, ex_85b, ex_86, ex_93b, ex_94b, ex_47, ex_48, ex_63, ex_64, ex_65]

end Gong2022.Examples
