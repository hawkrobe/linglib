module

public import Linglib.Data.Examples.Schema

/-!
# `Pylkkanen2008` — typed example data

Auto-generated from `Linglib/Data/Examples/Pylkkanen2008.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Pylkkanen2008.Examples`.
-/

@[expose] public section

namespace Pylkkanen2008.Examples

def ex19a : Datum :=
  { id := "pylkkanen2008_ex19a"
    source := ⟨"pylkkanen-2008", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I baked him a cake."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "recipient")] }

def ex19b : Datum :=
  { id := "pylkkanen2008_ex19b"
    source := ⟨"pylkkanen-2008", "(19b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni tegami-o kaita."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("tegami-o", "letter-ACC"), ("kaita", "write.PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "recipient")] }

def ex19c : Datum :=
  { id := "pylkkanen2008_ex19c"
    source := ⟨"pylkkanen-2008", "(19c)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "John-i Mary-hanthey pyunci-lul sse-ess-ta."
    glossedTokens := [("John-i", "John-NOM"), ("Mary-hanthey", "Mary-DAT"), ("pyunci-lul", "letter-ACC"), ("sse-ess-ta", "write-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "recipient")] }

def ex19d : Datum :=
  { id := "pylkkanen2008_ex19d"
    source := ⟨"pylkkanen-2008", "(19d)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Mukasa ya-som-e-dde Katonga ekitabo."
    glossedTokens := [("Mukasa", "Mukasa"), ("ya-som-e-dde", "3SG.PST-read-APPL-PST"), ("Katonga", "Katonga"), ("ekitabo", "book")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "benefactive")] }

def ex19e : Datum :=
  { id := "pylkkanen2008_ex19e"
    source := ⟨"pylkkanen-2008", "(19e)"⟩
    reportedIn := none
    language := "vend1245"
    primaryText := "Nd-o-tandulela tshimu ya mukegulu."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "benefactive")] }

def ex19f : Datum :=
  { id := "pylkkanen2008_ex19f"
    source := ⟨"pylkkanen-2008", "(19f)"⟩
    reportedIn := none
    language := "alba1267"
    primaryText := "Drita i poqi Agimit kek."
    glossedTokens := [("Drita", "Drita.NOM"), ("i", "CL"), ("poqi", "bake.PST"), ("Agimit", "Agim.DAT"), ("kek", "cake")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "benefactive")] }

def ex20a : Datum :=
  { id := "pylkkanen2008_ex20a"
    source := ⟨"pylkkanen-2008", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I ran him."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex20b : Datum :=
  { id := "pylkkanen2008_ex20b"
    source := ⟨"pylkkanen-2008", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I held him the bag."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex21a : Datum :=
  { id := "pylkkanen2008_ex21a"
    source := ⟨"pylkkanen-2008", "(21a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni hasit-ta."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("hasit-ta", "run-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex21b : Datum :=
  { id := "pylkkanen2008_ex21b"
    source := ⟨"pylkkanen-2008", "(21b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni kanojo-no kaban-o mot-ta."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("kanojo-no", "she-GEN"), ("kaban-o", "bag-ACC"), ("mot-ta", "hold-PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex22a : Datum :=
  { id := "pylkkanen2008_ex22a"
    source := ⟨"pylkkanen-2008", "(22a)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Mary-ka John-hanthey talli-ess-ta."
    glossedTokens := [("Mary-ka", "Mary-NOM"), ("John-hanthey", "John-DAT"), ("talli-ess-ta", "run-PST-DECL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex22b : Datum :=
  { id := "pylkkanen2008_ex22b"
    source := ⟨"pylkkanen-2008", "(22b)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "John-i Mary-hanthey kabang-ul cap-ass-ta."
    glossedTokens := [("John-i", "John-NOM"), ("Mary-hanthey", "Mary-DAT"), ("kabang-ul", "bag-ACC"), ("cap-ass-ta", "hold-PST-DECL")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex23a : Datum :=
  { id := "pylkkanen2008_ex23a"
    source := ⟨"pylkkanen-2008", "(23a)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Mukasa ya-tambu-le-dde Katonga."
    glossedTokens := [("Mukasa", "Mukasa"), ("ya-tambu-le-dde", "3SG.PST-walk-APPL-PST"), ("Katonga", "Katonga")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex23b : Datum :=
  { id := "pylkkanen2008_ex23b"
    source := ⟨"pylkkanen-2008", "(23b)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Katonga ya-kwaant-i-dde Mukasa ensawo."
    glossedTokens := [("Katonga", "Katonga"), ("ya-kwaant-i-dde", "3SG.PST-hold-APPL-PST"), ("Mukasa", "Mukasa"), ("ensawo", "bag")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex24a : Datum :=
  { id := "pylkkanen2008_ex24a"
    source := ⟨"pylkkanen-2008", "(24a)"⟩
    reportedIn := none
    language := "vend1245"
    primaryText := "Ndi-do-shum-el-a musadzi."
    glossedTokens := [("Ndi-do-shum-el-a", "1SG-FUT-work-APPL-FV"), ("musadzi", "lady")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex24b : Datum :=
  { id := "pylkkanen2008_ex24b"
    source := ⟨"pylkkanen-2008", "(24b)"⟩
    reportedIn := none
    language := "vend1245"
    primaryText := "Nd-o-far-el-a Mukasa khali."
    glossedTokens := [("Nd-o-far-el-a", "1SG-PST-hold-APPL-FV"), ("Mukasa", "Mukasa"), ("khali", "pot")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex25a : Datum :=
  { id := "pylkkanen2008_ex25a"
    source := ⟨"pylkkanen-2008", "(25a)"⟩
    reportedIn := none
    language := "alba1267"
    primaryText := "I vrapova."
    glossedTokens := [("I", "3SG.DAT.CL"), ("vrapova", "run.PST.1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "unergative")] }

def ex25b : Datum :=
  { id := "pylkkanen2008_ex25b"
    source := ⟨"pylkkanen-2008", "(25b)"⟩
    reportedIn := none
    language := "alba1267"
    primaryText := "Agimi i mban Drites çanten time."
    glossedTokens := [("Agimi", "Agim.NOM"), ("i", "CL"), ("mban", "hold.3SG"), ("Drites", "Drita.DAT"), ("çanten", "bag.ACC"), ("time", "my")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "static")] }

def ex26a : Datum :=
  { id := "pylkkanen2008_ex26a"
    source := ⟨"pylkkanen-2008", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave Mary the meat raw."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveObject")] }

def ex26b : Datum :=
  { id := "pylkkanen2008_ex26b"
    source := ⟨"pylkkanen-2008", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I gave Mary the meat hungry."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveApplied")] }

def ex40a : Datum :=
  { id := "pylkkanen2008_ex40a"
    source := ⟨"pylkkanen-2008", "(40a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga hadaka-de Hanako-ni hon-o yonda."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("hadaka-de", "naked"), ("Hanako-ni", "Hanako-DAT"), ("hon-o", "book-ACC"), ("yonda", "read.PST")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveApplied")] }

def ex43a : Datum :=
  { id := "pylkkanen2008_ex43a"
    source := ⟨"pylkkanen-2008", "(43a)"⟩
    reportedIn := none
    language := "gand1255"
    primaryText := "Mustafa ya-ko-le-dde Katonga nga mulwadde."
    glossedTokens := [("Mustafa", "Mustafa"), ("ya-ko-le-dde", "3SG.PST-work-APPL-PST"), ("Katonga", "Katonga"), ("nga", "DEP"), ("mulwadde", "sick")]
    context := "Mustafa is healthy and Katonga is sick."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "depictiveApplied")] }

def ex12 : Datum :=
  { id := "pylkkanen2008_ex12"
    source := ⟨"pylkkanen-2008", "(12)"⟩
    reportedIn := none
    language := "kore1280"
    primaryText := "Totuk-i Mary-hanthey panci-lul humchi-ess-ta."
    glossedTokens := [("Totuk-i", "thief-NOM"), ("Mary-hanthey", "Mary-DAT"), ("panci-lul", "ring-ACC"), ("humchi-ess-ta", "steal-PST-DECL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "source")] }

def ex82a : Datum :=
  { id := "pylkkanen2008_ex82a"
    source := ⟨"pylkkanen-2008", "(82a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Ha-yalda kilkela le-Dan et ha-radio."
    glossedTokens := [("Ha-yalda", "the-girl"), ("kilkela", "spoil.PST"), ("le-Dan", "to-Dan"), ("et", "ACC"), ("ha-radio", "the-radio")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "source"), ("construction", "possessorDative")] }

def ex120a : Datum :=
  { id := "pylkkanen2008_ex120a"
    source := ⟨"pylkkanen-2008", "(120a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Hanako-ga dorobou-ni yubiwa-o to-rare-ta."
    glossedTokens := [("Hanako-ga", "Hanako-NOM"), ("dorobou-ni", "thief-DAT"), ("yubiwa-o", "ring-ACC"), ("to-rare-ta", "steal-PASS-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "source"), ("construction", "adversityGapped")] }

def ex121a : Datum :=
  { id := "pylkkanen2008_ex121a"
    source := ⟨"pylkkanen-2008", "(121a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Taroo-ga Hanako-ni shinkoushukyoo-o hajime-rare-ta."
    glossedTokens := [("Taroo-ga", "Taro-NOM"), ("Hanako-ni", "Hanako-DAT"), ("shinkoushukyoo-o", "new.religion-ACC"), ("hajime-rare-ta", "begin-PASS-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "baseline"), ("relation", "malefactive"), ("construction", "adversityGapless")] }

def ex95 : Datum :=
  { id := "pylkkanen2008_ex95"
    source := ⟨"pylkkanen-2008", "(95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John cried the child."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("test", "rootCausativeUnergative")] }

def ex96 : Datum :=
  { id := "pylkkanen2008_ex96"
    source := ⟨"pylkkanen-2008", "(96)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-ga kodomo-o nak-asi-ta."
    glossedTokens := [("John-ga", "John-NOM"), ("kodomo-o", "child-ACC"), ("nak-asi-ta", "cry-CAUS-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("test", "rootCausativeUnergative")] }

def all : List Datum := [ex19a, ex19b, ex19c, ex19d, ex19e, ex19f, ex20a, ex20b, ex21a, ex21b, ex22a, ex22b, ex23a, ex23b, ex24a, ex24b, ex25a, ex25b, ex26a, ex26b, ex40a, ex43a, ex12, ex82a, ex120a, ex121a, ex95, ex96]

end Pylkkanen2008.Examples
