module

public import Linglib.Data.Examples.Schema

/-!
# `VanDerAuweraVanAlsenoy2016` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerAuweraVanAlsenoy2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerAuweraVanAlsenoy2016.Examples`.
-/

@[expose] public section

namespace VanDerAuweraVanAlsenoy2016.Examples

open Data.Examples

def ex_1a : Datum :=
  { id := "vanderauweravanalsenoy2016_1a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I ain't never been to jail"
    glossedTokens := []
    context := "Non-standard English."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("exponents", "clausal negator + negative adverb")] }

def ex_2 : Datum :=
  { id := "vanderauweravanalsenoy2016_2"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(2)"⟩
    reportedIn := some ⟨"de-swart-2010", ""⟩
    language := "stan1288"
    primaryText := "Nadie ha dicho nada"
    glossedTokens := [("Nadie", "nobody"), ("ha", "has"), ("dicho", "said"), ("nada", "nothing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "negative spread")] }

def ex_3a : Datum :=
  { id := "vanderauweravanalsenoy2016_3a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(3a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je n'ai rien entendu"
    glossedTokens := [("Je", "I"), ("n'ai", "NEG.have"), ("rien", "nothing"), ("entendu", "heard")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "negative"), ("negator", "ne")] }

def ex_3e : Datum :=
  { id := "vanderauweravanalsenoy2016_3e"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(3e)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai rien entendu"
    glossedTokens := [("J'ai", "I.have"), ("rien", "nothing"), ("entendu", "heard")]
    context := "Intended with a positive reading of rien."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "negative")] }

def ex_14a : Datum :=
  { id := "vanderauweravanalsenoy2016_14a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(14a)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "poli1260"
    primaryText := "Nikt nie przyszedł"
    glossedTokens := [("Nikt", "nobody"), ("nie", "NEG"), ("przyszedł", "came")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("position", "preverbal")] }

def ex_14b : Datum :=
  { id := "vanderauweravanalsenoy2016_14b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(14b)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "poli1260"
    primaryText := "Nie widziałam nikogo"
    glossedTokens := [("Nie", "NEG"), ("widziałam", "saw"), ("nikogo", "nobody")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("position", "postverbal")] }

def ex_15a : Datum :=
  { id := "vanderauweravanalsenoy2016_15a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(15a)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "stan1288"
    primaryText := "Nadie vino"
    glossedTokens := [("Nadie", "nobody"), ("vino", "came")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "absent")] }

def ex_15b : Datum :=
  { id := "vanderauweravanalsenoy2016_15b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(15b)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "stan1288"
    primaryText := "No vi a nadie"
    glossedTokens := [("No", "NEG"), ("vi", "saw"), ("a", "to"), ("nadie", "nobody")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "obligatory")] }

def ex_16a : Datum :=
  { id := "vanderauweravanalsenoy2016_16a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(16a)"⟩
    reportedIn := none
    language := "cent2050"
    primaryText := "ndú-má lèzə̂-nyí"
    glossedTokens := [("ndú-má", "who-NEG"), ("lèzə̂-nyí", "went-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("negator", "postverbal")] }

def ex_20a : Datum :=
  { id := "vanderauweravanalsenoy2016_20a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(20a)"⟩
    reportedIn := none
    language := "cham1312"
    primaryText := "ni unu istaba guini gi paingi"
    glossedTokens := [("ni", "NEG"), ("unu", "one"), ("istaba", "AGR.be"), ("guini", "here"), ("gi", "LOC"), ("paingi", "last.night")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("contact", "Spanish")] }

def ex_21a : Datum :=
  { id := "vanderauweravanalsenoy2016_21a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(21a)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "wala taxi wiʔif"
    glossedTokens := [("wala", "not.even"), ("taxi", "taxi"), ("wiʔif", "stop.PRF.3MSG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("indefinite", "wala")] }

def ex_21b : Datum :=
  { id := "vanderauweravanalsenoy2016_21b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(21b)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "miš sāmiʕ wala kilma"
    glossedTokens := [("miš", "NEG"), ("sāmiʕ", "hear.PTCP.MSG"), ("wala", "not.even"), ("kilma", "word")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "obligatory")] }

def ex_24 : Datum :=
  { id := "vanderauweravanalsenoy2016_24"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(24)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vissi ekki sjá neitt"
    glossedTokens := [("Ég", "I"), ("vissi", "did"), ("ekki", "NEG"), ("sjá", "see"), ("neitt", "nothing")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("paradigm", "neinn")] }

def ex_25 : Datum :=
  { id := "vanderauweravanalsenoy2016_25"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(25)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "icel1247"
    primaryText := "Neinn sag (ekki) mig"
    glossedTokens := [("Neinn", "nobody"), ("sag", "saw"), ("(ekki)", "NEG"), ("mig", "me")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("paradigm", "neinn")] }

def ex_27c : Datum :=
  { id := "vanderauweravanalsenoy2016_27c"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(27c)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "oldr1238"
    primaryText := "jako svoego nikto že ne xulit'"
    glossedTokens := [("jako", "because"), ("svoego", "self.ACC"), ("nikto", "nobody"), ("že", "PRT"), ("ne", "NEG"), ("xulit'", "abuses")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_29a : Datum :=
  { id := "vanderauweravanalsenoy2016_29a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(29a)"⟩
    reportedIn := some ⟨"de-swart-2010", ""⟩
    language := "stan1289"
    primaryText := "Ningú (no) ha vist Joan"
    glossedTokens := [("Ningú", "nobody"), ("(no)", "NEG"), ("ha", "has"), ("vist", "seen"), ("Joan", "John")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_31a : Datum :=
  { id := "vanderauweravanalsenoy2016_31a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(31a)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "stan1293"
    primaryText := "Nobody don't know where it's at"
    glossedTokens := []
    context := "African American Vernacular English."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_33b : Datum :=
  { id := "vanderauweravanalsenoy2016_33b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(33b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je (n')ai vu personne"
    glossedTokens := [("Je", "I"), ("(n')ai", "NEG.have"), ("vu", "seen"), ("personne", "nobody")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")] }

def ex_34a : Datum :=
  { id := "vanderauweravanalsenoy2016_34a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(34a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Niemand heeft mij (*nie) gezien"
    glossedTokens := [("Niemand", "nobody"), ("heeft", "has"), ("mij", "me"), ("(*nie)", "NEG"), ("gezien", "seen")]
    context := "Brabantic Belgian Dutch."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "absent")] }

def ex_34b : Datum :=
  { id := "vanderauweravanalsenoy2016_34b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(34b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik heb niemand (nie) gezien"
    glossedTokens := [("Ik", "I"), ("heb", "have"), ("niemand", "nobody"), ("(nie)", "NEG"), ("gezien", "seen")]
    context := "Brabantic Belgian Dutch."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")] }

def ex_35b : Datum :=
  { id := "vanderauweravanalsenoy2016_35b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(35b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "versad šeni cigni ver vnaxe"
    glossedTokens := [("versad", "nowhere"), ("šeni", "your"), ("cigni", "book"), ("ver", "NEG"), ("vnaxe", "1.see.3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("parameter", "immediate precedence")] }

def ex_37 : Datum :=
  { id := "vanderauweravanalsenoy2016_37"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(37)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "votʃ-intʃ (tʃi)-desa"
    glossedTokens := [("votʃ-intʃ", "no-what"), ("(tʃi)-desa", "(NEG)-saw")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")] }

def ex_40b : Datum :=
  { id := "vanderauweravanalsenoy2016_40b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(40b)"⟩
    reportedIn := some ⟨"de-swart-2010", ""⟩
    language := "wels1247"
    primaryText := "Welish i neb"
    glossedTokens := [("Welish", "saw"), ("i", "I"), ("neb", "nobody")]
    context := "Informal Welsh."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")] }

def ex_45 : Datum :=
  { id := "vanderauweravanalsenoy2016_45"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(45)"⟩
    reportedIn := none
    language := "east2295"
    primaryText := "Ober men ken dokh tsum keyser nit firn a yidn mit bord un peyes"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("parameter", "emphasis")] }

def all : List Datum := [ex_1a, ex_2, ex_3a, ex_3e, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_20a, ex_21a, ex_21b, ex_24, ex_25, ex_27c, ex_29a, ex_31a, ex_33b, ex_34a, ex_34b, ex_35b, ex_37, ex_40b, ex_45]

end VanDerAuweraVanAlsenoy2016.Examples
