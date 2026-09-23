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

def ex_1a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_1a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I ain't never been to jail"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Non-standard English."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("exponents", "clausal negator + negative adverb")]
    comment := "One semantic negation with two exponents."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_2"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(2)"⟩
    reportedIn := some ⟨"de-swart-2010", ""⟩
    language := "stan1288"
    primaryText := "Nadie ha dicho nada"
    discourseSegments := []
    glossedTokens := [("Nadie", "nobody"), ("ha", "has"), ("dicho", "said"), ("nada", "nothing")]
    translation := "Nobody has said anything"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "negative spread")]
    comment := "Two negative indefinites and no clausal negator: negative spread."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_3a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(3a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je n'ai rien entendu"
    discourseSegments := []
    glossedTokens := [("Je", "I"), ("n'ai", "NEG.have"), ("rien", "nothing"), ("entendu", "heard")]
    translation := "I have heard nothing"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "negative"), ("negator", "ne")]
    comment := "Rien is treated as negative, its dominant use being negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3e : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_3e"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(3e)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "J'ai rien entendu"
    discourseSegments := []
    glossedTokens := [("J'ai", "I.have"), ("rien", "nothing"), ("entendu", "heard")]
    translation := "I have heard something"
    context := "Intended with a positive reading of rien."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("indefinite", "negative")]
    comment := "Rien cannot mean 'something'; without ne the sentence means 'I heard nothing' in the informal register."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_14a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(14a)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "poli1260"
    primaryText := "Nikt nie przyszedł"
    discourseSegments := []
    glossedTokens := [("Nikt", "nobody"), ("nie", "NEG"), ("przyszedł", "came")]
    translation := "Nobody came"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("position", "preverbal")]
    comment := "Strict concord: the negator is obligatory with a preverbal negative indefinite."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14b : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_14b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(14b)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "poli1260"
    primaryText := "Nie widziałam nikogo"
    discourseSegments := []
    glossedTokens := [("Nie", "NEG"), ("widziałam", "saw"), ("nikogo", "nobody")]
    translation := "I saw nobody"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("position", "postverbal")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_15a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(15a)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "stan1288"
    primaryText := "Nadie vino"
    discourseSegments := []
    glossedTokens := [("Nadie", "nobody"), ("vino", "came")]
    translation := "Nobody came"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "absent")]
    comment := "The Spanish subtype: no clausal negator with a preverbal negative indefinite."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15b : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_15b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(15b)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "stan1288"
    primaryText := "No vi a nadie"
    discourseSegments := []
    glossedTokens := [("No", "NEG"), ("vi", "saw"), ("a", "to"), ("nadie", "nobody")]
    translation := "I didn't see anybody"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "obligatory")]
    comment := "The clausal negator is obligatory with a postverbal negative indefinite: Negative Early."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_16a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(16a)"⟩
    reportedIn := none
    language := "cent2050"
    primaryText := "ndú-má lèzə̂-nyí"
    discourseSegments := []
    glossedTokens := [("ndú-má", "who-NEG"), ("lèzə̂-nyí", "went-NEG")]
    translation := "Nobody went"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "strict"), ("negator", "postverbal")]
    comment := "Strict concord in a sample language with a postverbal negator."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_20a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(20a)"⟩
    reportedIn := none
    language := "cham1312"
    primaryText := "ni unu istaba guini gi paingi"
    discourseSegments := []
    glossedTokens := [("ni", "NEG"), ("unu", "one"), ("istaba", "AGR.be"), ("guini", "here"), ("gi", "LOC"), ("paingi", "last.night")]
    translation := "No one was here last night"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("contact", "Spanish")]
    comment := "A preverbal negative indefinite in a VSO language, with the Spanish-type pattern borrowed along with the marker ni."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_21a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(21a)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "wala taxi wiʔif"
    discourseSegments := []
    glossedTokens := [("wala", "not.even"), ("taxi", "taxi"), ("wiʔif", "stop.PRF.3MSG")]
    translation := "Not a single taxi stopped"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("indefinite", "wala")]
    comment := "Only the scalar determiner wala shows non-strict concord in Egyptian Arabic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21b : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_21b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(21b)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "miš sāmiʕ wala kilma"
    discourseSegments := []
    glossedTokens := [("miš", "NEG"), ("sāmiʕ", "hear.PTCP.MSG"), ("wala", "not.even"), ("kilma", "word")]
    translation := "I can't hear a single word"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "obligatory")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_24"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(24)"⟩
    reportedIn := none
    language := "icel1247"
    primaryText := "Ég vissi ekki sjá neitt"
    discourseSegments := []
    glossedTokens := [("Ég", "I"), ("vissi", "did"), ("ekki", "NEG"), ("sjá", "see"), ("neitt", "nothing")]
    translation := "I didn't see anything"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("paradigm", "neinn")]
    comment := "The second Icelandic paradigm takes the verbal negator postverbally."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25 : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_25"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(25)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "icel1247"
    primaryText := "Neinn sag (ekki) mig"
    discourseSegments := []
    glossedTokens := [("Neinn", "nobody"), ("sag", "saw"), ("(ekki)", "NEG"), ("mig", "me")]
    translation := "Nobody saw me"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("paradigm", "neinn")]
    comment := "The neinn paradigm cannot occur preverbally at all, (26): concord depends on word order."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27c : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_27c"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(27c)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "oldr1238"
    primaryText := "jako svoego nikto že ne xulit'"
    discourseSegments := []
    glossedTokens := [("jako", "because"), ("svoego", "self.ACC"), ("nikto", "nobody"), ("že", "PRT"), ("ne", "NEG"), ("xulit'", "abuses")]
    translation := "because nobody abuses his own"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")]
    comment := "Older Slavic allows the negator with a preverbal negative indefinite, (28), unlike Spanish."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_29a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(29a)"⟩
    reportedIn := some ⟨"de-swart-2010", ""⟩
    language := "stan1289"
    primaryText := "Ningú (no) ha vist Joan"
    discourseSegments := []
    glossedTokens := [("Ningú", "nobody"), ("(no)", "NEG"), ("ha", "has"), ("vist", "seen"), ("Joan", "John")]
    translation := "Nobody has seen John"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")]
    comment := "Catalan has the older Slavic pattern synchronically, moving from strict formal concord to Spanish-style informal concord."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_31a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_31a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(31a)"⟩
    reportedIn := some ⟨"haspelmath-1997", ""⟩
    language := "stan1293"
    primaryText := "Nobody don't know where it's at"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "African American Vernacular English."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")]
    comment := "The negator is optional in both positions, (32)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_33b : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_33b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(33b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Je (n')ai vu personne"
    discourseSegments := []
    glossedTokens := [("Je", "I"), ("(n')ai", "NEG.have"), ("vu", "seen"), ("personne", "nobody")]
    translation := "I haven't seen anybody"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")]
    comment := "Ne drop makes French a non-strict system of the (32) type."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34a : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_34a"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(34a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Niemand heeft mij (*nie) gezien"
    discourseSegments := []
    glossedTokens := [("Niemand", "nobody"), ("heeft", "has"), ("mij", "me"), ("(*nie)", "NEG"), ("gezien", "seen")]
    translation := "Nobody has seen me"
    context := "Brabantic Belgian Dutch."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "absent")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34b : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_34b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(34b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ik heb niemand (nie) gezien"
    discourseSegments := []
    glossedTokens := [("Ik", "I"), ("heb", "have"), ("niemand", "nobody"), ("(nie)", "NEG"), ("gezien", "seen")]
    translation := "I have seen nobody"
    context := "Brabantic Belgian Dutch."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")]
    comment := "The pattern (30), stage 2 of Table 6, with a postverbal negator."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35b : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_35b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(35b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "versad šeni cigni ver vnaxe"
    discourseSegments := []
    glossedTokens := [("versad", "nowhere"), ("šeni", "your"), ("cigni", "book"), ("ver", "NEG"), ("vnaxe", "1.see.3")]
    translation := "I couldn't see your book anywhere"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("parameter", "immediate precedence")]
    comment := "The negator is optional only when the negative indefinite immediately precedes the verb, (36)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_37 : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_37"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(37)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "votʃ-intʃ (tʃi)-desa"
    discourseSegments := []
    glossedTokens := [("votʃ-intʃ", "no-what"), ("(tʃi)-desa", "(NEG)-saw")]
    translation := "I didn't see anything"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "preverbal"), ("negator", "optional")]
    comment := "Western Armenian tolerates no postverbal negative indefinite, (38), being strongly verb-final."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_40b : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_40b"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(40b)"⟩
    reportedIn := some ⟨"de-swart-2010", ""⟩
    language := "wels1247"
    primaryText := "Welish i neb"
    discourseSegments := []
    glossedTokens := [("Welish", "saw"), ("i", "I"), ("neb", "nobody")]
    translation := "I saw nobody"
    context := "Informal Welsh."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("position", "postverbal"), ("negator", "optional")]
    comment := "Welsh is verb-initial, so there is no preverbal position, (39)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_45 : LinguisticExample :=
  { id := "vanderauweravanalsenoy2016_45"
    source := ⟨"van-der-auwera-van-alsenoy-2016", "(45)"⟩
    reportedIn := none
    language := "east2295"
    primaryText := "Ober men ken dokh tsum keyser nit firn a yidn mit bord un peyes"
    discourseSegments := []
    glossedTokens := []
    translation := "But surely one cannot bring to the emperor any Jew with beard and earlocks"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("concord", "non-strict"), ("parameter", "emphasis")]
    comment := "In Yiddish the absence of concord creates emphasis, independently of word order."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_2, ex_3a, ex_3e, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_20a, ex_21a, ex_21b, ex_24, ex_25, ex_27c, ex_29a, ex_31a, ex_33b, ex_34a, ex_34b, ex_35b, ex_37, ex_40b, ex_45]

end VanDerAuweraVanAlsenoy2016.Examples
