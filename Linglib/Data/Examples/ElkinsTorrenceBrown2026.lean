module

public import Linglib.Data.Examples.Schema

/-!
# `ElkinsTorrenceBrown2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ElkinsTorrenceBrown2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ElkinsTorrenceBrown2026.Examples`.
-/

@[expose] public section

namespace ElkinsTorrenceBrown2026.Examples

open Data.Examples

def ex_10b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_10b"
    source := ⟨"elkins-torrence-brown-2026", "(10b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye kyim?"
    glossedTokens := [("alkye", "who"), ("∅-∅-kyim", "COMPL-B2/3S-die")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "absolutive"), ("reflex", "blocked")] }

def ex_11b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_11b"
    source := ⟨"elkins-torrence-brown-2026", "(11b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Titi' tjaq' Li'y?"
    glossedTokens := [("titi'", "what"), ("∅-∅-t-jaq'", "COMPL-B2/3SG-A2/3SG-open"), ("Li'y", "María")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "absolutive"), ("reflex", "blocked")] }

def ex_12b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_12b"
    source := ⟨"elkins-torrence-brown-2026", "(12b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye jq'on te tjpel ja'?"
    glossedTokens := [("alkye", "who"), ("∅-∅-jq'o-n", "COMPL-B2/3S-open-ANTIP"), ("t-e", "A2/3S-RN:PAT"), ("tjpel", "door"), ("ja'", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("mover", "ergative"), ("reflex", "blocked")] }

def ex_13a : LinguisticExample :=
  { id := "elkinstorrencebrown2026_13a"
    source := ⟨"elkins-torrence-brown-2026", "(13a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "El tsu'n Li'y spik'b'il tu'n xb'uy."
    glossedTokens := [("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n", "A2/3SG-clean-DS"), ("Li'y", "María"), ("spik'b'il", "window"), ("t-u'n", "A2/3SG-RN:INS"), ("xb'uy", "rag")]
    context := ""
    judgment := .acceptable
    alternatives := [("El tsu'na' Li'y spik'b'il tu'n xb'uy.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.1"), ("mover", "none"), ("reflex", "blocked")] }

def ex_13b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_13b"
    source := ⟨"elkins-torrence-brown-2026", "(13b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqu'n el tsu'n(a') Li'y spik'b'il?"
    glossedTokens := [("al-qu'n", "what-RN:INS"), ("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n(=a')", "A2/3SG-clean-DS=MVMT"), ("Li'y", "María"), ("spik'b'il", "window")]
    context := ""
    judgment := .acceptable
    alternatives := [("Alqu'n el tsu'na' Li'y spik'b'il?", .acceptable), ("Alqu'n el tsu'n Li'y spik'b'il?", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2.1"), ("mover", "instrument"), ("reflex", "licensed")] }

def ex_14b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_14b"
    source := ⟨"elkins-torrence-brown-2026", "(14b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe tjaq'(a')ya tjpel ja'?"
    glossedTokens := [("al-qe", "who-RN:BEN"), ("∅-∅-t-jaq'(=a')=ya", "COMPL-B2/3SG-A2/3SG-open=MVMT=2P"), ("tjpel", "door"), ("ja'", "house")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("mover", "benefactive"), ("reflex", "licensed")] }

def ex_15b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_15b"
    source := ⟨"elkins-torrence-brown-2026", "(15b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe' xi' kq'o'n(a)ye' saqchb'il?"
    glossedTokens := [("al-qe", "who-RN:DAT"), ("∅-∅-xi'", "COMPL-B2/3SG-DIR"), ("k-q'o-'n(=a')=ye'", "A2/3P-give-DS=MVMT=2P"), ("saqchb'il", "toy")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.2"), ("mover", "dative"), ("reflex", "licensed")] }

def ex_16b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_16b"
    source := ⟨"elkins-torrence-brown-2026", "(16b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja e' chiyon(a') tx'yan ewi?"
    glossedTokens := [("ja", "where"), ("∅-e'", "COMPL-B2/3P"), ("chiyo-n(=a')", "bark-ANTIP=MVMT"), ("tx'yan", "dog")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.3"), ("mover", "locative"), ("reflex", "licensed")] }

def ex_17b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_17b"
    source := ⟨"elkins-torrence-brown-2026", "(17b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Tiqu'n el tsu'n(a') Li'y spik'b'il tu'n xb'uy?"
    glossedTokens := [("ti'-qu'n", "what-RN:REASON"), ("∅-∅-el", "COMPL-B2/3SG-DIR"), ("t-su-'n(=a')", "A2/3SG-clean-DS=MVMT"), ("Li'y", "María"), ("spik'b'il", "window"), ("t-u'n", "A2/3SG-RN:INS"), ("xb'uy", "rag")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("mover", "reason"), ("reflex", "licensed")] }

def ex_18b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_18b"
    source := ⟨"elkins-torrence-brown-2026", "(18b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Tiqu'n tjoy(a') Xwan tx'yol toj k'ul?"
    glossedTokens := [("ti'-qu'n", "what-RN:PURP"), ("∅-∅-t-joy(=a')", "COMPL-B2/3S-A2/3S-look.for=MVMT"), ("Xwan", "Juan"), ("tx'yol", "mushroom"), ("t-oj", "A2/3S-RN:in"), ("k'ul", "forest")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.4"), ("mover", "purpose"), ("reflex", "licensed")] }

def ex_19b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_19b"
    source := ⟨"elkins-torrence-brown-2026", "(19b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Se'ntu'mel kub' tpa'n(a') Li'y lmet?"
    glossedTokens := [("se'n=tu'mel", "how=ENCL"), ("∅-∅-kub'", "COMPL-B2/3SG-DIR"), ("t-pa-'n(=a')", "A2/3SG-break-DS=MVMT"), ("Li'y", "María"), ("lmet", "bottle")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2.5"), ("mover", "manner"), ("reflex", "licensed")] }

def ex_20b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_20b"
    source := ⟨"elkins-torrence-brown-2026", "(20b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jtoj kxe'l telq'a'n Xwan chmek'?"
    glossedTokens := [("jtoj", "when.NON.PST"), ("k-xe'-l", "B2/3S-DIR-POT"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey")]
    context := ""
    judgment := .acceptable
    alternatives := [("Jtoj kxe'l telq'a'na' Xwan chmek'?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.6"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_21b : LinguisticExample :=
  { id := "elkinstorrencebrown2026_21b"
    source := ⟨"elkins-torrence-brown-2026", "(21b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jtoje xi' telq'a'n Xwan chmek'?"
    glossedTokens := [("jtoje", "when.PST"), ("∅-∅-xi'", "COMPL-B2/3S-DIR"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey")]
    context := ""
    judgment := .acceptable
    alternatives := [("Jtoje xi' telq'a'na' Xwan chmek'?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "2.2.6"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_22 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_22"
    source := ⟨"elkins-torrence-brown-2026", "(22)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja jaw(a') xhchin(a') Luch?"
    glossedTokens := [("ja", "where"), ("∅-∅-jaw(=a')", "COMPL-B2/3S-DIR=MVMT"), ("xhchi-n(=a')", "shout-ANTIP=MVMT"), ("Luch", "Pedro")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("mover", "locative"), ("directionals", "1"), ("hosts", "2")] }

def ex_24 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_24"
    source := ⟨"elkins-torrence-brown-2026", "(24)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Se'ntu'mel in tma'n(a') Li'y kye tzaj wulin(a') Xwan weye'?"
    glossedTokens := [("se'n=tu'mel", "how=ENCL"), ("in", "INC"), ("∅-t-ma-'n(=a')", "B2/3S-A2/3S-say-DS=MVMT"), ("Li'y", "María"), ("kye", "COMP"), ("∅-∅-tzaj", "COM-B2/3S-DIR"), ("wuli-n(=a')", "insult-ANTIP=MVMT"), ("Xwan", "Juan"), ("w-e=ye'", "A1S-RN:DAT=1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "manner"), ("embeddedSize", "cP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_26 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_26"
    source := ⟨"elkins-torrence-brown-2026", "(26)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Mixti' b'i'n wu'ne' se'n kub' tbincha'n(a') Li'y bisiklet."
    glossedTokens := [("mixti'", "NEG"), ("∅-b'i-'n(*=a')", "B2/3S-know-PASS=MVMT"), ("w-u'n=e'", "A1S-RN:AGT=1S"), ("se'n", "how"), ("∅-∅-kub'(=a')", "COM-B2/3S-DIR=MVMT"), ("t-b'incha-'n(=a')", "A2/3S-repair-DS=MVMT"), ("Li'y", "María"), ("bisiklet", "bicycle")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "manner"), ("embeddedSize", "cP"), ("landing", "embedded"), ("matrixReflex", "blocked"), ("embeddedReflex", "licensed")] }

def ex_28 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_28"
    source := ⟨"elkins-torrence-brown-2026", "(28)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja xi'(ya') telq'a'n(a) Xwan chmek' aju tzaj klq'o'n qya?"
    glossedTokens := [("ja", "where"), ("∅-∅-xi'(=ya')", "COMPL-B2/3S-DIR=MVMT"), ("t-elq'a-'n(=a')", "A2/3S-steal-DS=MVMT"), ("Xwan", "Juan"), ("chmek'", "turkey"), ("aju", "REL"), ("∅-∅-tzaj", "COMPL-B2/3S-DIR"), ("k-lq'o-'n", "A2/3P-buy-DS"), ("qya", "woman")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix locative (where Juan stole it)", .acceptable), ("relative-clause locative (where the women bought it)", .unacceptable)]
    paperFeatures := [("section", "3.2"), ("mover", "locative")] }

def ex_29a : LinguisticExample :=
  { id := "elkinstorrencebrown2026_29a"
    source := ⟨"elkins-torrence-brown-2026", "(29a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja xi' telq'a'n Xwan chmek' aju tzaj(a') klq'o'n(a') qya?"
    glossedTokens := [("ja", "where"), ("∅-∅-xi'", "COMPL-B2/3S-DIR"), ("t-elq'a-'n", "A2/3S-steal-DS"), ("Xwan", "Juan"), ("chmek'", "turkey"), ("aju", "REL"), ("∅-∅-tzaj(=a')", "COMPL-B2/3S-DIR=MVMT"), ("k-lq'o-'n(=a')", "A2/3P-buy-DS=MVMT"), ("qya", "woman")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("mover", "locative")] }

def ex_31 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_31"
    source := ⟨"elkins-torrence-brown-2026", "(31)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jatu'mel chu'xh(a) tu'n tk'a'yit(a') chmek'?"
    glossedTokens := [("ja=tu'mel", "where=ENCL"), ("∅-chu'x(=a')", "B2/3S-be.difficult=MVMT"), ("t-u'n", "A2/3S-RN:PURP"), ("t-k'a'y-it(=a')", "A1S-sell-PASS=MVMT"), ("chmek'", "turkey")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("mover", "locative"), ("embeddedSize", "voiceP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_34 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_34"
    source := ⟨"elkins-torrence-brown-2026", "(34)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alqe ok(a') kq'on(a')ye' Pabl jqol(*a') spik'b'il?"
    glossedTokens := [("al-qe", "who-RN:BEN"), ("∅-∅-ok(=a')", "COM-B2/3S-DIR=MVMT"), ("k-q'o-n(=a')=ye'", "A2/3P-make-DS=MVMT=2P"), ("Pabl", "Pablo"), ("jqo-l(*=a')", "open-INF=MVMT"), ("spik'b'il", "window")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("mover", "benefactive"), ("embeddedSize", "bareVP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "blocked")] }

def ex_35c : LinguisticExample :=
  { id := "elkinstorrencebrown2026_35c"
    source := ⟨"elkins-torrence-brown-2026", "(35c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Iku' tzaj tlq'ona'."
    glossedTokens := [("iku'", "yes"), ("∅-∅-tzaj", "COM-B2/3S-DIR"), ("t-lq'o-'n=a'", "A2/3-buy-DS=MVMT")]
    context := "Answering: Did Juan buy the jocotes in the market?"
    judgment := .ungrammatical
    alternatives := [("Iku', atzu tzaj tlq'o'na'.", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.5"), ("mover", "none"), ("reflex", "blocked")] }

def ex_37 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_37"
    source := ⟨"elkins-torrence-brown-2026", "(37)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja'tumel e' k'a'yinjtz(a') muqin tu'n Xwan?"
    glossedTokens := [("ja=tu'mel", "where=ENCL"), ("e'", "COMPL"), ("∅-k'a'yi-njtz(=a')", "B2/3S-sell-PASS=MVMT"), ("muqin", "tortilla"), ("t-u'n", "A2/3S-RN:AGT"), ("Xwan", "Juan")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.6"), ("mover", "locative"), ("reflex", "licensed"), ("voice", "passive")] }

def ex_38 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_38"
    source := ⟨"elkins-torrence-brown-2026", "(38)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Alkye tmaya qa el sun te spik'b'il tu'n xb'uy?"
    glossedTokens := [("alkye", "who"), ("∅-∅-t-ma=ya", "COM-B2/3S-A2/3S-say=2S"), ("qa", "COMP"), ("∅-∅-el", "COM-B2/3S-DIR"), ("su-n", "clean-ANTIP"), ("t-e", "A2/3S-RN:PAT"), ("spik'b'il", "window"), ("t-u'n", "A2/3S-RN:AGT"), ("xb'uy", "rag")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.6"), ("mover", "ergative"), ("antipassive", "embedded only")] }

def ex_63 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_63"
    source := ⟨"elkins-torrence-brown-2026", "(63)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ja e' b'aj(a') el(a') laqj(a') kwetiy?"
    glossedTokens := [("ja", "where"), ("∅-e'", "COM-B2/3PL"), ("b'aj=a'", "DIR=MVMT"), ("el=a'", "DIR=MVMT"), ("laqj=a'", "explode=MVMT"), ("kwetiy", "fireworks")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("mover", "locative"), ("directionals", "2"), ("hosts", "3")] }

def ex_65 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_65"
    source := ⟨"elkins-torrence-brown-2026", "(65)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Jni' hor kub' kjone' chib'j?"
    glossedTokens := [("jni'", "how.many"), ("hor", "hour"), ("∅-∅-kub'", "COMPL-B2/3S-DIR"), ("k-jon(*=a)=e'", "A2/3PL-cut-DS=MVMT=2PL"), ("chib'j", "meat")]
    context := ""
    judgment := .acceptable
    alternatives := [("Jni' hor kub' kjonae' chib'j?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.3"), ("mover", "temporal"), ("reflex", "blocked")] }

def ex_51 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_51"
    source := ⟨"mendes-ranero-2021", "(2)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(51)"⟩
    language := "kich1262"
    primaryText := "Jawii xatb'ee wi iwiir?"
    glossedTokens := [("Jawii", "where"), ("x-at-b'ee", "COMPL-B2SG-go"), ("*(wi)", "FP"), ("iwiir", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := [("Jawii xatb'ee iwiir?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "locative"), ("reflex", "licensed")] }

def ex_52 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_52"
    source := ⟨"mendes-ranero-2021", "(17)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(52)"⟩
    language := "kich1262"
    primaryText := "Jawi xkib'iij wi chi ke'e wi?"
    glossedTokens := [("Jawi", "where"), ("x-∅-ki-b'iij", "COMPL-B3SG-A3SG-say"), ("*(wi)", "FP"), ("chi", "COMP"), ("k-e-'e", "INC-B3PL-go"), ("*(wi)", "FP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "locative"), ("embeddedSize", "cP"), ("landing", "matrix"), ("matrixReflex", "licensed"), ("embeddedReflex", "licensed")] }

def ex_53 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_53"
    source := ⟨"mendes-ranero-2021", "(19)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(53)"⟩
    language := "kich1262"
    primaryText := "Jas ruuk' karayiij katij wi le wa?"
    glossedTokens := [("Jas", "WH"), ("r-uuk'", "A3SG-RN"), ("k-∅-a-rayii-j", "INC-B3SG-A2SG-desire-ACT"), ("(*wi)", "FP"), ("k-∅-a-tij", "INC-B3SG-A2SG-eat"), ("*(wi)", "FP"), ("le", "DET"), ("wa", "food")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("mover", "instrument"), ("embeddedSize", "aspP"), ("landing", "matrix"), ("matrixReflex", "blocked"), ("embeddedReflex", "licensed")] }

def ex_64 : LinguisticExample :=
  { id := "elkinstorrencebrown2026_64"
    source := ⟨"mendes-ranero-2021", "(14a)"⟩
    reportedIn := some ⟨"elkins-torrence-brown-2026", "(64)"⟩
    language := "kaqc1270"
    primaryText := "Achike ruma xsamäj ri a Juan?"
    glossedTokens := [("Achike", "what"), ("ru-ma", "A3SG-RN"), ("x-∅-samäj", "COMPL-B3SG-work"), ("(*wi)", "FP"), ("ri", "DET"), ("a", "CLF"), ("Juan", "Juan")]
    context := ""
    judgment := .acceptable
    alternatives := [("Achike ruma xsamäj wi ri a Juan?", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "5.3"), ("mover", "reason"), ("reflex", "blocked")] }

def all : List LinguisticExample := [ex_10b, ex_11b, ex_12b, ex_13a, ex_13b, ex_14b, ex_15b, ex_16b, ex_17b, ex_18b, ex_19b, ex_20b, ex_21b, ex_22, ex_24, ex_26, ex_28, ex_29a, ex_31, ex_34, ex_35c, ex_37, ex_38, ex_63, ex_65, ex_51, ex_52, ex_53, ex_64]

end ElkinsTorrenceBrown2026.Examples
