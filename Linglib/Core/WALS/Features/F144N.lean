import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144N: Obligatory Double Negation in SOV languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144N`.

Chapter 144, 45 languages.
-/

namespace Core.WALS.F144N

/-- WALS 144N values. -/
inductive ObligatoryDoubleNegationInSovLanguages where
  /-- SONegVNeg (1 languages). -/
  | sonegvneg
  /-- SVO but NegSNegOV (1 languages). -/
  | svoButNegsnegov
  /-- NegSO[V-Neg] (4 languages). -/
  | negsoVNeg
  /-- SONeg[V-Neg] (2 languages). -/
  | sonegVNeg
  /-- SO[Neg-V]Neg (1 languages). -/
  | soNegVNeg
  /-- SO[Neg-V-Neg] (13 languages). -/
  | soNegVNeg_6
  /-- SO[Neg-V] with negative tone on verb  SO[Neg-V]&NegTone (1 languages). -/
  | soNegVWithNegativeToneOnVerbSoNegVNegtone
  /-- SONegVNeg/SONeg[V-Neg] (1 languages). -/
  | sonegvnegSonegVNeg
  /-- SVO but SONeg[V-Neg]/SO[Neg-V-Neg] (1 languages). -/
  | svoButSonegVNegSoNegVNeg
  /-- SNegO[V-Neg]/SONeg[V-Neg] (2 languages). -/
  | snegoVNegSonegVNeg
  /-- SO[V-Neg]Neg & OptNegPref/Infix (1 languages). -/
  | soVNegNegOptnegprefInfix
  /-- SNegOVNeg/SNegVONeg (1 languages). -/
  | snegovnegSnegvoneg
  /-- SNegOVNeg/SVONeg&NegTone (1 languages). -/
  | snegovnegSvonegNegtone
  /-- SOV & NegVNeg (3 languages). -/
  | sovNegvneg
  /-- SOV & Neg[V-Neg] (7 languages). -/
  | sovNegVNeg
  /-- SOV & Neg[Neg-V] (1 languages). -/
  | sovNegNegV
  /-- SV & OV & Neg[V-Neg] (2 languages). -/
  | svOvNegVNeg
  /-- SV & OV & [Neg-V-Neg] (2 languages). -/
  | svOvNegVNeg_18
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144N dataset (45 languages). -/
def allData : List (Datapoint ObligatoryDoubleNegationInSovLanguages) :=
  [ { walsCode := "amn", language := "Amanab", iso := "amn", value := .sovNegVNeg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .soNegVNeg_6 }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .svOvNegVNeg }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .snegoVNegSonegVNeg }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .svOvNegVNeg_18 }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .sonegvnegSonegVNeg }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .svoButNegsnegov }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .soNegVNeg }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .soNegVNeg_6 }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .sovNegNegV }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .negsoVNeg }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .sovNegVNeg }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .sovNegVNeg }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .sonegVNeg }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .soNegVNeg_6 }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .snegovnegSnegvoneg }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .negsoVNeg }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .sovNegVNeg }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .negsoVNeg }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .snegovnegSvonegNegtone }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .snegoVNegSonegVNeg }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .soNegVNeg_6 }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .soNegVNeg_6 }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .soNegVNeg_6 }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .svOvNegVNeg_18 }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .sovNegvneg }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .soNegVNeg_6 }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .soNegVNeg_6 }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .sovNegVNeg }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .soNegVWithNegativeToneOnVerbSoNegVNegtone }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .sovNegVNeg }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .sovNegvneg }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .sovNegVNeg }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .sovNegvneg }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .soVNegNegOptnegprefInfix }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .svOvNegVNeg }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .sonegVNeg }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .soNegVNeg_6 }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .svoButSonegVNegSoNegVNeg }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .soNegVNeg_6 }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .sonegvneg }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .soNegVNeg_6 }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .soNegVNeg_6 }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .negsoVNeg }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .soNegVNeg_6 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144N
