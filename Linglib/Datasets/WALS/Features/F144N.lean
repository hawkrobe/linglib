import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144N: Obligatory Double Negation in SOV languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144N`.

Chapter 144, 45 languages.
-/

namespace Datasets.WALS.F144N

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
  [ { walsCode := "amn", iso := "amn", value := .sovNegVNeg }
  , { walsCode := "amh", iso := "amh", value := .soNegVNeg_6 }
  , { walsCode := "amx", iso := "imi", value := .svOvNegVNeg }
  , { walsCode := "apw", iso := "apw", value := .snegoVNegSonegVNeg }
  , { walsCode := "ana", iso := "aro", value := .svOvNegVNeg_18 }
  , { walsCode := "awp", iso := "kwi", value := .sonegvnegSonegVNeg }
  , { walsCode := "baf", iso := "bfd", value := .svoButNegsnegov }
  , { walsCode := "brm", iso := "mya", value := .soNegVNeg }
  , { walsCode := "cml", iso := "rab", value := .soNegVNeg_6 }
  , { walsCode := "chb", iso := "can", value := .sovNegNegV }
  , { walsCode := "cui", iso := "cui", value := .negsoVNeg }
  , { walsCode := "dha", iso := "dsh", value := .sovNegVNeg }
  , { walsCode := "evn", iso := "eve", value := .sovNegVNeg }
  , { walsCode := "eve", iso := "evn", value := .sonegVNeg }
  , { walsCode := "fur", iso := "fvr", value := .soNegVNeg_6 }
  , { walsCode := "gwa", iso := "gbr", value := .snegovnegSnegvoneg }
  , { walsCode := "hai", iso := "hai", value := .negsoVNeg }
  , { walsCode := "ite", iso := "itl", value := .sovNegVNeg }
  , { walsCode := "kio", iso := "kio", value := .negsoVNeg }
  , { walsCode := "kis", iso := "kss", value := .snegovnegSvonegNegtone }
  , { walsCode := "kiw", iso := "kjd", value := .snegoVNegSonegVNeg }
  , { walsCode := "krw", iso := "khe", value := .soNegVNeg_6 }
  , { walsCode := "kry", iso := "kpy", value := .soNegVNeg_6 }
  , { walsCode := "lep", iso := "lep", value := .soNegVNeg_6 }
  , { walsCode := "lim", iso := "lif", value := .svOvNegVNeg_18 }
  , { walsCode := "msn", iso := "mbq", value := .sovNegvneg }
  , { walsCode := "mdn", iso := "mhq", value := .soNegVNeg_6 }
  , { walsCode := "mar", iso := "mrc", value := .soNegVNeg_6 }
  , { walsCode := "mom", iso := "mso", value := .sovNegVNeg }
  , { walsCode := "orh", iso := "hae", value := .soNegVWithNegativeToneOnVerbSoNegVNegtone }
  , { walsCode := "orw", iso := "ssn", value := .sovNegVNeg }
  , { walsCode := "pis", iso := "psa", value := .sovNegvneg }
  , { walsCode := "pso", iso := "pom", value := .sovNegVNeg }
  , { walsCode := "qhu", iso := "qub", value := .sovNegvneg }
  , { walsCode := "tbl", iso := "tnm", value := .soVNegNegOptnegprefInfix }
  , { walsCode := "tnc", iso := "tcb", value := .svOvNegVNeg }
  , { walsCode := "thu", iso := "tdh", value := .sonegVNeg }
  , { walsCode := "tig", iso := "tir", value := .soNegVNeg_6 }
  , { walsCode := "trm", iso := "suq", value := .svoButSonegVNegSoNegVNeg }
  , { walsCode := "tte", iso := "tta", value := .soNegVNeg_6 }
  , { walsCode := "tye", iso := "woa", value := .sonegvneg }
  , { walsCode := "way", iso := "oym", value := .soNegVNeg_6 }
  , { walsCode := "yqy", iso := "jaq", value := .soNegVNeg_6 }
  , { walsCode := "zun", iso := "zun", value := .negsoVNeg }
  , { walsCode := "eme", iso := "eme", value := .soNegVNeg_6 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144N
