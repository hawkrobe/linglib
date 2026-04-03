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
  | sonegvneg  -- SONegVNeg (1 languages)
  | svoButNegsnegov  -- SVO but NegSNegOV (1 languages)
  | negsoVNeg  -- NegSO[V-Neg] (4 languages)
  | sonegVNeg  -- SONeg[V-Neg] (2 languages)
  | soNegVNeg  -- SO[Neg-V]Neg (1 languages)
  | soNegVNeg_6  -- SO[Neg-V-Neg] (13 languages)
  | soNegVWithNegativeToneOnVerbSoNegVNegtone  -- SO[Neg-V] with negative tone on verb  SO[Neg-V]&NegTone (1 languages)
  | sonegvnegSonegVNeg  -- SONegVNeg/SONeg[V-Neg] (1 languages)
  | svoButSonegVNegSoNegVNeg  -- SVO but SONeg[V-Neg]/SO[Neg-V-Neg] (1 languages)
  | snegoVNegSonegVNeg  -- SNegO[V-Neg]/SONeg[V-Neg] (2 languages)
  | soVNegNegOptnegprefInfix  -- SO[V-Neg]Neg & OptNegPref/Infix (1 languages)
  | snegovnegSnegvoneg  -- SNegOVNeg/SNegVONeg (1 languages)
  | snegovnegSvonegNegtone  -- SNegOVNeg/SVONeg&NegTone (1 languages)
  | sovNegvneg  -- SOV & NegVNeg (3 languages)
  | sovNegVNeg  -- SOV & Neg[V-Neg] (7 languages)
  | sovNegNegV  -- SOV & Neg[Neg-V] (1 languages)
  | svOvNegVNeg  -- SV & OV & Neg[V-Neg] (2 languages)
  | svOvNegVNeg_18  -- SV & OV & [Neg-V-Neg] (2 languages)
  deriving DecidableEq, Repr

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

-- Count verification
theorem total_count : allData.length = 45 := by native_decide

theorem count_sonegvneg :
    (allData.filter (·.value == .sonegvneg)).length = 1 := by native_decide
theorem count_svoButNegsnegov :
    (allData.filter (·.value == .svoButNegsnegov)).length = 1 := by native_decide
theorem count_negsoVNeg :
    (allData.filter (·.value == .negsoVNeg)).length = 4 := by native_decide
theorem count_sonegVNeg :
    (allData.filter (·.value == .sonegVNeg)).length = 2 := by native_decide
theorem count_soNegVNeg :
    (allData.filter (·.value == .soNegVNeg)).length = 1 := by native_decide
theorem count_soNegVNeg_6 :
    (allData.filter (·.value == .soNegVNeg_6)).length = 13 := by native_decide
theorem count_soNegVWithNegativeToneOnVerbSoNegVNegtone :
    (allData.filter (·.value == .soNegVWithNegativeToneOnVerbSoNegVNegtone)).length = 1 := by native_decide
theorem count_sonegvnegSonegVNeg :
    (allData.filter (·.value == .sonegvnegSonegVNeg)).length = 1 := by native_decide
theorem count_svoButSonegVNegSoNegVNeg :
    (allData.filter (·.value == .svoButSonegVNegSoNegVNeg)).length = 1 := by native_decide
theorem count_snegoVNegSonegVNeg :
    (allData.filter (·.value == .snegoVNegSonegVNeg)).length = 2 := by native_decide
theorem count_soVNegNegOptnegprefInfix :
    (allData.filter (·.value == .soVNegNegOptnegprefInfix)).length = 1 := by native_decide
theorem count_snegovnegSnegvoneg :
    (allData.filter (·.value == .snegovnegSnegvoneg)).length = 1 := by native_decide
theorem count_snegovnegSvonegNegtone :
    (allData.filter (·.value == .snegovnegSvonegNegtone)).length = 1 := by native_decide
theorem count_sovNegvneg :
    (allData.filter (·.value == .sovNegvneg)).length = 3 := by native_decide
theorem count_sovNegVNeg :
    (allData.filter (·.value == .sovNegVNeg)).length = 7 := by native_decide
theorem count_sovNegNegV :
    (allData.filter (·.value == .sovNegNegV)).length = 1 := by native_decide
theorem count_svOvNegVNeg :
    (allData.filter (·.value == .svOvNegVNeg)).length = 2 := by native_decide
theorem count_svOvNegVNeg_18 :
    (allData.filter (·.value == .svOvNegVNeg_18)).length = 2 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144N
