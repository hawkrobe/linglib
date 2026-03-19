import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 143B: Obligatory Double Negation
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143B`.

Chapter 143, 119 languages.
-/

namespace Core.WALS.F143B

/-- WALS 143B values. -/
inductive ObligatoryDoubleNegation where
  | negvneg  -- NegVNeg (35 languages)
  | negVNeg  -- Neg[V-Neg] (28 languages)
  | negVNeg_3  -- [Neg-V]Neg (9 languages)
  | negVNeg_4  -- [Neg-V-Neg] (27 languages)
  | negativeToneVneg  -- Negative tone & VNeg (1 languages)
  | negativeToneNegV  -- Negative tone & [Neg-V] (2 languages)
  | negnegv  -- NegNegV (2 languages)
  | negNegV  -- Neg[Neg-V] (2 languages)
  | vnegneg  -- VNegNeg (2 languages)
  | type1Type2  -- Type 1 / Type 2 (1 languages)
  | type1Type3  -- Type 1 / Type 3 (1 languages)
  | type1Type5  -- Type 1 / Type 5 (1 languages)
  | type1Type7  -- Type 1 / Type 7 (1 languages)
  | type1Type9  -- Type 1 / Type 9 (1 languages)
  | type2Type4  -- Type 2 / Type 4 (1 languages)
  | obligdoublenegOpttripleneg  -- ObligDoubleNeg&OptTripleNeg (5 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 143B dataset (119 languages). -/
def allData : List (Datapoint ObligatoryDoubleNegation) :=
  [ { walsCode := "abu", language := "Abun", iso := "kgr", value := .negvneg }
  , { walsCode := "amn", language := "Amanab", iso := "amn", value := .negVNeg }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .negvneg }
  , { walsCode := "amh", language := "Amharic", iso := "amh", value := .negVNeg_4 }
  , { walsCode := "amo", language := "Amo", iso := "amo", value := .negvneg }
  , { walsCode := "amx", language := "Anamuxra", iso := "imi", value := .negVNeg }
  , { walsCode := "apw", language := "Apache (Western)", iso := "apw", value := .negVNeg }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .negVNeg_4 }
  , { walsCode := "ana", language := "Araona", iso := "aro", value := .negVNeg_4 }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .negVNeg_4 }
  , { walsCode := "awp", language := "Awa Pit", iso := "kwi", value := .type1Type2 }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .negvneg }
  , { walsCode := "baf", language := "Bafut", iso := "bfd", value := .negnegv }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .negativeToneVneg }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .negvneg }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .negvneg }
  , { walsCode := "bbf", language := "Bobo Madaré (Northern)", iso := "bbo", value := .negvneg }
  , { walsCode := "boi", language := "Boiken", iso := "bzf", value := .negVNeg }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .type1Type7 }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .negvneg }
  , { walsCode := "brm", language := "Burmese", iso := "mya", value := .negVNeg_3 }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .negvneg }
  , { walsCode := "cml", language := "Camling", iso := "rab", value := .negVNeg_4 }
  , { walsCode := "chb", language := "Chambri", iso := "can", value := .negNegV }
  , { walsCode := "cui", language := "Cuiba", iso := "cui", value := .negVNeg }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .negativeToneNegV }
  , { walsCode := "dha", language := "Dhaasanac", iso := "dsh", value := .negVNeg }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .obligdoublenegOpttripleneg }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .negvneg }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .negVNeg_4 }
  , { walsCode := "evn", language := "Even", iso := "eve", value := .negVNeg }
  , { walsCode := "eve", language := "Evenki", iso := "evn", value := .negVNeg }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .negvneg }
  , { walsCode := "fur", language := "Fur", iso := "fvr", value := .negVNeg_4 }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .negvneg }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .obligdoublenegOpttripleneg }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .negvneg }
  , { walsCode := "hai", language := "Haida", iso := "hai", value := .negVNeg }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .negvneg }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vnegneg }
  , { walsCode := "ido", language := "Idoma", iso := "idu", value := .negvneg }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .negvneg }
  , { walsCode := "ite", language := "Itelmen", iso := "itl", value := .negVNeg }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .negVNeg_3 }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .negVNeg }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .negvneg }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .negvneg }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .negVNeg_3 }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .negvneg }
  , { walsCode := "krk", language := "Karok", iso := "kyh", value := .negVNeg }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .negvneg }
  , { walsCode := "kio", language := "Kiowa", iso := "kio", value := .negVNeg }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .type1Type5 }
  , { walsCode := "kiw", language := "Kiwai (Southern)", iso := "kjd", value := .negVNeg }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .obligdoublenegOpttripleneg }
  , { walsCode := "krw", language := "Korowai", iso := "khe", value := .negVNeg_4 }
  , { walsCode := "kry", language := "Koryak", iso := "kpy", value := .negVNeg_4 }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .negvneg }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .negvneg }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .negVNeg_3 }
  , { walsCode := "lng", language := "Lengua", iso := "enx", value := .negVNeg_4 }
  , { walsCode := "lep", language := "Lepcha", iso := "lep", value := .negVNeg_4 }
  , { walsCode := "lim", language := "Limbu", iso := "lif", value := .negVNeg_4 }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .negVNeg_3 }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .negvneg }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .negVNeg_3 }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .type1Type3 }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .negVNeg_3 }
  , { walsCode := "msn", language := "Maisin", iso := "mbq", value := .negvneg }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .negVNeg_4 }
  , { walsCode := "mdn", language := "Mandan", iso := "mhq", value := .negVNeg_4 }
  , { walsCode := "mar", language := "Maricopa", iso := "mrc", value := .negVNeg_4 }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .negvneg }
  , { walsCode := "mbl", language := "Mbole", iso := "mdq", value := .negVNeg_4 }
  , { walsCode := "men", language := "Menomini", iso := "mez", value := .negVNeg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .type1Type9 }
  , { walsCode := "mom", language := "Mombum", iso := "mso", value := .negVNeg }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .negvneg }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .negvneg }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .negVNeg }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .negVNeg_4 }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .negVNeg_3 }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .obligdoublenegOpttripleneg }
  , { walsCode := "orh", language := "Oromo (Harar)", iso := "hae", value := .negativeToneNegV }
  , { walsCode := "orw", language := "Oromo (Waata)", iso := "ssn", value := .negVNeg }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .negvneg }
  , { walsCode := "psm", language := "Passamaquoddy-Maliseet", iso := "pqm", value := .negVNeg }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .negvneg }
  , { walsCode := "pis", language := "Pisa", iso := "psa", value := .negvneg }
  , { walsCode := "pso", language := "Pomo (Southeastern)", iso := "pom", value := .negVNeg }
  , { walsCode := "qhu", language := "Quechua (Huallaga)", iso := "qub", value := .negvneg }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .negvneg }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .negvneg }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .negNegV }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .negVNeg_3 }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .negVNeg }
  , { walsCode := "sub", language := "Subiya", iso := "sbs", value := .negVNeg_4 }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .negVNeg_4 }
  , { walsCode := "swt", language := "Swati", iso := "ssw", value := .negVNeg_4 }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .obligdoublenegOpttripleneg }
  , { walsCode := "tnc", language := "Tanacross", iso := "tcb", value := .negVNeg }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .negvneg }
  , { walsCode := "thu", language := "Thulung", iso := "tdh", value := .negVNeg }
  , { walsCode := "tig", language := "Tigrinya", iso := "tir", value := .negVNeg_4 }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .type2Type4 }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .negnegv }
  , { walsCode := "tte", language := "Tutelo", iso := "tta", value := .negVNeg_4 }
  , { walsCode := "tye", language := "Tyeraity", iso := "woa", value := .negvneg }
  , { walsCode := "ute", language := "Ute", iso := "ute", value := .negVNeg_4 }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .negVNeg_4 }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .negVNeg }
  , { walsCode := "way", language := "Wayampi", iso := "oym", value := .negVNeg_4 }
  , { walsCode := "win", language := "Wintu", iso := "wnw", value := .negVNeg }
  , { walsCode := "yqy", language := "Yaqay", iso := "jaq", value := .negVNeg_4 }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .negVNeg }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .vnegneg }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .negVNeg }
  , { walsCode := "zun", language := "Zuni", iso := "zun", value := .negVNeg }
  , { walsCode := "eme", language := "Émérillon", iso := "eme", value := .negVNeg_4 }
  ]

-- Count verification
theorem total_count : allData.length = 119 := by native_decide

theorem count_negvneg :
    (allData.filter (·.value == .negvneg)).length = 35 := by native_decide
theorem count_negVNeg :
    (allData.filter (·.value == .negVNeg)).length = 28 := by native_decide
theorem count_negVNeg_3 :
    (allData.filter (·.value == .negVNeg_3)).length = 9 := by native_decide
theorem count_negVNeg_4 :
    (allData.filter (·.value == .negVNeg_4)).length = 27 := by native_decide
theorem count_negativeToneVneg :
    (allData.filter (·.value == .negativeToneVneg)).length = 1 := by native_decide
theorem count_negativeToneNegV :
    (allData.filter (·.value == .negativeToneNegV)).length = 2 := by native_decide
theorem count_negnegv :
    (allData.filter (·.value == .negnegv)).length = 2 := by native_decide
theorem count_negNegV :
    (allData.filter (·.value == .negNegV)).length = 2 := by native_decide
theorem count_vnegneg :
    (allData.filter (·.value == .vnegneg)).length = 2 := by native_decide
theorem count_type1Type2 :
    (allData.filter (·.value == .type1Type2)).length = 1 := by native_decide
theorem count_type1Type3 :
    (allData.filter (·.value == .type1Type3)).length = 1 := by native_decide
theorem count_type1Type5 :
    (allData.filter (·.value == .type1Type5)).length = 1 := by native_decide
theorem count_type1Type7 :
    (allData.filter (·.value == .type1Type7)).length = 1 := by native_decide
theorem count_type1Type9 :
    (allData.filter (·.value == .type1Type9)).length = 1 := by native_decide
theorem count_type2Type4 :
    (allData.filter (·.value == .type2Type4)).length = 1 := by native_decide
theorem count_obligdoublenegOpttripleneg :
    (allData.filter (·.value == .obligdoublenegOpttripleneg)).length = 5 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143B
