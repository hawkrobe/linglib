/-!
# WALS Feature 144F: Obligatory Double Negation in SVO languages
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144F`.

Chapter 144, 56 languages.
-/

namespace Core.WALS.F144F

/-- WALS 144F values. -/
inductive ObligatoryDoubleNegationInSvoLanguages where
  | snegvoneg  -- SNegVONeg (11 languages)
  | snegvnego  -- SNegVNegO (6 languages)
  | svnegoneg  -- SVNegONeg (1 languages)
  | svoVsoButNegsvoneg  -- SVO/VSO but NegSVONeg (1 languages)
  | sNegVOneg  -- S[Neg-V]ONeg (7 languages)
  | snegVNegO  -- SNeg[V-Neg]O (4 languages)
  | sNegVNego  -- S[Neg-V]NegO (1 languages)
  | negsVNegO  -- NegS[V-Neg]O (2 languages)
  | sNegVNegO  -- S[Neg-V-Neg]O (5 languages)
  | svnegoNegtone  -- SVNegO&NegTone (1 languages)
  | sNegVONegtone  -- S[Neg-V]O&NegTone (1 languages)
  | snegnegvoSnegvnego  -- SNegNegVO/SNegVNegO (1 languages)
  | snegvnegoSnegvoneg  -- SNegVNegO/SNegVONeg (1 languages)
  | snegvonegSNegVOneg  -- SNegVONeg/S[Neg-V]ONeg (1 languages)
  | svoneg  -- (Neg)S(Neg)VONeg (1 languages)
  | snegVNegONegtoneSnegvnego  -- SNeg[V-Neg]O&NegTone/SNegVNegO (1 languages)
  | sNegVNegO_17  -- S(Neg)[Neg-V-Neg]O (1 languages)
  | snegVOnegSNegVOneg  -- SNeg[V(-Neg)]ONeg/S[Neg-V(-Neg)]ONeg (1 languages)
  | snegvonegSnegovneg  -- SNegVONeg/SNegOVNeg (1 languages)
  | svonegNegtoneSnegovneg  -- SVONeg&NegTone/SNegOVNeg (1 languages)
  | snegvonegSvnegonegNegvosnegVnegosneg  -- SNegVONeg/SVNegONeg/NegVOSNeg/VNegOSNeg (1 languages)
  | svoNegvneg  -- SVO & NegVNeg (5 languages)
  | sNegVONegv  -- S[Neg-V]O & NegV (1 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144F datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : ObligatoryDoubleNegationInSvoLanguages
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144F dataset (56 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "abu", language := "Abun", iso := "kgr", value := .snegvoneg }
  , { walsCode := "aml", language := "Ambae (Lolovoli Northeast)", iso := "omb", value := .snegvnegoSnegvoneg }
  , { walsCode := "bab", language := "Babungo", iso := "bav", value := .snegvoneg }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .svnegoNegtone }
  , { walsCode := "bid", language := "Bidiya", iso := "bid", value := .svoNegvneg }
  , { walsCode := "bob", language := "Bobangi", iso := "bni", value := .snegvoneg }
  , { walsCode := "bre", language := "Breton", iso := "bre", value := .snegnegvoSnegvnego }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .snegvoneg }
  , { walsCode := "deg", language := "Degema", iso := "deg", value := .sNegVONegtone }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .snegVNegONegtoneSnegvnego }
  , { walsCode := "erk", language := "Efate (South)", iso := "erk", value := .snegvoneg }
  , { walsCode := "eko", language := "Ekoti", iso := "eko", value := .sNegVNegO }
  , { walsCode := "ewe", language := "Ewe", iso := "ewe", value := .snegvoneg }
  , { walsCode := "gua", language := "Guaraní", iso := "gug", value := .snegvnego }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .sNegVNegO_17 }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .snegvonegSnegovneg }
  , { walsCode := "hal", language := "Halia", iso := "hla", value := .snegvnego }
  , { walsCode := "ifm", language := "Ifumu", iso := "ifm", value := .svoNegvneg }
  , { walsCode := "kwy", language := "Iwoyo", iso := "yom", value := .sNegVOneg }
  , { walsCode := "izi", language := "Izi", iso := "izz", value := .snegVNegO }
  , { walsCode := "knk", language := "Kanakuru", iso := "kna", value := .snegvoneg }
  , { walsCode := "kbw", language := "Karen (Bwe)", iso := "bwe", value := .sNegVOneg }
  , { walsCode := "ksg", language := "Karen (Sgaw)", iso := "ksw", value := .snegvoneg }
  , { walsCode := "ktl", language := "Katla", iso := "kcr", value := .snegvnego }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .svonegNegtoneSnegovneg }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .snegVOnegSNegVOneg }
  , { walsCode := "lmu", language := "Lamen", iso := "lmu", value := .snegvnego }
  , { walsCode := "len", language := "Lenakel", iso := "tnl", value := .sNegVNego }
  , { walsCode := "lnd", language := "Linda", iso := "liy", value := .sNegVOneg }
  , { walsCode := "lou", language := "Lou", iso := "loj", value := .snegvoneg }
  , { walsCode := "lbu", language := "Lunda", iso := "lun", value := .sNegVOneg }
  , { walsCode := "luv", language := "Luvale", iso := "lue", value := .snegvonegSNegVOneg }
  , { walsCode := "ma", language := "Ma", iso := "msj", value := .sNegVOneg }
  , { walsCode := "mkz", language := "Makaa", iso := "mcp", value := .sNegVNegO }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .svoVsoButNegsvoneg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .snegvonegSvnegonegNegvosnegVnegosneg }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .snegvoneg }
  , { walsCode := "aoj", language := "Mufian", iso := "aoj", value := .svoNegvneg }
  , { walsCode := "mwo", language := "Mwotlap", iso := "mlv", value := .snegVNegO }
  , { walsCode := "ndb", language := "Ndebele", iso := "nde", value := .sNegVNegO }
  , { walsCode := "ndu", language := "Ndumu", iso := "nmd", value := .sNegVOneg }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .svoneg }
  , { walsCode := "otr", language := "Otoro", iso := "otr", value := .svoNegvneg }
  , { walsCode := "per", language := "Pero", iso := "pip", value := .snegvoneg }
  , { walsCode := "rag", language := "Raga", iso := "lml", value := .svoNegvneg }
  , { walsCode := "rot", language := "Rotuman", iso := "rtm", value := .snegvnego }
  , { walsCode := "sal", language := "Salinan", iso := "sln", value := .sNegVONegv }
  , { walsCode := "sgl", language := "Sengele", iso := "szg", value := .sNegVOneg }
  , { walsCode := "stn", language := "Sotho (Northern)", iso := "nso", value := .snegVNegO }
  , { walsCode := "skm", language := "Sukuma", iso := "suk", value := .sNegVNegO }
  , { walsCode := "teo", language := "Teop", iso := "tio", value := .snegvnego }
  , { walsCode := "vnm", language := "Vinmavis", iso := "vnm", value := .sNegVNegO }
  , { walsCode := "wrk", language := "Warekena", iso := "gae", value := .snegVNegO }
  , { walsCode := "yuk", language := "Yukulta", iso := "gcd", value := .negsVNegO }
  , { walsCode := "zan", language := "Zande", iso := "zne", value := .svnegoneg }
  , { walsCode := "zpr", language := "Zaparo", iso := "zro", value := .negsVNegO }
  ]

-- Count verification
theorem total_count : allData.length = 56 := by native_decide

theorem count_snegvoneg :
    (allData.filter (·.value == .snegvoneg)).length = 11 := by native_decide
theorem count_snegvnego :
    (allData.filter (·.value == .snegvnego)).length = 6 := by native_decide
theorem count_svnegoneg :
    (allData.filter (·.value == .svnegoneg)).length = 1 := by native_decide
theorem count_svoVsoButNegsvoneg :
    (allData.filter (·.value == .svoVsoButNegsvoneg)).length = 1 := by native_decide
theorem count_sNegVOneg :
    (allData.filter (·.value == .sNegVOneg)).length = 7 := by native_decide
theorem count_snegVNegO :
    (allData.filter (·.value == .snegVNegO)).length = 4 := by native_decide
theorem count_sNegVNego :
    (allData.filter (·.value == .sNegVNego)).length = 1 := by native_decide
theorem count_negsVNegO :
    (allData.filter (·.value == .negsVNegO)).length = 2 := by native_decide
theorem count_sNegVNegO :
    (allData.filter (·.value == .sNegVNegO)).length = 5 := by native_decide
theorem count_svnegoNegtone :
    (allData.filter (·.value == .svnegoNegtone)).length = 1 := by native_decide
theorem count_sNegVONegtone :
    (allData.filter (·.value == .sNegVONegtone)).length = 1 := by native_decide
theorem count_snegnegvoSnegvnego :
    (allData.filter (·.value == .snegnegvoSnegvnego)).length = 1 := by native_decide
theorem count_snegvnegoSnegvoneg :
    (allData.filter (·.value == .snegvnegoSnegvoneg)).length = 1 := by native_decide
theorem count_snegvonegSNegVOneg :
    (allData.filter (·.value == .snegvonegSNegVOneg)).length = 1 := by native_decide
theorem count_svoneg :
    (allData.filter (·.value == .svoneg)).length = 1 := by native_decide
theorem count_snegVNegONegtoneSnegvnego :
    (allData.filter (·.value == .snegVNegONegtoneSnegvnego)).length = 1 := by native_decide
theorem count_sNegVNegO_17 :
    (allData.filter (·.value == .sNegVNegO_17)).length = 1 := by native_decide
theorem count_snegVOnegSNegVOneg :
    (allData.filter (·.value == .snegVOnegSNegVOneg)).length = 1 := by native_decide
theorem count_snegvonegSnegovneg :
    (allData.filter (·.value == .snegvonegSnegovneg)).length = 1 := by native_decide
theorem count_svonegNegtoneSnegovneg :
    (allData.filter (·.value == .svonegNegtoneSnegovneg)).length = 1 := by native_decide
theorem count_snegvonegSvnegonegNegvosnegVnegosneg :
    (allData.filter (·.value == .snegvonegSvnegonegNegvosnegVnegosneg)).length = 1 := by native_decide
theorem count_svoNegvneg :
    (allData.filter (·.value == .svoNegvneg)).length = 5 := by native_decide
theorem count_sNegVONegv :
    (allData.filter (·.value == .sNegVONegv)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144F
