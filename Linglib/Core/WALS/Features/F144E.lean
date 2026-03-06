/-!
# WALS Feature 144E: Multiple Negative Constructions in SVO Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144E`.

Chapter 144, 48 languages.
-/

namespace Core.WALS.F144E

/-- WALS 144E values. -/
inductive MultipleNegativeConstructionsInSvoLanguages where
  | snegvoSvnego  -- SNegVO/SVNegO (5 languages)
  | negsvoSnegvo  -- NegSVO/SNegVO (3 languages)
  | negsvoSvnego  -- NegSVO/SVNegO (1 languages)
  | snegvoSvoneg  -- SNegVO/SVONeg (1 languages)
  | svnegoSvoneg  -- SVNegO/SVONeg (2 languages)
  | svoFlexibleNeg  -- SVO & Flexible Neg (1 languages)
  | snegvoSVNegO  -- SNegVO/S[V-Neg]O (2 languages)
  | sNegVOSvnego  -- S[Neg-V]O/SVNegO (2 languages)
  | negsvoSnegvoSVNegO  -- NegSVO/SNegVO/S[V-Neg]O (1 languages)
  | snegvoNegvso  -- SNegVO/NegVSO (5 languages)
  | svonegVsoneg  -- SVONeg/VSONeg (1 languages)
  | negsvoNegvos  -- NegSVO/NegVOS (1 languages)
  | snegvoNegvos  -- SNegVO/NegVOS (2 languages)
  | sNegVONegVOs  -- S[Neg-V]O/[Neg-V]OS (2 languages)
  | svonegSonegv  -- SVONeg/SONegV (2 languages)
  | svnegoSovneg  -- SVNegO/SOVNeg (1 languages)
  | svonegSnegovSovneg  -- SVONeg/SNegOV/SOVNeg (1 languages)
  | negsvoSvnegoNegsovSnegov  -- NegSVO/SVNegO/NegSOV/SNegOV (1 languages)
  | snegvoSonegvSvonegSovneg  -- SNegVO/SONegV/SVONeg/SOVNeg (1 languages)
  | sNegVOSoNegV  -- S[Neg-V]O/SO[Neg-V] (1 languages)
  | sVNegOSoVNeg  -- S[V-Neg]O/SO[V-Neg] (2 languages)
  | snegvoSonegvSNegVOSoNegV  -- SNegVO/SONegV/S[Neg-V]O/SO[Neg-V] (1 languages)
  | negsvoONegVS  -- NegSVO/O[Neg-V]S (1 languages)
  | svoNegvVneg  -- SVO & NegV/VNeg (1 languages)
  | svoNegvVNeg  -- SVO & NegV/[V-Neg] (2 languages)
  | svoVsoNegv  -- SVO/VSO & NegV (2 languages)
  | svoVosNegv  -- SVO/VOS & NegV (2 languages)
  | svoSovNegvVneg  -- SVO/SOV & NegV/VNeg (1 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144E datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : MultipleNegativeConstructionsInSvoLanguages
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144E dataset (48 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "acl", language := "Acholi", iso := "ach", value := .svoNegvVneg }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .snegvoSvnego }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .svoSovNegvVneg }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .negsvoSnegvo }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .snegvoNegvso }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .snegvoSonegvSNegVOSoNegV }
  , { walsCode := "au", language := "Au", iso := "avt", value := .snegvoSvoneg }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .svoVsoNegv }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .snegvoNegvso }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .snegvoNegvso }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .svoFlexibleNeg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .svoVsoNegv }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .snegvoSonegvSvonegSovneg }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .snegvoSvnego }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .negsvoNegvos }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .svonegSonegv }
  , { walsCode := "ger", language := "German", iso := "deu", value := .svonegSonegv }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .snegvoNegvso }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .sNegVONegVOs }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .snegvoSvnego }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .svoVosNegv }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .svoNegvVNeg }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .sVNegOSoVNeg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .svoVosNegv }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .svonegSnegovSovneg }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .negsvoSnegvo }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .negsvoSvnego }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .svnegoSvoneg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .svonegVsoneg }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .svoNegvVNeg }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .negsvoSnegvo }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .negsvoONegVS }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .negsvoSvnegoNegsovSnegov }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .sNegVOSvnego }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .snegvoSvnego }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .sNegVOSvnego }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .negsvoSnegvoSVNegO }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .svnegoSvoneg }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .snegvoSvnego }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .snegvoNegvso }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .snegvoNegvos }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .sNegVOSoNegV }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .sNegVONegVOs }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .sVNegOSoVNeg }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .svnegoSovneg }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .snegvoNegvos }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .snegvoSVNegO }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .snegvoSVNegO }
  ]

-- Count verification
theorem total_count : allData.length = 48 := by native_decide

theorem count_snegvoSvnego :
    (allData.filter (·.value == .snegvoSvnego)).length = 5 := by native_decide
theorem count_negsvoSnegvo :
    (allData.filter (·.value == .negsvoSnegvo)).length = 3 := by native_decide
theorem count_negsvoSvnego :
    (allData.filter (·.value == .negsvoSvnego)).length = 1 := by native_decide
theorem count_snegvoSvoneg :
    (allData.filter (·.value == .snegvoSvoneg)).length = 1 := by native_decide
theorem count_svnegoSvoneg :
    (allData.filter (·.value == .svnegoSvoneg)).length = 2 := by native_decide
theorem count_svoFlexibleNeg :
    (allData.filter (·.value == .svoFlexibleNeg)).length = 1 := by native_decide
theorem count_snegvoSVNegO :
    (allData.filter (·.value == .snegvoSVNegO)).length = 2 := by native_decide
theorem count_sNegVOSvnego :
    (allData.filter (·.value == .sNegVOSvnego)).length = 2 := by native_decide
theorem count_negsvoSnegvoSVNegO :
    (allData.filter (·.value == .negsvoSnegvoSVNegO)).length = 1 := by native_decide
theorem count_snegvoNegvso :
    (allData.filter (·.value == .snegvoNegvso)).length = 5 := by native_decide
theorem count_svonegVsoneg :
    (allData.filter (·.value == .svonegVsoneg)).length = 1 := by native_decide
theorem count_negsvoNegvos :
    (allData.filter (·.value == .negsvoNegvos)).length = 1 := by native_decide
theorem count_snegvoNegvos :
    (allData.filter (·.value == .snegvoNegvos)).length = 2 := by native_decide
theorem count_sNegVONegVOs :
    (allData.filter (·.value == .sNegVONegVOs)).length = 2 := by native_decide
theorem count_svonegSonegv :
    (allData.filter (·.value == .svonegSonegv)).length = 2 := by native_decide
theorem count_svnegoSovneg :
    (allData.filter (·.value == .svnegoSovneg)).length = 1 := by native_decide
theorem count_svonegSnegovSovneg :
    (allData.filter (·.value == .svonegSnegovSovneg)).length = 1 := by native_decide
theorem count_negsvoSvnegoNegsovSnegov :
    (allData.filter (·.value == .negsvoSvnegoNegsovSnegov)).length = 1 := by native_decide
theorem count_snegvoSonegvSvonegSovneg :
    (allData.filter (·.value == .snegvoSonegvSvonegSovneg)).length = 1 := by native_decide
theorem count_sNegVOSoNegV :
    (allData.filter (·.value == .sNegVOSoNegV)).length = 1 := by native_decide
theorem count_sVNegOSoVNeg :
    (allData.filter (·.value == .sVNegOSoVNeg)).length = 2 := by native_decide
theorem count_snegvoSonegvSNegVOSoNegV :
    (allData.filter (·.value == .snegvoSonegvSNegVOSoNegV)).length = 1 := by native_decide
theorem count_negsvoONegVS :
    (allData.filter (·.value == .negsvoONegVS)).length = 1 := by native_decide
theorem count_svoNegvVneg :
    (allData.filter (·.value == .svoNegvVneg)).length = 1 := by native_decide
theorem count_svoNegvVNeg :
    (allData.filter (·.value == .svoNegvVNeg)).length = 2 := by native_decide
theorem count_svoVsoNegv :
    (allData.filter (·.value == .svoVsoNegv)).length = 2 := by native_decide
theorem count_svoVosNegv :
    (allData.filter (·.value == .svoVosNegv)).length = 2 := by native_decide
theorem count_svoSovNegvVneg :
    (allData.filter (·.value == .svoSovNegvVneg)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144E
