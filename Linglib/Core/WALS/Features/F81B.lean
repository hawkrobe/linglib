import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 81B: Languages with two Dominant Orders of Subject, Object, and Verb
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 81B`.

Chapter 81, 67 languages.
-/

namespace Core.WALS.F81B

/-- WALS 81B values. -/
inductive LanguagesWithTwoDominantOrdersOfSubjectObjectAndVerb where
  | sovOrSvo  -- SOV or SVO (29 languages)
  | vsoOrVos  -- VSO or VOS (14 languages)
  | svoOrVso  -- SVO or VSO (13 languages)
  | svoOrVos  -- SVO or VOS (8 languages)
  | sovOrOvs  -- SOV or OVS (3 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 81B dataset (67 languages). -/
def allData : List (Datapoint LanguagesWithTwoDominantOrdersOfSubjectObjectAndVerb) :=
  [ { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .sovOrSvo }
  , { walsCode := "ami", language := "Amis", iso := "ami", value := .vsoOrVos }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .sovOrOvs }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .svoOrVso }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .sovOrSvo }
  , { walsCode := "avo", language := "Avokaya", iso := "avu", value := .sovOrSvo }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .svoOrVso }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .svoOrVso }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .svoOrVso }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .svoOrVso }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .svoOrVso }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .sovOrSvo }
  , { walsCode := "ddj", language := "Dadjriwalé", iso := "god", value := .sovOrSvo }
  , { walsCode := "dam", language := "Damana", iso := "mbp", value := .sovOrSvo }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .sovOrSvo }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .sovOrSvo }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .svoOrVos }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .sovOrSvo }
  , { walsCode := "fij", language := "Fijian", iso := "fij", value := .vsoOrVos }
  , { walsCode := "fri", language := "Frisian", iso := "fry", value := .sovOrSvo }
  , { walsCode := "grr", language := "Garrwa", iso := "wrk", value := .svoOrVso }
  , { walsCode := "ger", language := "German", iso := "deu", value := .sovOrSvo }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .svoOrVso }
  , { walsCode := "gwa", language := "Gwari", iso := "gbr", value := .sovOrSvo }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .svoOrVos }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .sovOrSvo }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .sovOrSvo }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .svoOrVos }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .sovOrSvo }
  , { walsCode := "kut", language := "Kutenai", iso := "kut", value := .vsoOrVos }
  , { walsCode := "kwk", language := "Kwakw'ala", iso := "kwk", value := .svoOrVso }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .sovOrSvo }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .svoOrVos }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .sovOrSvo }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .sovOrSvo }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .sovOrSvo }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .sovOrSvo }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .sovOrOvs }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .svoOrVso }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .svoOrVso }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .svoOrVos }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .sovOrSvo }
  , { walsCode := "mov", language := "Movima", iso := "mzp", value := .vsoOrVos }
  , { walsCode := "nnc", language := "Nancowry", iso := "ncb", value := .vsoOrVos }
  , { walsCode := "ney", language := "Neyo", iso := "ney", value := .sovOrSvo }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .sovOrSvo }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .sovOrSvo }
  , { walsCode := "nuu", language := "Nuuchahnulth", iso := "nuk", value := .vsoOrVos }
  , { walsCode := "oji", language := "Ojibwa (Eastern)", iso := "", value := .vsoOrVos }
  , { walsCode := "pai", language := "Paiwan", iso := "pwn", value := .vsoOrVos }
  , { walsCode := "pnx", language := "Panará", iso := "kre", value := .sovOrSvo }
  , { walsCode := "pok", language := "Poko-Rawo", iso := "rwa", value := .sovOrSvo }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .svoOrVso }
  , { walsCode := "ruk", language := "Rukai (Tanan)", iso := "dru", value := .vsoOrVos }
  , { walsCode := "sam", language := "Samoan", iso := "smo", value := .vsoOrVos }
  , { walsCode := "sml", language := "Semelai", iso := "sza", value := .vsoOrVos }
  , { walsCode := "shu", language := "Shuswap", iso := "shs", value := .vsoOrVos }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .svoOrVso }
  , { walsCode := "tho", language := "Thompson", iso := "thp", value := .vsoOrVos }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .svoOrVos }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .sovOrSvo }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .svoOrVos }
  , { walsCode := "tng", language := "Tongan", iso := "ton", value := .vsoOrVos }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .sovOrSvo }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .sovOrSvo }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .svoOrVos }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .sovOrOvs }
  ]

-- Count verification
theorem total_count : allData.length = 67 := by native_decide

theorem count_sovOrSvo :
    (allData.filter (·.value == .sovOrSvo)).length = 29 := by native_decide
theorem count_vsoOrVos :
    (allData.filter (·.value == .vsoOrVos)).length = 14 := by native_decide
theorem count_svoOrVso :
    (allData.filter (·.value == .svoOrVso)).length = 13 := by native_decide
theorem count_svoOrVos :
    (allData.filter (·.value == .svoOrVos)).length = 8 := by native_decide
theorem count_sovOrOvs :
    (allData.filter (·.value == .sovOrOvs)).length = 3 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F81B
