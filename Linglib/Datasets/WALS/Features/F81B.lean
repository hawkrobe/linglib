import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 81B: Languages with two Dominant Orders of Subject, Object, and Verb
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 81B`.

Chapter 81, 67 languages.
-/

namespace Datasets.WALS.F81B

/-- WALS 81B values. -/
inductive LanguagesWithTwoDominantOrdersOfSubjectObjectAndVerb where
  /-- SOV or SVO (29 languages). -/
  | sovOrSvo
  /-- VSO or VOS (14 languages). -/
  | vsoOrVos
  /-- SVO or VSO (13 languages). -/
  | svoOrVso
  /-- SVO or VOS (8 languages). -/
  | svoOrVos
  /-- SOV or OVS (3 languages). -/
  | sovOrOvs
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 81B dataset (67 languages). -/
def allData : List (Datapoint LanguagesWithTwoDominantOrdersOfSubjectObjectAndVerb) :=
  [ { walsCode := "ajg", iso := "ajg", value := .sovOrSvo }
  , { walsCode := "ami", iso := "ami", value := .vsoOrVos }
  , { walsCode := "apl", iso := "apy", value := .sovOrOvs }
  , { walsCode := "asy", iso := "apc", value := .svoOrVso }
  , { walsCode := "arm", iso := "hye", value := .sovOrSvo }
  , { walsCode := "avo", iso := "avu", value := .sovOrSvo }
  , { walsCode := "bwc", iso := "bdr", value := .svoOrVso }
  , { walsCode := "bbu", iso := "brm", value := .svoOrVso }
  , { walsCode := "bkr", iso := "btx", value := .svoOrVso }
  , { walsCode := "bch", iso := "shy", value := .svoOrVso }
  , { walsCode := "btk", iso := "lbk", value := .svoOrVso }
  , { walsCode := "cai", iso := "suq", value := .sovOrSvo }
  , { walsCode := "ddj", iso := "god", value := .sovOrSvo }
  , { walsCode := "dam", iso := "mbp", value := .sovOrSvo }
  , { walsCode := "din", iso := "din", value := .sovOrSvo }
  , { walsCode := "dgo", iso := "doo", value := .sovOrSvo }
  , { walsCode := "dre", iso := "dhv", value := .svoOrVos }
  , { walsCode := "dut", iso := "nld", value := .sovOrSvo }
  , { walsCode := "fij", iso := "fij", value := .vsoOrVos }
  , { walsCode := "fri", iso := "fry", value := .sovOrSvo }
  , { walsCode := "grr", iso := "wrk", value := .svoOrVso }
  , { walsCode := "ger", iso := "deu", value := .sovOrSvo }
  , { walsCode := "grk", iso := "ell", value := .svoOrVso }
  , { walsCode := "gwa", iso := "gbr", value := .sovOrSvo }
  , { walsCode := "gku", iso := "pue", value := .svoOrVos }
  , { walsCode := "hun", iso := "hun", value := .sovOrSvo }
  , { walsCode := "ina", iso := "szp", value := .sovOrSvo }
  , { walsCode := "klv", iso := "kij", value := .svoOrVos }
  , { walsCode := "kis", iso := "kss", value := .sovOrSvo }
  , { walsCode := "kut", iso := "kut", value := .vsoOrVos }
  , { walsCode := "kwk", iso := "kwk", value := .svoOrVso }
  , { walsCode := "kwz", iso := "xwa", value := .sovOrSvo }
  , { walsCode := "lac", iso := "lac", value := .svoOrVos }
  , { walsCode := "ldu", iso := "led", value := .sovOrSvo }
  , { walsCode := "lgt", iso := "log", value := .sovOrSvo }
  , { walsCode := "lug", iso := "lgg", value := .sovOrSvo }
  , { walsCode := "mad", iso := "mhi", value := .sovOrSvo }
  , { walsCode := "mac", iso := "mbc", value := .sovOrOvs }
  , { walsCode := "msk", iso := "jle", value := .svoOrVso }
  , { walsCode := "meh", iso := "gdq", value := .svoOrVso }
  , { walsCode := "miy", iso := "mkf", value := .svoOrVos }
  , { walsCode := "mou", iso := "mgd", value := .sovOrSvo }
  , { walsCode := "mov", iso := "mzp", value := .vsoOrVos }
  , { walsCode := "nnc", iso := "ncb", value := .vsoOrVos }
  , { walsCode := "ney", iso := "ney", value := .sovOrSvo }
  , { walsCode := "nti", iso := "niy", value := .sovOrSvo }
  , { walsCode := "nue", iso := "nus", value := .sovOrSvo }
  , { walsCode := "nuu", iso := "nuk", value := .vsoOrVos }
  , { walsCode := "oji", iso := "", value := .vsoOrVos }
  , { walsCode := "pai", iso := "pwn", value := .vsoOrVos }
  , { walsCode := "pnx", iso := "kre", value := .sovOrSvo }
  , { walsCode := "pok", iso := "rwa", value := .sovOrSvo }
  , { walsCode := "rwe", iso := "rmw", value := .svoOrVso }
  , { walsCode := "ruk", iso := "dru", value := .vsoOrVos }
  , { walsCode := "sam", iso := "smo", value := .vsoOrVos }
  , { walsCode := "sml", iso := "sza", value := .vsoOrVos }
  , { walsCode := "shu", iso := "shs", value := .vsoOrVos }
  , { walsCode := "tee", iso := "tee", value := .svoOrVso }
  , { walsCode := "tho", iso := "thp", value := .vsoOrVos }
  , { walsCode := "tin", iso := "cir", value := .svoOrVos }
  , { walsCode := "twn", iso := "twf", value := .sovOrSvo }
  , { walsCode := "tob", iso := "tob", value := .svoOrVos }
  , { walsCode := "tng", iso := "ton", value := .vsoOrVos }
  , { walsCode := "ton", iso := "tqw", value := .sovOrSvo }
  , { walsCode := "tru", iso := "tpy", value := .sovOrSvo }
  , { walsCode := "tzu", iso := "tzj", value := .svoOrVos }
  , { walsCode := "wic", iso := "wic", value := .sovOrOvs }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F81B
