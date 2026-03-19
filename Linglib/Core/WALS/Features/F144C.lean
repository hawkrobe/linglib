/-!
# WALS Feature 144C: Languages with different word order in negative clauses
@cite{dryer-haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144C`.

Chapter 144, 28 languages.
-/

namespace Core.WALS.F144C

/-- WALS 144C values. -/
inductive LanguagesWithDifferentWordOrderInNegativeClauses where
  | vsoButNegsvo  -- VSO, but NegSVO (6 languages)
  | svoButSnegov  -- SVO, but SNegOV (3 languages)
  | svoButSonegv  -- SVO, but SONegV (1 languages)
  | svoButSovneg  -- SVO, but SOVNeg (1 languages)
  | svoButNegvso  -- SVO, but NegVSO (1 languages)
  | svoButSoVNeg  -- SVO but SO[V-Neg] (1 languages)
  | svoButSoNegV  -- SVO but SO[Neg-V] (1 languages)
  | osvButNegsvoONegVS  -- OSV but NegSVO/O[Neg-V]S (1 languages)
  | svoButNegsnegov  -- SVO, but NegSNegOV (1 languages)
  | svoButSonegVNegSoNegVNeg  -- SVO, but SONeg[V-Neg]/SO[Neg-V-Neg] (1 languages)
  | sovButSonegVNegSNegVNegO  -- SOV but  SONeg[V-Neg]/S[Neg-V-Neg] O (1 languages)
  | svoVsoButNegsvoneg  -- SVO/VSO, but NegSVONeg (1 languages)
  | svoVsoButNegVSo  -- SVO/VSO, but [Neg-V]SO(Neg) (1 languages)
  | svoSovButSvoneg  -- SVO/SOV, but SVONeg (5 languages)
  | svoSovButSnegvo  -- SVO/SOV, but SNegVO (1 languages)
  | svoSovButSnegov  -- SVO/SOV, but SNegOV (1 languages)
  | svoSovButSovneg  -- SVO/SOV, but SOVNeg (1 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 144C datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : LanguagesWithDifferentWordOrderInNegativeClauses
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 144C dataset (28 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "baf", language := "Bafut", iso := "bfd", value := .svoButNegsnegov }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .svoVsoButNegVSo }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .svoButNegvso }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .svoSovButSnegov }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .svoSovButSvoneg }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .svoButSnegov }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .vsoButNegsvo }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .svoSovButSnegvo }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .sovButSonegVNegSNegVNegO }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .svoButSnegov }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .svoButSoNegV }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .svoSovButSvoneg }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .svoSovButSvoneg }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .svoSovButSvoneg }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .vsoButNegsvo }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .vsoButNegsvo }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .vsoButNegsvo }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .svoVsoButNegsvoneg }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .svoButSnegov }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .svoButSovneg }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .svoButSoVNeg }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .svoSovButSvoneg }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .svoButSonegv }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .osvButNegsvoONegVS }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .svoSovButSovneg }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .vsoButNegsvo }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .vsoButNegsvo }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .svoButSonegVNegSoNegVNeg }
  ]

-- Count verification
theorem total_count : allData.length = 28 := by native_decide

theorem count_vsoButNegsvo :
    (allData.filter (·.value == .vsoButNegsvo)).length = 6 := by native_decide
theorem count_svoButSnegov :
    (allData.filter (·.value == .svoButSnegov)).length = 3 := by native_decide
theorem count_svoButSonegv :
    (allData.filter (·.value == .svoButSonegv)).length = 1 := by native_decide
theorem count_svoButSovneg :
    (allData.filter (·.value == .svoButSovneg)).length = 1 := by native_decide
theorem count_svoButNegvso :
    (allData.filter (·.value == .svoButNegvso)).length = 1 := by native_decide
theorem count_svoButSoVNeg :
    (allData.filter (·.value == .svoButSoVNeg)).length = 1 := by native_decide
theorem count_svoButSoNegV :
    (allData.filter (·.value == .svoButSoNegV)).length = 1 := by native_decide
theorem count_osvButNegsvoONegVS :
    (allData.filter (·.value == .osvButNegsvoONegVS)).length = 1 := by native_decide
theorem count_svoButNegsnegov :
    (allData.filter (·.value == .svoButNegsnegov)).length = 1 := by native_decide
theorem count_svoButSonegVNegSoNegVNeg :
    (allData.filter (·.value == .svoButSonegVNegSoNegVNeg)).length = 1 := by native_decide
theorem count_sovButSonegVNegSNegVNegO :
    (allData.filter (·.value == .sovButSonegVNegSNegVNegO)).length = 1 := by native_decide
theorem count_svoVsoButNegsvoneg :
    (allData.filter (·.value == .svoVsoButNegsvoneg)).length = 1 := by native_decide
theorem count_svoVsoButNegVSo :
    (allData.filter (·.value == .svoVsoButNegVSo)).length = 1 := by native_decide
theorem count_svoSovButSvoneg :
    (allData.filter (·.value == .svoSovButSvoneg)).length = 5 := by native_decide
theorem count_svoSovButSnegvo :
    (allData.filter (·.value == .svoSovButSnegvo)).length = 1 := by native_decide
theorem count_svoSovButSnegov :
    (allData.filter (·.value == .svoSovButSnegov)).length = 1 := by native_decide
theorem count_svoSovButSovneg :
    (allData.filter (·.value == .svoSovButSovneg)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F144C
