import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144Y: The Position of Negative Morphemes in Object-Initial Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144Y`.

Chapter 144, 16 languages.
-/

namespace Core.WALS.F144Y

/-- WALS 144Y values. -/
inductive PositionOfNegativeMorphemesInObjectInitialLanguages where
  | onegvs  -- ONegVS (3 languages)
  | ovnegs  -- OVNegS (1 languages)
  | osvneg  -- OSVNeg (1 languages)
  | oVNegS  -- O[V-Neg]S (4 languages)
  | osV  -- OS(Neg)[V(-Neg)] (1 languages)
  | oNegVNegS  -- O[Neg-V-Neg]S (1 languages)
  | ovnegsSovneg  -- OVNegS/SOVNeg (1 languages)
  | negovsNegsov  -- NegOVS/NegSOV (1 languages)
  | oVNegSSoVNeg  -- O[V-Neg]S/SO[V-Neg] (1 languages)
  | oNegVSNegsvo  -- O[Neg-V]S/NegSVO (1 languages)
  | ovsNegv  -- OVS & NegV (1 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144Y dataset (16 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInObjectInitialLanguages) :=
  [ { walsCode := "apl", language := "Apalaí", iso := "apy", value := .oVNegSSoVNeg }
  , { walsCode := "asu", language := "Asuriní", iso := "asu", value := .oNegVNegS }
  , { walsCode := "cub", language := "Cubeo", iso := "cub", value := .oVNegS }
  , { walsCode := "hix", language := "Hixkaryana", iso := "hix", value := .oVNegS }
  , { walsCode := "kxo", language := "Kxoe", iso := "xuu", value := .osvneg }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .ovnegsSovneg }
  , { walsCode := "myi", language := "Mangarrayi", iso := "mpc", value := .onegvs }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .oNegVSNegsvo }
  , { walsCode := "par", language := "Päri", iso := "lkr", value := .ovsNegv }
  , { walsCode := "sel", language := "Selknam", iso := "ona", value := .ovnegs }
  , { walsCode := "tir", language := "Tiriyo", iso := "tri", value := .oVNegS }
  , { walsCode := "tbt", language := "Tobati", iso := "tti", value := .osV }
  , { walsCode := "tvl", language := "Tuvaluan", iso := "tvl", value := .onegvs }
  , { walsCode := "ung", language := "Ungarinjin", iso := "ung", value := .onegvs }
  , { walsCode := "urn", language := "Urarina", iso := "ura", value := .oVNegS }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .negovsNegsov }
  ]

-- Count verification
theorem total_count : allData.length = 16 := by native_decide

theorem count_onegvs :
    (allData.filter (·.value == .onegvs)).length = 3 := by native_decide
theorem count_ovnegs :
    (allData.filter (·.value == .ovnegs)).length = 1 := by native_decide
theorem count_osvneg :
    (allData.filter (·.value == .osvneg)).length = 1 := by native_decide
theorem count_oVNegS :
    (allData.filter (·.value == .oVNegS)).length = 4 := by native_decide
theorem count_osV :
    (allData.filter (·.value == .osV)).length = 1 := by native_decide
theorem count_oNegVNegS :
    (allData.filter (·.value == .oNegVNegS)).length = 1 := by native_decide
theorem count_ovnegsSovneg :
    (allData.filter (·.value == .ovnegsSovneg)).length = 1 := by native_decide
theorem count_negovsNegsov :
    (allData.filter (·.value == .negovsNegsov)).length = 1 := by native_decide
theorem count_oVNegSSoVNeg :
    (allData.filter (·.value == .oVNegSSoVNeg)).length = 1 := by native_decide
theorem count_oNegVSNegsvo :
    (allData.filter (·.value == .oNegVSNegsvo)).length = 1 := by native_decide
theorem count_ovsNegv :
    (allData.filter (·.value == .ovsNegv)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144Y
