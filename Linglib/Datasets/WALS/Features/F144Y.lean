import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144Y: The Position of Negative Morphemes in Object-Initial Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144Y`.

Chapter 144, 16 languages.
-/

namespace Datasets.WALS.F144Y

/-- WALS 144Y values. -/
inductive PositionOfNegativeMorphemesInObjectInitialLanguages where
  /-- ONegVS (3 languages). -/
  | onegvs
  /-- OVNegS (1 languages). -/
  | ovnegs
  /-- OSVNeg (1 languages). -/
  | osvneg
  /-- O[V-Neg]S (4 languages). -/
  | oVNegS
  /-- OS(Neg)[V(-Neg)] (1 languages). -/
  | osV
  /-- O[Neg-V-Neg]S (1 languages). -/
  | oNegVNegS
  /-- OVNegS/SOVNeg (1 languages). -/
  | ovnegsSovneg
  /-- NegOVS/NegSOV (1 languages). -/
  | negovsNegsov
  /-- O[V-Neg]S/SO[V-Neg] (1 languages). -/
  | oVNegSSoVNeg
  /-- O[Neg-V]S/NegSVO (1 languages). -/
  | oNegVSNegsvo
  /-- OVS & NegV (1 languages). -/
  | ovsNegv
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144Y dataset (16 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInObjectInitialLanguages) :=
  [ { walsCode := "apl", iso := "apy", value := .oVNegSSoVNeg }
  , { walsCode := "asu", iso := "asu", value := .oNegVNegS }
  , { walsCode := "cub", iso := "cub", value := .oVNegS }
  , { walsCode := "hix", iso := "hix", value := .oVNegS }
  , { walsCode := "kxo", iso := "xuu", value := .osvneg }
  , { walsCode := "mac", iso := "mbc", value := .ovnegsSovneg }
  , { walsCode := "myi", iso := "mpc", value := .onegvs }
  , { walsCode := "nad", iso := "mbj", value := .oNegVSNegsvo }
  , { walsCode := "par", iso := "lkr", value := .ovsNegv }
  , { walsCode := "sel", iso := "ona", value := .ovnegs }
  , { walsCode := "tir", iso := "tri", value := .oVNegS }
  , { walsCode := "tbt", iso := "tti", value := .osV }
  , { walsCode := "tvl", iso := "tvl", value := .onegvs }
  , { walsCode := "ung", iso := "ung", value := .onegvs }
  , { walsCode := "urn", iso := "ura", value := .oVNegS }
  , { walsCode := "wic", iso := "wic", value := .negovsNegsov }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144Y
