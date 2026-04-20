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

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144Y
