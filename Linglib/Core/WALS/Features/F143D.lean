import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 143D: Optional Triple Negation
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143D`.

Chapter 143, 6 languages.
-/

namespace Core.WALS.F143D

/-- WALS 143D values. -/
inductive OptionalTripleNegation where
  | negVNeg  -- (Neg)[Neg-V-Neg] (1 languages)
  | vNegNegOptneginfixOrPref  -- [V-Neg]Neg&OptNegInfix or Pref (1 languages)
  | negvnegNegnegvneg  -- NegVNeg/NegNegVNeg (1 languages)
  | negVNegNegvnegNegtone  -- Neg[V-Neg]/NegVNeg&NegTone (1 languages)
  | negVNegNegVNeg  -- Neg[V(-Neg)]Neg/[Neg-V(-Neg)]Neg (1 languages)
  | negV  -- Neg[V-(Neg)](Neg) (1 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 143D dataset (6 languages). -/
def allData : List (Datapoint OptionalTripleNegation) :=
  [ { walsCode := "doy", language := "Doyayo", iso := "dow", value := .negVNegNegvnegNegtone }
  , { walsCode := "gnb", language := "Gunbalang", iso := "wlg", value := .negVNeg }
  , { walsCode := "kon", language := "Kongo", iso := "kng", value := .negVNegNegVNeg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .negV }
  , { walsCode := "non", language := "Noni", iso := "nhu", value := .negvnegNegnegvneg }
  , { walsCode := "tbl", language := "Tabla", iso := "tnm", value := .vNegNegOptneginfixOrPref }
  ]

-- Count verification
theorem total_count : allData.length = 6 := by native_decide

theorem count_negVNeg :
    (allData.filter (·.value == .negVNeg)).length = 1 := by native_decide
theorem count_vNegNegOptneginfixOrPref :
    (allData.filter (·.value == .vNegNegOptneginfixOrPref)).length = 1 := by native_decide
theorem count_negvnegNegnegvneg :
    (allData.filter (·.value == .negvnegNegnegvneg)).length = 1 := by native_decide
theorem count_negVNegNegvnegNegtone :
    (allData.filter (·.value == .negVNegNegvnegNegtone)).length = 1 := by native_decide
theorem count_negVNegNegVNeg :
    (allData.filter (·.value == .negVNegNegVNeg)).length = 1 := by native_decide
theorem count_negV :
    (allData.filter (·.value == .negV)).length = 1 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143D
