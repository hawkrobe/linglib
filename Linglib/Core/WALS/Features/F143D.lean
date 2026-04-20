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
  /-- (Neg)[Neg-V-Neg] (1 languages). -/
  | negVNeg
  /-- [V-Neg]Neg&OptNegInfix or Pref (1 languages). -/
  | vNegNegOptneginfixOrPref
  /-- NegVNeg/NegNegVNeg (1 languages). -/
  | negvnegNegnegvneg
  /-- Neg[V-Neg]/NegVNeg&NegTone (1 languages). -/
  | negVNegNegvnegNegtone
  /-- Neg[V(-Neg)]Neg/[Neg-V(-Neg)]Neg (1 languages). -/
  | negVNegNegVNeg
  /-- Neg[V-(Neg)](Neg) (1 languages). -/
  | negV
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

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143D
