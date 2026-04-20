import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 143B: Obligatory Double Negation
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143B`.

Chapter 143, 119 languages.
-/

namespace Core.WALS.F143B

/-- WALS 143B values. -/
inductive ObligatoryDoubleNegation where
  /-- NegVNeg (35 languages). -/
  | negvneg
  /-- Neg[V-Neg] (28 languages). -/
  | negVNeg
  /-- [Neg-V]Neg (9 languages). -/
  | negVNeg_3
  /-- [Neg-V-Neg] (27 languages). -/
  | negVNeg_4
  /-- Negative tone & VNeg (1 languages). -/
  | negativeToneVneg
  /-- Negative tone & [Neg-V] (2 languages). -/
  | negativeToneNegV
  /-- NegNegV (2 languages). -/
  | negnegv
  /-- Neg[Neg-V] (2 languages). -/
  | negNegV
  /-- VNegNeg (2 languages). -/
  | vnegneg
  /-- Type 1 / Type 2 (1 languages). -/
  | type1Type2
  /-- Type 1 / Type 3 (1 languages). -/
  | type1Type3
  /-- Type 1 / Type 5 (1 languages). -/
  | type1Type5
  /-- Type 1 / Type 7 (1 languages). -/
  | type1Type7
  /-- Type 1 / Type 9 (1 languages). -/
  | type1Type9
  /-- Type 2 / Type 4 (1 languages). -/
  | type2Type4
  /-- ObligDoubleNeg&OptTripleNeg (5 languages). -/
  | obligdoublenegOpttripleneg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 143B dataset (119 languages). -/
def allData : List (Datapoint ObligatoryDoubleNegation) :=
  [ { walsCode := "abu", iso := "kgr", value := .negvneg }
  , { walsCode := "amn", iso := "amn", value := .negVNeg }
  , { walsCode := "aml", iso := "omb", value := .negvneg }
  , { walsCode := "amh", iso := "amh", value := .negVNeg_4 }
  , { walsCode := "amo", iso := "amo", value := .negvneg }
  , { walsCode := "amx", iso := "imi", value := .negVNeg }
  , { walsCode := "apw", iso := "apw", value := .negVNeg }
  , { walsCode := "amr", iso := "ary", value := .negVNeg_4 }
  , { walsCode := "ana", iso := "aro", value := .negVNeg_4 }
  , { walsCode := "asu", iso := "asu", value := .negVNeg_4 }
  , { walsCode := "awp", iso := "kwi", value := .type1Type2 }
  , { walsCode := "bab", iso := "bav", value := .negvneg }
  , { walsCode := "baf", iso := "bfd", value := .negnegv }
  , { walsCode := "ble", iso := "bci", value := .negativeToneVneg }
  , { walsCode := "bid", iso := "bid", value := .negvneg }
  , { walsCode := "bob", iso := "bni", value := .negvneg }
  , { walsCode := "bbf", iso := "bbo", value := .negvneg }
  , { walsCode := "boi", iso := "bzf", value := .negVNeg }
  , { walsCode := "bre", iso := "bre", value := .type1Type7 }
  , { walsCode := "buy", iso := "bwu", value := .negvneg }
  , { walsCode := "brm", iso := "mya", value := .negVNeg_3 }
  , { walsCode := "cak", iso := "cak", value := .negvneg }
  , { walsCode := "cml", iso := "rab", value := .negVNeg_4 }
  , { walsCode := "chb", iso := "can", value := .negNegV }
  , { walsCode := "cui", iso := "cui", value := .negVNeg }
  , { walsCode := "deg", iso := "deg", value := .negativeToneNegV }
  , { walsCode := "dha", iso := "dsh", value := .negVNeg }
  , { walsCode := "doy", iso := "dow", value := .obligdoublenegOpttripleneg }
  , { walsCode := "erk", iso := "erk", value := .negvneg }
  , { walsCode := "eko", iso := "eko", value := .negVNeg_4 }
  , { walsCode := "evn", iso := "eve", value := .negVNeg }
  , { walsCode := "eve", iso := "evn", value := .negVNeg }
  , { walsCode := "ewe", iso := "ewe", value := .negvneg }
  , { walsCode := "fur", iso := "fvr", value := .negVNeg_4 }
  , { walsCode := "gua", iso := "gug", value := .negvneg }
  , { walsCode := "gnb", iso := "wlg", value := .obligdoublenegOpttripleneg }
  , { walsCode := "gwa", iso := "gbr", value := .negvneg }
  , { walsCode := "hai", iso := "hai", value := .negVNeg }
  , { walsCode := "hal", iso := "hla", value := .negvneg }
  , { walsCode := "hdi", iso := "xed", value := .vnegneg }
  , { walsCode := "ido", iso := "idu", value := .negvneg }
  , { walsCode := "ifm", iso := "ifm", value := .negvneg }
  , { walsCode := "ite", iso := "itl", value := .negVNeg }
  , { walsCode := "kwy", iso := "yom", value := .negVNeg_3 }
  , { walsCode := "izi", iso := "izz", value := .negVNeg }
  , { walsCode := "kbl", iso := "kab", value := .negvneg }
  , { walsCode := "knk", iso := "kna", value := .negvneg }
  , { walsCode := "kbw", iso := "bwe", value := .negVNeg_3 }
  , { walsCode := "ksg", iso := "ksw", value := .negvneg }
  , { walsCode := "krk", iso := "kyh", value := .negVNeg }
  , { walsCode := "ktl", iso := "kcr", value := .negvneg }
  , { walsCode := "kio", iso := "kio", value := .negVNeg }
  , { walsCode := "kis", iso := "kss", value := .type1Type5 }
  , { walsCode := "kiw", iso := "kjd", value := .negVNeg }
  , { walsCode := "kon", iso := "kng", value := .obligdoublenegOpttripleneg }
  , { walsCode := "krw", iso := "khe", value := .negVNeg_4 }
  , { walsCode := "kry", iso := "kpy", value := .negVNeg_4 }
  , { walsCode := "kro", iso := "kgo", value := .negvneg }
  , { walsCode := "lmu", iso := "lmu", value := .negvneg }
  , { walsCode := "len", iso := "tnl", value := .negVNeg_3 }
  , { walsCode := "lng", iso := "enx", value := .negVNeg_4 }
  , { walsCode := "lep", iso := "lep", value := .negVNeg_4 }
  , { walsCode := "lim", iso := "lif", value := .negVNeg_4 }
  , { walsCode := "lnd", iso := "liy", value := .negVNeg_3 }
  , { walsCode := "lou", iso := "loj", value := .negvneg }
  , { walsCode := "lbu", iso := "lun", value := .negVNeg_3 }
  , { walsCode := "luv", iso := "lue", value := .type1Type3 }
  , { walsCode := "ma", iso := "msj", value := .negVNeg_3 }
  , { walsCode := "msn", iso := "mbq", value := .negvneg }
  , { walsCode := "mkz", iso := "mcp", value := .negVNeg_4 }
  , { walsCode := "mdn", iso := "mhq", value := .negVNeg_4 }
  , { walsCode := "mar", iso := "mrc", value := .negVNeg_4 }
  , { walsCode := "msk", iso := "jle", value := .negvneg }
  , { walsCode := "mbl", iso := "mdq", value := .negVNeg_4 }
  , { walsCode := "men", iso := "mez", value := .negVNeg }
  , { walsCode := "miy", iso := "mkf", value := .type1Type9 }
  , { walsCode := "mom", iso := "mso", value := .negVNeg }
  , { walsCode := "moo", iso := "mos", value := .negvneg }
  , { walsCode := "aoj", iso := "aoj", value := .negvneg }
  , { walsCode := "mwo", iso := "mlv", value := .negVNeg }
  , { walsCode := "ndb", iso := "nde", value := .negVNeg_4 }
  , { walsCode := "ndu", iso := "nmd", value := .negVNeg_3 }
  , { walsCode := "non", iso := "nhu", value := .obligdoublenegOpttripleneg }
  , { walsCode := "orh", iso := "hae", value := .negativeToneNegV }
  , { walsCode := "orw", iso := "ssn", value := .negVNeg }
  , { walsCode := "otr", iso := "otr", value := .negvneg }
  , { walsCode := "psm", iso := "pqm", value := .negVNeg }
  , { walsCode := "per", iso := "pip", value := .negvneg }
  , { walsCode := "pis", iso := "psa", value := .negvneg }
  , { walsCode := "pso", iso := "pom", value := .negVNeg }
  , { walsCode := "qhu", iso := "qub", value := .negvneg }
  , { walsCode := "rag", iso := "lml", value := .negvneg }
  , { walsCode := "rot", iso := "rtm", value := .negvneg }
  , { walsCode := "sal", iso := "sln", value := .negNegV }
  , { walsCode := "sgl", iso := "szg", value := .negVNeg_3 }
  , { walsCode := "stn", iso := "nso", value := .negVNeg }
  , { walsCode := "sub", iso := "sbs", value := .negVNeg_4 }
  , { walsCode := "skm", iso := "suk", value := .negVNeg_4 }
  , { walsCode := "swt", iso := "ssw", value := .negVNeg_4 }
  , { walsCode := "tbl", iso := "tnm", value := .obligdoublenegOpttripleneg }
  , { walsCode := "tnc", iso := "tcb", value := .negVNeg }
  , { walsCode := "teo", iso := "tio", value := .negvneg }
  , { walsCode := "thu", iso := "tdh", value := .negVNeg }
  , { walsCode := "tig", iso := "tir", value := .negVNeg_4 }
  , { walsCode := "trm", iso := "suq", value := .type2Type4 }
  , { walsCode := "tsi", iso := "tsi", value := .negnegv }
  , { walsCode := "tte", iso := "tta", value := .negVNeg_4 }
  , { walsCode := "tye", iso := "woa", value := .negvneg }
  , { walsCode := "ute", iso := "ute", value := .negVNeg_4 }
  , { walsCode := "vnm", iso := "vnm", value := .negVNeg_4 }
  , { walsCode := "wrk", iso := "gae", value := .negVNeg }
  , { walsCode := "way", iso := "oym", value := .negVNeg_4 }
  , { walsCode := "win", iso := "wnw", value := .negVNeg }
  , { walsCode := "yqy", iso := "jaq", value := .negVNeg_4 }
  , { walsCode := "yuk", iso := "gcd", value := .negVNeg }
  , { walsCode := "zan", iso := "zne", value := .vnegneg }
  , { walsCode := "zpr", iso := "zro", value := .negVNeg }
  , { walsCode := "zun", iso := "zun", value := .negVNeg }
  , { walsCode := "eme", iso := "eme", value := .negVNeg_4 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143B
