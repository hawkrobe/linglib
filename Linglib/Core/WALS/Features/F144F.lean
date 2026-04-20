import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144F: Obligatory Double Negation in SVO languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144F`.

Chapter 144, 56 languages.
-/

namespace Core.WALS.F144F

/-- WALS 144F values. -/
inductive ObligatoryDoubleNegationInSvoLanguages where
  /-- SNegVONeg (11 languages). -/
  | snegvoneg
  /-- SNegVNegO (6 languages). -/
  | snegvnego
  /-- SVNegONeg (1 languages). -/
  | svnegoneg
  /-- SVO/VSO but NegSVONeg (1 languages). -/
  | svoVsoButNegsvoneg
  /-- S[Neg-V]ONeg (7 languages). -/
  | sNegVOneg
  /-- SNeg[V-Neg]O (4 languages). -/
  | snegVNegO
  /-- S[Neg-V]NegO (1 languages). -/
  | sNegVNego
  /-- NegS[V-Neg]O (2 languages). -/
  | negsVNegO
  /-- S[Neg-V-Neg]O (5 languages). -/
  | sNegVNegO
  /-- SVNegO&NegTone (1 languages). -/
  | svnegoNegtone
  /-- S[Neg-V]O&NegTone (1 languages). -/
  | sNegVONegtone
  /-- SNegNegVO/SNegVNegO (1 languages). -/
  | snegnegvoSnegvnego
  /-- SNegVNegO/SNegVONeg (1 languages). -/
  | snegvnegoSnegvoneg
  /-- SNegVONeg/S[Neg-V]ONeg (1 languages). -/
  | snegvonegSNegVOneg
  /-- (Neg)S(Neg)VONeg (1 languages). -/
  | svoneg
  /-- SNeg[V-Neg]O&NegTone/SNegVNegO (1 languages). -/
  | snegVNegONegtoneSnegvnego
  /-- S(Neg)[Neg-V-Neg]O (1 languages). -/
  | sNegVNegO_17
  /-- SNeg[V(-Neg)]ONeg/S[Neg-V(-Neg)]ONeg (1 languages). -/
  | snegVOnegSNegVOneg
  /-- SNegVONeg/SNegOVNeg (1 languages). -/
  | snegvonegSnegovneg
  /-- SVONeg&NegTone/SNegOVNeg (1 languages). -/
  | svonegNegtoneSnegovneg
  /-- SNegVONeg/SVNegONeg/NegVOSNeg/VNegOSNeg (1 languages). -/
  | snegvonegSvnegonegNegvosnegVnegosneg
  /-- SVO & NegVNeg (5 languages). -/
  | svoNegvneg
  /-- S[Neg-V]O & NegV (1 languages). -/
  | sNegVONegv
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144F dataset (56 languages). -/
def allData : List (Datapoint ObligatoryDoubleNegationInSvoLanguages) :=
  [ { walsCode := "abu", iso := "kgr", value := .snegvoneg }
  , { walsCode := "aml", iso := "omb", value := .snegvnegoSnegvoneg }
  , { walsCode := "bab", iso := "bav", value := .snegvoneg }
  , { walsCode := "ble", iso := "bci", value := .svnegoNegtone }
  , { walsCode := "bid", iso := "bid", value := .svoNegvneg }
  , { walsCode := "bob", iso := "bni", value := .snegvoneg }
  , { walsCode := "bre", iso := "bre", value := .snegnegvoSnegvnego }
  , { walsCode := "buy", iso := "bwu", value := .snegvoneg }
  , { walsCode := "deg", iso := "deg", value := .sNegVONegtone }
  , { walsCode := "doy", iso := "dow", value := .snegVNegONegtoneSnegvnego }
  , { walsCode := "erk", iso := "erk", value := .snegvoneg }
  , { walsCode := "eko", iso := "eko", value := .sNegVNegO }
  , { walsCode := "ewe", iso := "ewe", value := .snegvoneg }
  , { walsCode := "gua", iso := "gug", value := .snegvnego }
  , { walsCode := "gnb", iso := "wlg", value := .sNegVNegO_17 }
  , { walsCode := "gwa", iso := "gbr", value := .snegvonegSnegovneg }
  , { walsCode := "hal", iso := "hla", value := .snegvnego }
  , { walsCode := "ifm", iso := "ifm", value := .svoNegvneg }
  , { walsCode := "kwy", iso := "yom", value := .sNegVOneg }
  , { walsCode := "izi", iso := "izz", value := .snegVNegO }
  , { walsCode := "knk", iso := "kna", value := .snegvoneg }
  , { walsCode := "kbw", iso := "bwe", value := .sNegVOneg }
  , { walsCode := "ksg", iso := "ksw", value := .snegvoneg }
  , { walsCode := "ktl", iso := "kcr", value := .snegvnego }
  , { walsCode := "kis", iso := "kss", value := .svonegNegtoneSnegovneg }
  , { walsCode := "kon", iso := "kng", value := .snegVOnegSNegVOneg }
  , { walsCode := "lmu", iso := "lmu", value := .snegvnego }
  , { walsCode := "len", iso := "tnl", value := .sNegVNego }
  , { walsCode := "lnd", iso := "liy", value := .sNegVOneg }
  , { walsCode := "lou", iso := "loj", value := .snegvoneg }
  , { walsCode := "lbu", iso := "lun", value := .sNegVOneg }
  , { walsCode := "luv", iso := "lue", value := .snegvonegSNegVOneg }
  , { walsCode := "ma", iso := "msj", value := .sNegVOneg }
  , { walsCode := "mkz", iso := "mcp", value := .sNegVNegO }
  , { walsCode := "msk", iso := "jle", value := .svoVsoButNegsvoneg }
  , { walsCode := "miy", iso := "mkf", value := .snegvonegSvnegonegNegvosnegVnegosneg }
  , { walsCode := "moo", iso := "mos", value := .snegvoneg }
  , { walsCode := "aoj", iso := "aoj", value := .svoNegvneg }
  , { walsCode := "mwo", iso := "mlv", value := .snegVNegO }
  , { walsCode := "ndb", iso := "nde", value := .sNegVNegO }
  , { walsCode := "ndu", iso := "nmd", value := .sNegVOneg }
  , { walsCode := "non", iso := "nhu", value := .svoneg }
  , { walsCode := "otr", iso := "otr", value := .svoNegvneg }
  , { walsCode := "per", iso := "pip", value := .snegvoneg }
  , { walsCode := "rag", iso := "lml", value := .svoNegvneg }
  , { walsCode := "rot", iso := "rtm", value := .snegvnego }
  , { walsCode := "sal", iso := "sln", value := .sNegVONegv }
  , { walsCode := "sgl", iso := "szg", value := .sNegVOneg }
  , { walsCode := "stn", iso := "nso", value := .snegVNegO }
  , { walsCode := "skm", iso := "suk", value := .sNegVNegO }
  , { walsCode := "teo", iso := "tio", value := .snegvnego }
  , { walsCode := "vnm", iso := "vnm", value := .sNegVNegO }
  , { walsCode := "wrk", iso := "gae", value := .snegVNegO }
  , { walsCode := "yuk", iso := "gcd", value := .negsVNegO }
  , { walsCode := "zan", iso := "zne", value := .svnegoneg }
  , { walsCode := "zpr", iso := "zro", value := .negsVNegO }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144F
