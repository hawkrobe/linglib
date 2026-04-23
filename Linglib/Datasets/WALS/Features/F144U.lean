import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144U: Double negation in verb-initial languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144U`.

Chapter 144, 17 languages.
-/

namespace Datasets.WALS.F144U

/-- WALS 144U values. -/
inductive DoubleNegationInVerbInitialLanguages where
  /-- NegVNegSO (1 languages). -/
  | negvnegso
  /-- NegVNegOS (1 languages). -/
  | negvnegos
  /-- NegVSONeg (1 languages). -/
  | negvsoneg
  /-- NegNegVSO (1 languages). -/
  | negnegvso
  /-- VNegSONeg (1 languages). -/
  | vnegsoneg
  /-- VS & VO & [Neg-V-Neg] (1 languages). -/
  | vsVoNegVNeg
  /-- NegVOSNeg/VNegOSNeg/SNegVONeg/SVNegONeg (1 languages). -/
  | negvosnegVnegosnegSnegvonegSvnegoneg
  /-- V(Neg)SONeg (1 languages). -/
  | vsoneg
  /-- Neg(Neg)VSO (1 languages). -/
  | negvso
  /-- NegVSO/[Neg-V-Neg]SO (1 languages). -/
  | negvsoNegVNegSo
  /-- NegVSO&OptStemChange (1 languages). -/
  | negvsoOptstemchange
  /-- SVO/VSO but [Neg-V]SO(Neg) (1 languages). -/
  | svoVsoButNegVSo
  /-- VS&VO&Neg[(Neg-)V] (2 languages). -/
  | vsVoNegV
  /-- VS&VO&NegV/[(Neg-)V-Neg] (1 languages). -/
  | vsVoNegvVNeg
  /-- VOS & NegVNeg (1 languages). -/
  | vosNegvneg
  /-- VSO/SVO & (Neg)V(Neg) (1 languages). -/
  | vsoSvoV
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144U dataset (17 languages). -/
def allData : List (Datapoint DoubleNegationInVerbInitialLanguages) :=
  [ { walsCode := "ann", iso := "aoi", value := .vsVoNegV }
  , { walsCode := "amr", iso := "ary", value := .vsVoNegVNeg }
  , { walsCode := "bbu", iso := "brm", value := .svoVsoButNegVSo }
  , { walsCode := "cak", iso := "cak", value := .negvnegos }
  , { walsCode := "chj", iso := "cac", value := .vosNegvneg }
  , { walsCode := "dom", iso := "rmt", value := .vsVoNegvVNeg }
  , { walsCode := "hdi", iso := "xed", value := .vnegsoneg }
  , { walsCode := "kbl", iso := "kab", value := .negvnegso }
  , { walsCode := "kro", iso := "kgo", value := .negvsoneg }
  , { walsCode := "lmg", iso := "hia", value := .vsoneg }
  , { walsCode := "miy", iso := "mkf", value := .negvosnegVnegosnegSnegvonegSvnegoneg }
  , { walsCode := "ond", iso := "one", value := .vsVoNegV }
  , { walsCode := "pkt", iso := "pko", value := .negvsoNegVNegSo }
  , { walsCode := "rap", iso := "rap", value := .negvso }
  , { walsCode := "rwe", iso := "rmw", value := .vsoSvoV }
  , { walsCode := "tsk", iso := "taq", value := .negvsoOptstemchange }
  , { walsCode := "tsi", iso := "tsi", value := .negnegvso }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144U
