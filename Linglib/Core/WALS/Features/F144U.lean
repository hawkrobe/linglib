import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144U: Double negation in verb-initial languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144U`.

Chapter 144, 17 languages.
-/

namespace Core.WALS.F144U

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
  [ { walsCode := "ann", language := "Anindilyakwa", iso := "aoi", value := .vsVoNegV }
  , { walsCode := "amr", language := "Arabic (Moroccan)", iso := "ary", value := .vsVoNegVNeg }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .svoVsoButNegVSo }
  , { walsCode := "cak", language := "Cakchiquel", iso := "cak", value := .negvnegos }
  , { walsCode := "chj", language := "Chuj", iso := "cac", value := .vosNegvneg }
  , { walsCode := "dom", language := "Domari", iso := "rmt", value := .vsVoNegvVNeg }
  , { walsCode := "hdi", language := "Hdi", iso := "xed", value := .vnegsoneg }
  , { walsCode := "kbl", language := "Kabyle", iso := "kab", value := .negvnegso }
  , { walsCode := "kro", language := "Krongo", iso := "kgo", value := .negvsoneg }
  , { walsCode := "lmg", language := "Lamang", iso := "hia", value := .vsoneg }
  , { walsCode := "miy", language := "Miya", iso := "mkf", value := .negvosnegVnegosnegSnegvonegSvnegoneg }
  , { walsCode := "ond", language := "Oneida", iso := "one", value := .vsVoNegV }
  , { walsCode := "pkt", language := "Pokot", iso := "pko", value := .negvsoNegVNegSo }
  , { walsCode := "rap", language := "Rapanui", iso := "rap", value := .negvso }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .vsoSvoV }
  , { walsCode := "tsk", language := "Tamashek", iso := "taq", value := .negvsoOptstemchange }
  , { walsCode := "tsi", language := "Tsimshian (Coast)", iso := "tsi", value := .negnegvso }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144U
