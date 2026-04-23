import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144C: Languages with different word order in negative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144C`.

Chapter 144, 28 languages.
-/

namespace Datasets.WALS.F144C

/-- WALS 144C values. -/
inductive LanguagesWithDifferentWordOrderInNegativeClauses where
  /-- VSO, but NegSVO (6 languages). -/
  | vsoButNegsvo
  /-- SVO, but SNegOV (3 languages). -/
  | svoButSnegov
  /-- SVO, but SONegV (1 languages). -/
  | svoButSonegv
  /-- SVO, but SOVNeg (1 languages). -/
  | svoButSovneg
  /-- SVO, but NegVSO (1 languages). -/
  | svoButNegvso
  /-- SVO but SO[V-Neg] (1 languages). -/
  | svoButSoVNeg
  /-- SVO but SO[Neg-V] (1 languages). -/
  | svoButSoNegV
  /-- OSV but NegSVO/O[Neg-V]S (1 languages). -/
  | osvButNegsvoONegVS
  /-- SVO, but NegSNegOV (1 languages). -/
  | svoButNegsnegov
  /-- SVO, but SONeg[V-Neg]/SO[Neg-V-Neg] (1 languages). -/
  | svoButSonegVNegSoNegVNeg
  /-- SOV but  SONeg[V-Neg]/S[Neg-V-Neg] O (1 languages). -/
  | sovButSonegVNegSNegVNegO
  /-- SVO/VSO, but NegSVONeg (1 languages). -/
  | svoVsoButNegsvoneg
  /-- SVO/VSO, but [Neg-V]SO(Neg) (1 languages). -/
  | svoVsoButNegVSo
  /-- SVO/SOV, but SVONeg (5 languages). -/
  | svoSovButSvoneg
  /-- SVO/SOV, but SNegVO (1 languages). -/
  | svoSovButSnegvo
  /-- SVO/SOV, but SNegOV (1 languages). -/
  | svoSovButSnegov
  /-- SVO/SOV, but SOVNeg (1 languages). -/
  | svoSovButSovneg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144C dataset (28 languages). -/
def allData : List (Datapoint LanguagesWithDifferentWordOrderInNegativeClauses) :=
  [ { walsCode := "baf", iso := "bfd", value := .svoButNegsnegov }
  , { walsCode := "bbu", iso := "brm", value := .svoVsoButNegVSo }
  , { walsCode := "crn", iso := "cor", value := .svoButNegvso }
  , { walsCode := "din", iso := "din", value := .svoSovButSnegov }
  , { walsCode := "dgo", iso := "doo", value := .svoSovButSvoneg }
  , { walsCode := "grb", iso := "grj", value := .svoButSnegov }
  , { walsCode := "gud", iso := "gde", value := .vsoButNegsvo }
  , { walsCode := "hun", iso := "hun", value := .svoSovButSnegvo }
  , { walsCode := "kyz", iso := "kyz", value := .sovButSonegVNegSNegVNegO }
  , { walsCode := "kla", iso := "klu", value := .svoButSnegov }
  , { walsCode := "agb", iso := "agb", value := .svoButSoNegV }
  , { walsCode := "lgt", iso := "log", value := .svoSovButSvoneg }
  , { walsCode := "lug", iso := "lgg", value := .svoSovButSvoneg }
  , { walsCode := "mad", iso := "mhi", value := .svoSovButSvoneg }
  , { walsCode := "maj", iso := "mpe", value := .vsoButNegsvo }
  , { walsCode := "mao", iso := "mri", value := .vsoButNegsvo }
  , { walsCode := "mrq", iso := "", value := .vsoButNegsvo }
  , { walsCode := "msk", iso := "jle", value := .svoVsoButNegsvoneg }
  , { walsCode := "mbi", iso := "baw", value := .svoButSnegov }
  , { walsCode := "mdw", iso := "mdw", value := .svoButSovneg }
  , { walsCode := "mee", iso := "mym", value := .svoButSoVNeg }
  , { walsCode := "mou", iso := "mgd", value := .svoSovButSvoneg }
  , { walsCode := "mur", iso := "muz", value := .svoButSonegv }
  , { walsCode := "nad", iso := "mbj", value := .osvButNegsvoONegVS }
  , { walsCode := "nue", iso := "nus", value := .svoSovButSovneg }
  , { walsCode := "ten", iso := "tex", value := .vsoButNegsvo }
  , { walsCode := "tes", iso := "teo", value := .vsoButNegsvo }
  , { walsCode := "trm", iso := "suq", value := .svoButSonegVNegSoNegVNeg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144C
