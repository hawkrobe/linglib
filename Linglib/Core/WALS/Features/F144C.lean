import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144C: Languages with different word order in negative clauses
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144C`.

Chapter 144, 28 languages.
-/

namespace Core.WALS.F144C

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
  [ { walsCode := "baf", language := "Bafut", iso := "bfd", value := .svoButNegsnegov }
  , { walsCode := "bbu", language := "Barambu", iso := "brm", value := .svoVsoButNegVSo }
  , { walsCode := "crn", language := "Cornish", iso := "cor", value := .svoButNegvso }
  , { walsCode := "din", language := "Dinka", iso := "din", value := .svoSovButSnegov }
  , { walsCode := "dgo", language := "Dongo", iso := "doo", value := .svoSovButSvoneg }
  , { walsCode := "grb", language := "Grebo", iso := "grj", value := .svoButSnegov }
  , { walsCode := "gud", language := "Gude", iso := "gde", value := .vsoButNegsvo }
  , { walsCode := "hun", language := "Hungarian", iso := "hun", value := .svoSovButSnegvo }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .sovButSonegVNegSNegVNegO }
  , { walsCode := "kla", language := "Klao", iso := "klu", value := .svoButSnegov }
  , { walsCode := "agb", language := "Leggbó", iso := "agb", value := .svoButSoNegV }
  , { walsCode := "lgt", language := "Logoti", iso := "log", value := .svoSovButSvoneg }
  , { walsCode := "lug", language := "Lugbara", iso := "lgg", value := .svoSovButSvoneg }
  , { walsCode := "mad", language := "Ma'di", iso := "mhi", value := .svoSovButSvoneg }
  , { walsCode := "maj", language := "Majang", iso := "mpe", value := .vsoButNegsvo }
  , { walsCode := "mao", language := "Maori", iso := "mri", value := .vsoButNegsvo }
  , { walsCode := "mrq", language := "Marquesan", iso := "", value := .vsoButNegsvo }
  , { walsCode := "msk", language := "Masakin", iso := "jle", value := .svoVsoButNegsvoneg }
  , { walsCode := "mbi", language := "Mbili", iso := "baw", value := .svoButSnegov }
  , { walsCode := "mdw", language := "Mbosi", iso := "mdw", value := .svoButSovneg }
  , { walsCode := "mee", language := "Me'en", iso := "mym", value := .svoButSoVNeg }
  , { walsCode := "mou", language := "Moru", iso := "mgd", value := .svoSovButSvoneg }
  , { walsCode := "mur", language := "Mursi", iso := "muz", value := .svoButSonegv }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .osvButNegsvoONegVS }
  , { walsCode := "nue", language := "Nuer", iso := "nus", value := .svoSovButSovneg }
  , { walsCode := "ten", language := "Tennet", iso := "tex", value := .vsoButNegsvo }
  , { walsCode := "tes", language := "Teso", iso := "teo", value := .vsoButNegsvo }
  , { walsCode := "trm", language := "Tirmaga", iso := "suq", value := .svoButSonegVNegSoNegVNeg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144C
