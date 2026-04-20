import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144E: Multiple Negative Constructions in SVO Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144E`.

Chapter 144, 48 languages.
-/

namespace Core.WALS.F144E

/-- WALS 144E values. -/
inductive MultipleNegativeConstructionsInSvoLanguages where
  /-- SNegVO/SVNegO (5 languages). -/
  | snegvoSvnego
  /-- NegSVO/SNegVO (3 languages). -/
  | negsvoSnegvo
  /-- NegSVO/SVNegO (1 languages). -/
  | negsvoSvnego
  /-- SNegVO/SVONeg (1 languages). -/
  | snegvoSvoneg
  /-- SVNegO/SVONeg (2 languages). -/
  | svnegoSvoneg
  /-- SVO & Flexible Neg (1 languages). -/
  | svoFlexibleNeg
  /-- SNegVO/S[V-Neg]O (2 languages). -/
  | snegvoSVNegO
  /-- S[Neg-V]O/SVNegO (2 languages). -/
  | sNegVOSvnego
  /-- NegSVO/SNegVO/S[V-Neg]O (1 languages). -/
  | negsvoSnegvoSVNegO
  /-- SNegVO/NegVSO (5 languages). -/
  | snegvoNegvso
  /-- SVONeg/VSONeg (1 languages). -/
  | svonegVsoneg
  /-- NegSVO/NegVOS (1 languages). -/
  | negsvoNegvos
  /-- SNegVO/NegVOS (2 languages). -/
  | snegvoNegvos
  /-- S[Neg-V]O/[Neg-V]OS (2 languages). -/
  | sNegVONegVOs
  /-- SVONeg/SONegV (2 languages). -/
  | svonegSonegv
  /-- SVNegO/SOVNeg (1 languages). -/
  | svnegoSovneg
  /-- SVONeg/SNegOV/SOVNeg (1 languages). -/
  | svonegSnegovSovneg
  /-- NegSVO/SVNegO/NegSOV/SNegOV (1 languages). -/
  | negsvoSvnegoNegsovSnegov
  /-- SNegVO/SONegV/SVONeg/SOVNeg (1 languages). -/
  | snegvoSonegvSvonegSovneg
  /-- S[Neg-V]O/SO[Neg-V] (1 languages). -/
  | sNegVOSoNegV
  /-- S[V-Neg]O/SO[V-Neg] (2 languages). -/
  | sVNegOSoVNeg
  /-- SNegVO/SONegV/S[Neg-V]O/SO[Neg-V] (1 languages). -/
  | snegvoSonegvSNegVOSoNegV
  /-- NegSVO/O[Neg-V]S (1 languages). -/
  | negsvoONegVS
  /-- SVO & NegV/VNeg (1 languages). -/
  | svoNegvVneg
  /-- SVO & NegV/[V-Neg] (2 languages). -/
  | svoNegvVNeg
  /-- SVO/VSO & NegV (2 languages). -/
  | svoVsoNegv
  /-- SVO/VOS & NegV (2 languages). -/
  | svoVosNegv
  /-- SVO/SOV & NegV/VNeg (1 languages). -/
  | svoSovNegvVneg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144E dataset (48 languages). -/
def allData : List (Datapoint MultipleNegativeConstructionsInSvoLanguages) :=
  [ { walsCode := "acl", iso := "ach", value := .svoNegvVneg }
  , { walsCode := "agh", iso := "agq", value := .snegvoSvnego }
  , { walsCode := "ajg", iso := "ajg", value := .svoSovNegvVneg }
  , { walsCode := "apu", iso := "apu", value := .negsvoSnegvo }
  , { walsCode := "asy", iso := "apc", value := .snegvoNegvso }
  , { walsCode := "arm", iso := "hye", value := .snegvoSonegvSNegVOSoNegV }
  , { walsCode := "au", iso := "avt", value := .snegvoSvoneg }
  , { walsCode := "bwc", iso := "bdr", value := .svoVsoNegv }
  , { walsCode := "bkr", iso := "btx", value := .snegvoNegvso }
  , { walsCode := "bch", iso := "shy", value := .snegvoNegvso }
  , { walsCode := "bii", iso := "bzr", value := .svoFlexibleNeg }
  , { walsCode := "btk", iso := "lbk", value := .svoVsoNegv }
  , { walsCode := "cai", iso := "suq", value := .snegvoSonegvSvonegSovneg }
  , { walsCode := "dsh", iso := "dan", value := .snegvoSvnego }
  , { walsCode := "dre", iso := "dhv", value := .negsvoNegvos }
  , { walsCode := "dut", iso := "nld", value := .svonegSonegv }
  , { walsCode := "ger", iso := "deu", value := .svonegSonegv }
  , { walsCode := "grk", iso := "ell", value := .snegvoNegvso }
  , { walsCode := "gku", iso := "pue", value := .sNegVONegVOs }
  , { walsCode := "ice", iso := "isl", value := .snegvoSvnego }
  , { walsCode := "klv", iso := "kij", value := .svoVosNegv }
  , { walsCode := "koe", iso := "xwg", value := .svoNegvVNeg }
  , { walsCode := "kwz", iso := "xwa", value := .sVNegOSoVNeg }
  , { walsCode := "lac", iso := "lac", value := .svoVosNegv }
  , { walsCode := "ldu", iso := "led", value := .svonegSnegovSovneg }
  , { walsCode := "luo", iso := "luo", value := .negsvoSnegvo }
  , { walsCode := "mbt", iso := "mdj", value := .negsvoSvnego }
  , { walsCode := "mtb", iso := "mgw", value := .svnegoSvoneg }
  , { walsCode := "meh", iso := "gdq", value := .svonegVsoneg }
  , { walsCode := "mga", iso := "ndt", value := .svoNegvVNeg }
  , { walsCode := "mos", iso := "cas", value := .negsvoSnegvo }
  , { walsCode := "nad", iso := "mbj", value := .negsvoONegVS }
  , { walsCode := "nti", iso := "niy", value := .negsvoSvnegoNegsovSnegov }
  , { walsCode := "ngo", iso := "ngo", value := .sNegVOSvnego }
  , { walsCode := "nor", iso := "nor", value := .snegvoSvnego }
  , { walsCode := "nse", iso := "nse", value := .sNegVOSvnego }
  , { walsCode := "pau", iso := "pad", value := .negsvoSnegvoSVNegO }
  , { walsCode := "sah", iso := "saj", value := .svnegoSvoneg }
  , { walsCode := "swe", iso := "swe", value := .snegvoSvnego }
  , { walsCode := "tee", iso := "tee", value := .snegvoNegvso }
  , { walsCode := "tin", iso := "cir", value := .snegvoNegvos }
  , { walsCode := "twn", iso := "twf", value := .sNegVOSoNegV }
  , { walsCode := "tob", iso := "tob", value := .sNegVONegVOs }
  , { walsCode := "ton", iso := "tqw", value := .sVNegOSoVNeg }
  , { walsCode := "tru", iso := "tpy", value := .svnegoSovneg }
  , { walsCode := "tzu", iso := "tzj", value := .snegvoNegvos }
  , { walsCode := "wch", iso := "mzh", value := .snegvoSVNegO }
  , { walsCode := "wlf", iso := "wol", value := .snegvoSVNegO }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144E
