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
  [ { walsCode := "acl", language := "Acholi", iso := "ach", value := .svoNegvVneg }
  , { walsCode := "agh", language := "Aghem", iso := "agq", value := .snegvoSvnego }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .svoSovNegvVneg }
  , { walsCode := "apu", language := "Apurinã", iso := "apu", value := .negsvoSnegvo }
  , { walsCode := "asy", language := "Arabic (Syrian)", iso := "apc", value := .snegvoNegvso }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .snegvoSonegvSNegVOSoNegV }
  , { walsCode := "au", language := "Au", iso := "avt", value := .snegvoSvoneg }
  , { walsCode := "bwc", language := "Bajau (West Coast)", iso := "bdr", value := .svoVsoNegv }
  , { walsCode := "bkr", language := "Batak (Karo)", iso := "btx", value := .snegvoNegvso }
  , { walsCode := "bch", language := "Berber (Chaouia)", iso := "shy", value := .snegvoNegvso }
  , { walsCode := "bii", language := "Biri", iso := "bzr", value := .svoFlexibleNeg }
  , { walsCode := "btk", language := "Bontok", iso := "lbk", value := .svoVsoNegv }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .snegvoSonegvSvonegSovneg }
  , { walsCode := "dsh", language := "Danish", iso := "dan", value := .snegvoSvnego }
  , { walsCode := "dre", language := "Drehu", iso := "dhv", value := .negsvoNegvos }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .svonegSonegv }
  , { walsCode := "ger", language := "German", iso := "deu", value := .svonegSonegv }
  , { walsCode := "grk", language := "Greek (Modern)", iso := "ell", value := .snegvoNegvso }
  , { walsCode := "gku", language := "Gününa Küne", iso := "pue", value := .sNegVONegVOs }
  , { walsCode := "ice", language := "Icelandic", iso := "isl", value := .snegvoSvnego }
  , { walsCode := "klv", language := "Kilivila", iso := "kij", value := .svoVosNegv }
  , { walsCode := "koe", language := "Koegu", iso := "xwg", value := .svoNegvVNeg }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .sVNegOSoVNeg }
  , { walsCode := "lac", language := "Lacandón", iso := "lac", value := .svoVosNegv }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .svonegSnegovSovneg }
  , { walsCode := "luo", language := "Luo", iso := "luo", value := .negsvoSnegvo }
  , { walsCode := "mbt", language := "Mangbetu", iso := "mdj", value := .negsvoSvnego }
  , { walsCode := "mtb", language := "Matuumbi", iso := "mgw", value := .svnegoSvoneg }
  , { walsCode := "meh", language := "Mehri", iso := "gdq", value := .svonegVsoneg }
  , { walsCode := "mga", language := "Mondunga", iso := "ndt", value := .svoNegvVNeg }
  , { walsCode := "mos", language := "Mosetén", iso := "cas", value := .negsvoSnegvo }
  , { walsCode := "nad", language := "Nadëb", iso := "mbj", value := .negsvoONegVS }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .negsvoSvnegoNegsovSnegov }
  , { walsCode := "ngo", language := "Ngoni", iso := "ngo", value := .sNegVOSvnego }
  , { walsCode := "nor", language := "Norwegian", iso := "nor", value := .snegvoSvnego }
  , { walsCode := "nse", language := "Nsenga", iso := "nse", value := .sNegVOSvnego }
  , { walsCode := "pau", language := "Paumarí", iso := "pad", value := .negsvoSnegvoSVNegO }
  , { walsCode := "sah", language := "Sahu", iso := "saj", value := .svnegoSvoneg }
  , { walsCode := "swe", language := "Swedish", iso := "swe", value := .snegvoSvnego }
  , { walsCode := "tee", language := "Tepehua (Huehuetla)", iso := "tee", value := .snegvoNegvso }
  , { walsCode := "tin", language := "Tinrin", iso := "cir", value := .snegvoNegvos }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .sNegVOSoNegV }
  , { walsCode := "tob", language := "Toba", iso := "tob", value := .sNegVONegVOs }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .sVNegOSoVNeg }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .svnegoSovneg }
  , { walsCode := "tzu", language := "Tzutujil", iso := "tzj", value := .snegvoNegvos }
  , { walsCode := "wch", language := "Wichí", iso := "mzh", value := .snegvoSVNegO }
  , { walsCode := "wlf", language := "Wolof", iso := "wol", value := .snegvoSVNegO }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144E
