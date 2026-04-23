import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144M: Multiple Negative Constructions in SOV Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144M`.

Chapter 144, 54 languages.
-/

namespace Datasets.WALS.F144M

/-- WALS 144M values. -/
inductive MultipleNegativeConstructionsInSovLanguages where
  /-- SONegV/SOVNeg (1 languages). -/
  | sonegvSovneg
  /-- SNegOV/SONegV (2 languages). -/
  | snegovSonegv
  /-- NegSOV/SNegOV/SONegV (4 languages). -/
  | negsovSnegovSonegv
  /-- NegSOV/2ndPos (1 languages). -/
  | negsov2ndpos
  /-- SOVNeg/SO[V-Neg] (8 languages). -/
  | sovnegSoVNeg
  /-- SO[Neg-V]/SO[V-Neg] (6 languages). -/
  | soNegVSoVNeg
  /-- SO[Neg-V]/SOVwithNegInfix (1 languages). -/
  | soNegVSovwithneginfix
  /-- SNegOV/SONegV/SO[V-Neg] (1 languages). -/
  | snegovSonegvSoVNeg
  /-- SONegV/SVONeg (2 languages). -/
  | sonegvSvoneg
  /-- SOVNeg/SVNegO (1 languages). -/
  | sovnegSvnego
  /-- SNegOV/SOVNeg/SVONeg (1 languages). -/
  | snegovSovnegSvoneg
  /-- NegSOV/SNegOV/NegSVO/SVNegO (1 languages). -/
  | negsovSnegovNegsvoSvnego
  /-- SONegV/SOVNeg/SNegVO/SVONeg (1 languages). -/
  | sonegvSovnegSnegvoSvoneg
  /-- SO[Neg-V]/S[Neg-V]O (1 languages). -/
  | soNegVSNegVO
  /-- SO[V-Neg]/S[V-Neg]O/ (2 languages). -/
  | soVNegSVNegO
  /-- SONegV/SO[Neg-V]/SNegVO/S[Neg-V]O (1 languages). -/
  | sonegvSoNegVSnegvoSNegVO
  /-- NegSOV/NegOVS (1 languages). -/
  | negsovNegovs
  /-- SOVNeg/OVNegS (1 languages). -/
  | sovnegOvnegs
  /-- SO[V-Neg]/O[V-Neg]S (1 languages). -/
  | soVNegOVNegS
  /-- SOV & NegV/VNeg (a) (5 languages). -/
  | sovNegvVneg
  /-- SOV & NegV/[Neg-V] (3 languages). -/
  | sovNegvNegV
  /-- SOV & NegV/[V-Neg] (2 languages). -/
  | sovNegvVNeg
  /-- SOV & NegV/VNeg (b) (1 languages). -/
  | sovNegvVneg_23
  /-- SV & OV & NegV/VNeg (2 languages). -/
  | svOvNegvVneg
  /-- SV & OV & NegV/[V-Neg] (1 languages). -/
  | svOvNegvVNeg
  /-- SV & OV & [Neg-V]/[V-Neg] (2 languages). -/
  | svOvNegVVNeg
  /-- SV & OV & VNeg/[V-Neg] (1 languages). -/
  | svOvVnegVNeg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144M dataset (54 languages). -/
def allData : List (Datapoint MultipleNegativeConstructionsInSovLanguages) :=
  [ { walsCode := "abk", iso := "abk", value := .soNegVSoVNeg }
  , { walsCode := "ajg", iso := "ajg", value := .sovNegvVneg_23 }
  , { walsCode := "amb", iso := "abt", value := .sovNegvNegV }
  , { walsCode := "apl", iso := "apy", value := .soVNegOVNegS }
  , { walsCode := "arm", iso := "hye", value := .sonegvSoNegVSnegvoSNegVO }
  , { walsCode := "arw", iso := "hyw", value := .sovNegvVNeg }
  , { walsCode := "aym", iso := "ayr", value := .snegovSonegv }
  , { walsCode := "blt", iso := "bft", value := .sovNegvVneg }
  , { walsCode := "bod", iso := "brx", value := .svOvNegvVneg }
  , { walsCode := "cai", iso := "suq", value := .sonegvSovnegSnegvoSvoneg }
  , { walsCode := "cmn", iso := "com", value := .negsovSnegovSonegv }
  , { walsCode := "cup", iso := "cup", value := .negsov2ndpos }
  , { walsCode := "dmi", iso := "dus", value := .svOvNegVVNeg }
  , { walsCode := "dut", iso := "nld", value := .sonegvSvoneg }
  , { walsCode := "eip", iso := "eip", value := .sonegvSovneg }
  , { walsCode := "eka", iso := "ekg", value := .sovNegvVneg }
  , { walsCode := "ger", iso := "deu", value := .sonegvSvoneg }
  , { walsCode := "gug", iso := "ktd", value := .sovNegvNegV }
  , { walsCode := "ijo", iso := "ijc", value := .sovnegSoVNeg }
  , { walsCode := "kae", iso := "tbd", value := .snegovSonegv }
  , { walsCode := "kmk", iso := "xal", value := .svOvNegvVneg }
  , { walsCode := "kll", iso := "bco", value := .soNegVSoVNeg }
  , { walsCode := "krc", iso := "krc", value := .sovnegSoVNeg }
  , { walsCode := "kyr", iso := "yuj", value := .sovnegSoVNeg }
  , { walsCode := "kol", iso := "kfb", value := .sovnegSoVNeg }
  , { walsCode := "klg", iso := "kle", value := .svOvNegVVNeg }
  , { walsCode := "kwz", iso := "xwa", value := .soVNegSVNegO }
  , { walsCode := "lad", iso := "lbj", value := .soNegVSoVNeg }
  , { walsCode := "lav", iso := "lvk", value := .sovnegSoVNeg }
  , { walsCode := "ldu", iso := "led", value := .snegovSovnegSvoneg }
  , { walsCode := "lho", iso := "lhm", value := .svOvNegvVNeg }
  , { walsCode := "mac", iso := "mbc", value := .sovnegOvnegs }
  , { walsCode := "mkh", iso := "", value := .sovnegSoVNeg }
  , { walsCode := "mtu", iso := "meu", value := .sovNegvVneg }
  , { walsCode := "nag", iso := "nce", value := .sovNegvVneg }
  , { walsCode := "nas", iso := "nas", value := .sovnegSoVNeg }
  , { walsCode := "nav", iso := "nav", value := .negsovSnegovSonegv }
  , { walsCode := "nwd", iso := "new", value := .soNegVSovwithneginfix }
  , { walsCode := "nti", iso := "niy", value := .negsovSnegovNegsvoSvnego }
  , { walsCode := "oro", iso := "okv", value := .sovNegvNegV }
  , { walsCode := "paw", iso := "pwa", value := .sovnegSoVNeg }
  , { walsCode := "pba", iso := "pia", value := .negsovSnegovSonegv }
  , { walsCode := "pit", iso := "pjt", value := .svOvVnegVNeg }
  , { walsCode := "pra", iso := "prn", value := .sovNegvVNeg }
  , { walsCode := "pum", iso := "pmi", value := .soNegVSoVNeg }
  , { walsCode := "qim", iso := "qvi", value := .negsovSnegovSonegv }
  , { walsCode := "ram", iso := "rma", value := .snegovSonegvSoVNeg }
  , { walsCode := "sar", iso := "dju", value := .soNegVSoVNeg }
  , { walsCode := "tmo", iso := "bod", value := .sovNegvVneg }
  , { walsCode := "twn", iso := "twf", value := .soNegVSNegVO }
  , { walsCode := "ton", iso := "tqw", value := .soVNegSVNegO }
  , { walsCode := "tru", iso := "tpy", value := .sovnegSvnego }
  , { walsCode := "uby", iso := "uby", value := .soNegVSoVNeg }
  , { walsCode := "wic", iso := "wic", value := .negsovNegovs }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144M
