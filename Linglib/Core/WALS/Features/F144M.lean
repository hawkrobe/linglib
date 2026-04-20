import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144M: Multiple Negative Constructions in SOV Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144M`.

Chapter 144, 54 languages.
-/

namespace Core.WALS.F144M

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
  [ { walsCode := "abk", language := "Abkhaz", iso := "abk", value := .soNegVSoVNeg }
  , { walsCode := "ajg", language := "Ajagbe", iso := "ajg", value := .sovNegvVneg_23 }
  , { walsCode := "amb", language := "Ambulas", iso := "abt", value := .sovNegvNegV }
  , { walsCode := "apl", language := "Apalaí", iso := "apy", value := .soVNegOVNegS }
  , { walsCode := "arm", language := "Armenian (Eastern)", iso := "hye", value := .sonegvSoNegVSnegvoSNegVO }
  , { walsCode := "arw", language := "Armenian (Western)", iso := "hyw", value := .sovNegvVNeg }
  , { walsCode := "aym", language := "Aymara (Central)", iso := "ayr", value := .snegovSonegv }
  , { walsCode := "blt", language := "Balti", iso := "bft", value := .sovNegvVneg }
  , { walsCode := "bod", language := "Bodo", iso := "brx", value := .svOvNegvVneg }
  , { walsCode := "cai", language := "Chai", iso := "suq", value := .sonegvSovnegSnegvoSvoneg }
  , { walsCode := "cmn", language := "Comanche", iso := "com", value := .negsovSnegovSonegv }
  , { walsCode := "cup", language := "Cupeño", iso := "cup", value := .negsov2ndpos }
  , { walsCode := "dmi", language := "Dumi", iso := "dus", value := .svOvNegVVNeg }
  , { walsCode := "dut", language := "Dutch", iso := "nld", value := .sonegvSvoneg }
  , { walsCode := "eip", language := "Eipo", iso := "eip", value := .sonegvSovneg }
  , { walsCode := "eka", language := "Ekari", iso := "ekg", value := .sovNegvVneg }
  , { walsCode := "ger", language := "German", iso := "deu", value := .sonegvSvoneg }
  , { walsCode := "gug", language := "Gugada", iso := "ktd", value := .sovNegvNegV }
  , { walsCode := "ijo", language := "Ijo (Kolokuma)", iso := "ijc", value := .sovnegSoVNeg }
  , { walsCode := "kae", language := "Kaki Ae", iso := "tbd", value := .snegovSonegv }
  , { walsCode := "kmk", language := "Kalmyk", iso := "xal", value := .svOvNegvVneg }
  , { walsCode := "kll", language := "Kaluli", iso := "bco", value := .soNegVSoVNeg }
  , { walsCode := "krc", language := "Karachay-Balkar", iso := "krc", value := .sovnegSoVNeg }
  , { walsCode := "kyr", language := "Karkar-Yuri", iso := "yuj", value := .sovnegSoVNeg }
  , { walsCode := "kol", language := "Kolami", iso := "kfb", value := .sovnegSoVNeg }
  , { walsCode := "klg", language := "Kulung", iso := "kle", value := .svOvNegVVNeg }
  , { walsCode := "kwz", language := "Kwaza", iso := "xwa", value := .soVNegSVNegO }
  , { walsCode := "lad", language := "Ladakhi", iso := "lbj", value := .soNegVSoVNeg }
  , { walsCode := "lav", language := "Lavukaleve", iso := "lvk", value := .sovnegSoVNeg }
  , { walsCode := "ldu", language := "Lendu", iso := "led", value := .snegovSovnegSvoneg }
  , { walsCode := "lho", language := "Lhomi", iso := "lhm", value := .svOvNegvVNeg }
  , { walsCode := "mac", language := "Macushi", iso := "mbc", value := .sovnegOvnegs }
  , { walsCode := "mkh", language := "Mongol (Khamnigan)", iso := "", value := .sovnegSoVNeg }
  , { walsCode := "mtu", language := "Motu", iso := "meu", value := .sovNegvVneg }
  , { walsCode := "nag", language := "Nagatman", iso := "nce", value := .sovNegvVneg }
  , { walsCode := "nas", language := "Nasioi", iso := "nas", value := .sovnegSoVNeg }
  , { walsCode := "nav", language := "Navajo", iso := "nav", value := .negsovSnegovSonegv }
  , { walsCode := "nwd", language := "Newar (Dolakha)", iso := "new", value := .soNegVSovwithneginfix }
  , { walsCode := "nti", language := "Ngiti", iso := "niy", value := .negsovSnegovNegsvoSvnego }
  , { walsCode := "oro", language := "Orokaiva", iso := "okv", value := .sovNegvNegV }
  , { walsCode := "paw", language := "Pawaian", iso := "pwa", value := .sovnegSoVNeg }
  , { walsCode := "pba", language := "Pima Bajo", iso := "pia", value := .negsovSnegovSonegv }
  , { walsCode := "pit", language := "Pitjantjatjara", iso := "pjt", value := .svOvVnegVNeg }
  , { walsCode := "pra", language := "Prasuni", iso := "prn", value := .sovNegvVNeg }
  , { walsCode := "pum", language := "Pumi", iso := "pmi", value := .soNegVSoVNeg }
  , { walsCode := "qim", language := "Quechua (Imbabura)", iso := "qvi", value := .negsovSnegovSonegv }
  , { walsCode := "ram", language := "Rama", iso := "rma", value := .snegovSonegvSoVNeg }
  , { walsCode := "sar", language := "Sare", iso := "dju", value := .soNegVSoVNeg }
  , { walsCode := "tmo", language := "Tibetan (Modern Literary)", iso := "bod", value := .sovNegvVneg }
  , { walsCode := "twn", language := "Tiwa (Northern)", iso := "twf", value := .soNegVSNegVO }
  , { walsCode := "ton", language := "Tonkawa", iso := "tqw", value := .soVNegSVNegO }
  , { walsCode := "tru", language := "Trumai", iso := "tpy", value := .sovnegSvnego }
  , { walsCode := "uby", language := "Ubykh", iso := "uby", value := .soNegVSoVNeg }
  , { walsCode := "wic", language := "Wichita", iso := "wic", value := .negsovNegovs }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144M
