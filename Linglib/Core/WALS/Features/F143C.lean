import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 143C: Optional Double Negation
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 143C`.

Chapter 143, 81 languages.
-/

namespace Core.WALS.F143C

/-- WALS 143C values. -/
inductive OptionalDoubleNegation where
  /-- NegV(Neg) (11 languages). -/
  | negv
  /-- (Neg)VNeg (20 languages). -/
  | vneg
  /-- Neg[V(-Neg)] (5 languages). -/
  | negV
  /-- (Neg)[V-Neg] (5 languages). -/
  | vNeg
  /-- [Neg-V](Neg) (3 languages). -/
  | negV_5
  /-- [(Neg-)V]Neg (2 languages). -/
  | vNeg_6
  /-- [Neg-V(-Neg)] (5 languages). -/
  | negV_7
  /-- [(Neg-)V-Neg] (6 languages). -/
  | vNeg_8
  /-- V(Neg)Neg (2 languages). -/
  | vneg_9
  /-- [V-Neg](Neg) (2 languages). -/
  | vNeg_10
  /-- Neg(Neg)V (1 languages). -/
  | negv_11
  /-- Neg[(Neg-)]V (3 languages). -/
  | negV_12
  /-- NegV&OptChangeVerbStem (1 languages). -/
  | negvOptchangeverbstem
  /-- NegV/[Neg-V-Neg] (2 languages). -/
  | negvNegVNeg
  /-- VNeg/[Neg-V-Neg] (1 languages). -/
  | vnegNegVNeg
  /-- [Neg-V]/NegVNeg (1 languages). -/
  | negVNegvneg
  /-- NegV or NegativeTone&VNeg (1 languages). -/
  | negvOrNegativetoneVneg
  /-- NegV/[V-Neg]/Neg[V-Neg] (4 languages). -/
  | negvVNegNegVNeg
  /-- NegV/VNeg/NegVNeg (2 languages). -/
  | negvVnegNegvneg
  /-- NegV/[V-Neg]/[Neg-V-Neg] (1 languages). -/
  | negvVNegNegVNeg_20
  /-- [Neg-V]/VNeg/[Neg-V-Neg] (1 languages). -/
  | negVVnegNegVNeg
  /-- NegV/[Neg-V]/Neg[Neg-V] (1 languages). -/
  | negvNegVNegNegV
  /-- OptDoubleNeg&OptTripleNeg (1 languages). -/
  | optdoublenegOpttripleneg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 143C dataset (81 languages). -/
def allData : List (Datapoint OptionalDoubleNegation) :=
  [ { walsCode := "adg", iso := "adn", value := .vneg }
  , { walsCode := "adz", iso := "adz", value := .negV_5 }
  , { walsCode := "ame", iso := "aey", value := .negvVNegNegVNeg }
  , { walsCode := "ann", iso := "aoi", value := .negV_12 }
  , { walsCode := "ao", iso := "njo", value := .negV_7 }
  , { walsCode := "aeg", iso := "arz", value := .negvNegVNeg }
  , { walsCode := "arp", iso := "ape", value := .negv }
  , { walsCode := "bbu", iso := "brm", value := .negV_5 }
  , { walsCode := "bel", iso := "byw", value := .vNeg_8 }
  , { walsCode := "blx", iso := "bll", value := .vNeg_6 }
  , { walsCode := "bmb", iso := "bim", value := .negv }
  , { walsCode := "bok", iso := "bqc", value := .vneg }
  , { walsCode := "bol", iso := "bli", value := .negV_5 }
  , { walsCode := "bgo", iso := "bot", value := .vneg }
  , { walsCode := "ctl", iso := "cat", value := .negv }
  , { walsCode := "cmh", iso := "ute", value := .vNeg }
  , { walsCode := "chi", iso := "cid", value := .vNeg_8 }
  , { walsCode := "chr", iso := "crw", value := .negv }
  , { walsCode := "chj", iso := "cac", value := .negv }
  , { walsCode := "cop", iso := "cop", value := .negVNegvneg }
  , { walsCode := "dom", iso := "rmt", value := .negvVNegNegVNeg_20 }
  , { walsCode := "dma", iso := "dma", value := .vneg }
  , { walsCode := "dun", iso := "duc", value := .vnegNegVNeg }
  , { walsCode := "ewo", iso := "ewo", value := .negvOrNegativetoneVneg }
  , { walsCode := "fre", iso := "fra", value := .vneg }
  , { walsCode := "fye", iso := "pym", value := .vneg }
  , { walsCode := "gbb", iso := "gbp", value := .vneg }
  , { walsCode := "guh", iso := "ghs", value := .negvVNegNegVNeg }
  , { walsCode := "hau", iso := "hau", value := .negv }
  , { walsCode := "hlp", iso := "yuf", value := .vneg }
  , { walsCode := "mxe", iso := "mxe", value := .vNeg_6 }
  , { walsCode := "ina", iso := "szp", value := .vNeg }
  , { walsCode := "kma", iso := "kay", value := .vNeg_8 }
  , { walsCode := "kyz", iso := "kyz", value := .vNeg_8 }
  , { walsCode := "khg", iso := "klr", value := .negV_7 }
  , { walsCode := "klw", iso := "klb", value := .vneg }
  , { walsCode := "kmb", iso := "", value := .vNeg_8 }
  , { walsCode := "kre", iso := "krs", value := .vneg }
  , { walsCode := "kwo", iso := "kmo", value := .vNeg }
  , { walsCode := "kwt", iso := "kwo", value := .optdoublenegOpttripleneg }
  , { walsCode := "lmg", iso := "hia", value := .vneg_9 }
  , { walsCode := "lew", iso := "lww", value := .vneg_9 }
  , { walsCode := "mab", iso := "mde", value := .vNeg_10 }
  , { walsCode := "mku", iso := "zmr", value := .negv }
  , { walsCode := "mka", iso := "mxx", value := .negv }
  , { walsCode := "mbe", iso := "mdt", value := .vneg }
  , { walsCode := "min", iso := "min", value := .negv }
  , { walsCode := "mxx", iso := "mxp", value := .negvNegVNegNegV }
  , { walsCode := "moh", iso := "moh", value := .negV_12 }
  , { walsCode := "mum", iso := "mzm", value := .vneg }
  , { walsCode := "mgk", iso := "mhk", value := .vneg }
  , { walsCode := "mup", iso := "sur", value := .vneg }
  , { walsCode := "nph", iso := "npa", value := .negV_7 }
  , { walsCode := "niv", iso := "niv", value := .vNeg_10 }
  , { walsCode := "nke", iso := "isi", value := .negvVNegNegVNeg }
  , { walsCode := "one", iso := "aun", value := .vneg }
  , { walsCode := "ond", iso := "one", value := .negV_12 }
  , { walsCode := "paa", iso := "pqa", value := .vneg }
  , { walsCode := "plh", iso := "plh", value := .negv }
  , { walsCode := "pkt", iso := "pko", value := .negvNegVNeg }
  , { walsCode := "rap", iso := "rap", value := .negv_11 }
  , { walsCode := "rwe", iso := "rmw", value := .negvVnegNegvneg }
  , { walsCode := "run", iso := "rou", value := .vNeg }
  , { walsCode := "siu", iso := "sis", value := .negV }
  , { walsCode := "sup", iso := "spp", value := .vneg }
  , { walsCode := "tac", iso := "tna", value := .negvVnegNegvneg }
  , { walsCode := "tsk", iso := "taq", value := .negvOptchangeverbstem }
  , { walsCode := "tar", iso := "tae", value := .vNeg_8 }
  , { walsCode := "tmn", iso := "teq", value := .negV }
  , { walsCode := "ter", iso := "ttr", value := .vneg }
  , { walsCode := "tid", iso := "tvo", value := .vneg }
  , { walsCode := "tja", iso := "dih", value := .vneg }
  , { walsCode := "tbt", iso := "tti", value := .negvVNegNegVNeg }
  , { walsCode := "tgl", iso := "tsj", value := .negVVnegNegVNeg }
  , { walsCode := "tsh", iso := "par", value := .negV }
  , { walsCode := "urt", iso := "urt", value := .negv }
  , { walsCode := "wrn", iso := "wnd", value := .negV_7 }
  , { walsCode := "wiy", iso := "wiy", value := .negV }
  , { walsCode := "woi", iso := "woi", value := .vNeg }
  , { walsCode := "zch", iso := "zoh", value := .negV }
  , { walsCode := "zul", iso := "zul", value := .negV_7 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F143C
