import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144O: Optional Double Negation in SOV languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144O`.

Chapter 144, 31 languages.
-/

namespace Core.WALS.F144O

/-- WALS 144O values. -/
inductive OptionalDoubleNegationInSovLanguages where
  /-- NegSOV(Neg) (1 languages). -/
  | negsov
  /-- S(Neg)OVNeg (3 languages). -/
  | sovneg
  /-- SNegOV(Neg) (1 languages). -/
  | snegov
  /-- SNegO[V(-Neg)] (1 languages). -/
  | snegoV
  /-- SO[(Neg-)V]Neg (1 languages). -/
  | soVNeg
  /-- SO[Neg-V(-Neg)] (2 languages). -/
  | soNegV
  /-- SO[(Neg-)V-Neg] (3 languages). -/
  | soVNeg_7
  /-- SO[V-Neg](Neg) (2 languages). -/
  | soVNeg_8
  /-- SOVNeg/SO[Neg-V-Neg] (1 languages). -/
  | sovnegSoNegVNeg
  /-- SNegO[V(-Neg)](Neg) (1 languages). -/
  | snegoV_10
  /-- SOV but S[Neg-V-Neg]O/SO[V-Neg] (1 languages). -/
  | sovButSNegVNegOSoVNeg
  /-- SO[Neg-V-(Neg)]/SOVNeg (1 languages). -/
  | soNegVSovneg
  /-- (Neg)SOVNeg/S(Neg)OVNeg/SO(Neg)VNeg (3 languages). -/
  | sovnegSovnegSovneg
  /-- S(Neg)O[V(-Neg)]/SO(Neg)[V(-Neg)] (1 languages). -/
  | soVSoV
  /-- SOV & (Neg)[V-Neg] (2 languages). -/
  | sovVNeg
  /-- SOV & (Neg)[V(-Neg)] (1 languages). -/
  | sovV
  /-- SOV/SVO & Neg[V-(Neg)] (1 languages). -/
  | sovSvoNegV
  /-- SV & OV & (Neg)V(Neg) (1 languages). -/
  | svOvV
  /-- SV & OV &  (Neg)[V-Neg] (1 languages). -/
  | svOvVNeg
  /-- SV & OV &  [Neg-V(-Neg)] (1 languages). -/
  | svOvNegV
  /-- SV & OV &  [(Neg-)V-Neg] (2 languages). -/
  | svOvVNeg_21
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144O dataset (31 languages). -/
def allData : List (Datapoint OptionalDoubleNegationInSovLanguages) :=
  [ { walsCode := "adg", language := "Adang", iso := "adn", value := .sovneg }
  , { walsCode := "ame", language := "Amele", iso := "aey", value := .soVSoV }
  , { walsCode := "ao", language := "Ao", iso := "njo", value := .soNegV }
  , { walsCode := "bel", language := "Belhare", iso := "byw", value := .svOvVNeg_21 }
  , { walsCode := "blx", language := "Biloxi", iso := "bll", value := .soVNeg }
  , { walsCode := "bok", language := "Boko", iso := "bqc", value := .sovneg }
  , { walsCode := "chi", language := "Chimariko", iso := "cid", value := .svOvVNeg_21 }
  , { walsCode := "dun", language := "Duna", iso := "duc", value := .sovnegSoNegVNeg }
  , { walsCode := "guh", language := "Guhu-Samane", iso := "ghs", value := .sovV }
  , { walsCode := "hlp", language := "Hualapai", iso := "yuf", value := .sovnegSovnegSovneg }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .sovSvoNegV }
  , { walsCode := "kma", language := "Kamaiurá", iso := "kay", value := .soVNeg_7 }
  , { walsCode := "kyz", language := "Kayabí", iso := "kyz", value := .sovButSNegVNegOSoVNeg }
  , { walsCode := "khg", language := "Khaling", iso := "klr", value := .soNegV }
  , { walsCode := "klw", language := "Kiliwa", iso := "klb", value := .sovnegSovnegSovneg }
  , { walsCode := "kmb", language := "Kombai", iso := "", value := .soVNeg_7 }
  , { walsCode := "kwo", language := "Kwoma", iso := "kmo", value := .sovVNeg }
  , { walsCode := "kwt", language := "Kwomtari", iso := "kwo", value := .snegoV_10 }
  , { walsCode := "mab", language := "Maba", iso := "mde", value := .soVNeg_8 }
  , { walsCode := "mku", language := "Maranungku", iso := "zmr", value := .negsov }
  , { walsCode := "mka", language := "Mauka", iso := "mxx", value := .snegov }
  , { walsCode := "nph", language := "Nar-Phu", iso := "npa", value := .svOvNegV }
  , { walsCode := "niv", language := "Nivkh", iso := "niv", value := .soVNeg_8 }
  , { walsCode := "run", language := "Runga", iso := "rou", value := .sovVNeg }
  , { walsCode := "sup", language := "Supyire", iso := "spp", value := .sovneg }
  , { walsCode := "tac", language := "Tacana", iso := "tna", value := .svOvV }
  , { walsCode := "tar", language := "Tariana", iso := "tae", value := .soVNeg_7 }
  , { walsCode := "tja", language := "Tiipay (Jamul)", iso := "dih", value := .sovnegSovnegSovneg }
  , { walsCode := "tgl", language := "Tshangla", iso := "tsj", value := .soNegVSovneg }
  , { walsCode := "tsh", language := "Tümpisa Shoshone", iso := "par", value := .snegoV }
  , { walsCode := "woi", language := "Woisika", iso := "woi", value := .svOvVNeg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144O
