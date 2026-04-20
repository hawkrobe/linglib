import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144G: Optional Double Negation in SVO languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144G`.

Chapter 144, 35 languages.
-/

namespace Core.WALS.F144G

/-- WALS 144G values. -/
inductive OptionalDoubleNegationInSvoLanguages where
  /-- SNegVO(Neg) (6 languages). -/
  | snegvo
  /-- S(Neg)VONeg (8 languages). -/
  | svoneg
  /-- S(Neg)VNegO (3 languages). -/
  | svnego
  /-- SNegV(Neg)O (1 languages). -/
  | snegvo_4
  /-- (Neg)SVONeg (2 languages). -/
  | svoneg_5
  /-- SVNegO(Neg) (1 languages). -/
  | svnego_6
  /-- NegS[V(-Neg)]O (1 languages). -/
  | negsVO
  /-- S[(Neg-)V]NegO (1 languages). -/
  | sVNego
  /-- S[Neg-V]O(Neg) (2 languages). -/
  | sNegVO
  /-- SNegVO/SVNegO&NegTone (1 languages). -/
  | snegvoSvnegoNegtone
  /-- S(Neg)[V(-Neg)]O (1 languages). -/
  | sVO
  /-- S[Neg-V(-Neg)]O (2 languages). -/
  | sNegVO_12
  /-- (Neg)SVONeg/S(Neg)VONeg (1 languages). -/
  | svonegSvoneg
  /-- S[Neg-V]O/NegSVNegO (1 languages). -/
  | sNegVONegsvnego
  /-- SNeg[V-Neg]O/S[Neg-V-Neg]O (1 languages). -/
  | snegVNegOSNegVNegO
  /-- S[V(-Neg)]O & NegV (1 languages). -/
  | sVONegv
  /-- SVO/SOV & (Neg)[V-Neg] (1 languages). -/
  | svoSovVNeg
  /-- SVO/VSO & NegV/VNeg/NegVNeg (1 languages). -/
  | svoVsoNegvVnegNegvneg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144G dataset (35 languages). -/
def allData : List (Datapoint OptionalDoubleNegationInSvoLanguages) :=
  [ { walsCode := "adz", language := "Adzera", iso := "adz", value := .sNegVO }
  , { walsCode := "aeg", language := "Arabic (Egyptian)", iso := "arz", value := .snegVNegOSNegVNegO }
  , { walsCode := "arp", language := "Arapesh (Mountain)", iso := "ape", value := .snegvo }
  , { walsCode := "bmb", language := "Bimoba", iso := "bim", value := .snegvo }
  , { walsCode := "bol", language := "Bolia", iso := "bli", value := .sNegVO }
  , { walsCode := "bgo", language := "Bongo", iso := "bot", value := .svoneg }
  , { walsCode := "ctl", language := "Catalan", iso := "cat", value := .snegvo_4 }
  , { walsCode := "chr", language := "Chrau", iso := "crw", value := .snegvo }
  , { walsCode := "cop", language := "Coptic", iso := "cop", value := .sNegVONegsvnego }
  , { walsCode := "dma", language := "Duma", iso := "dma", value := .svnego }
  , { walsCode := "ewo", language := "Ewondo", iso := "ewo", value := .snegvoSvnegoNegtone }
  , { walsCode := "fre", language := "French", iso := "fra", value := .svnego }
  , { walsCode := "fye", language := "Fyem", iso := "pym", value := .svoneg_5 }
  , { walsCode := "gbb", language := "Gbeya Bossangoa", iso := "gbp", value := .svoneg }
  , { walsCode := "hau", language := "Hausa", iso := "hau", value := .snegvo }
  , { walsCode := "mxe", language := "Ifira-Mele", iso := "mxe", value := .sVNego }
  , { walsCode := "ina", language := "Inanwatan", iso := "szp", value := .svoSovVNeg }
  , { walsCode := "kre", language := "Kresh", iso := "krs", value := .svonegSvoneg }
  , { walsCode := "lew", language := "Lewo", iso := "lww", value := .svnego_6 }
  , { walsCode := "mbe", language := "Mbere", iso := "mdt", value := .svnego }
  , { walsCode := "mum", language := "Mumuye", iso := "mzm", value := .svoneg }
  , { walsCode := "mgk", language := "Mungaka", iso := "mhk", value := .svoneg }
  , { walsCode := "mup", language := "Mupun", iso := "sur", value := .svoneg_5 }
  , { walsCode := "nke", language := "Nkem", iso := "isi", value := .sVO }
  , { walsCode := "one", language := "One", iso := "aun", value := .svoneg }
  , { walsCode := "paa", language := "Pa'a", iso := "pqa", value := .svoneg }
  , { walsCode := "plh", language := "Paulohi", iso := "plh", value := .snegvo }
  , { walsCode := "rwe", language := "Romani (Welsh)", iso := "rmw", value := .svoVsoNegvVnegNegvneg }
  , { walsCode := "tmn", language := "Temein", iso := "teq", value := .negsVO }
  , { walsCode := "ter", language := "Tera", iso := "ttr", value := .svoneg }
  , { walsCode := "tid", language := "Tidore", iso := "tvo", value := .svoneg }
  , { walsCode := "urt", language := "Urat", iso := "urt", value := .snegvo }
  , { walsCode := "wrn", language := "Warndarang", iso := "wnd", value := .sNegVO_12 }
  , { walsCode := "zch", language := "Zoque (Chimalapa)", iso := "zoh", value := .sVONegv }
  , { walsCode := "zul", language := "Zulu", iso := "zul", value := .sNegVO_12 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144G
