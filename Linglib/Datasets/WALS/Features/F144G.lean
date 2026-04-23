import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144G: Optional Double Negation in SVO languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144G`.

Chapter 144, 35 languages.
-/

namespace Datasets.WALS.F144G

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
  [ { walsCode := "adz", iso := "adz", value := .sNegVO }
  , { walsCode := "aeg", iso := "arz", value := .snegVNegOSNegVNegO }
  , { walsCode := "arp", iso := "ape", value := .snegvo }
  , { walsCode := "bmb", iso := "bim", value := .snegvo }
  , { walsCode := "bol", iso := "bli", value := .sNegVO }
  , { walsCode := "bgo", iso := "bot", value := .svoneg }
  , { walsCode := "ctl", iso := "cat", value := .snegvo_4 }
  , { walsCode := "chr", iso := "crw", value := .snegvo }
  , { walsCode := "cop", iso := "cop", value := .sNegVONegsvnego }
  , { walsCode := "dma", iso := "dma", value := .svnego }
  , { walsCode := "ewo", iso := "ewo", value := .snegvoSvnegoNegtone }
  , { walsCode := "fre", iso := "fra", value := .svnego }
  , { walsCode := "fye", iso := "pym", value := .svoneg_5 }
  , { walsCode := "gbb", iso := "gbp", value := .svoneg }
  , { walsCode := "hau", iso := "hau", value := .snegvo }
  , { walsCode := "mxe", iso := "mxe", value := .sVNego }
  , { walsCode := "ina", iso := "szp", value := .svoSovVNeg }
  , { walsCode := "kre", iso := "krs", value := .svonegSvoneg }
  , { walsCode := "lew", iso := "lww", value := .svnego_6 }
  , { walsCode := "mbe", iso := "mdt", value := .svnego }
  , { walsCode := "mum", iso := "mzm", value := .svoneg }
  , { walsCode := "mgk", iso := "mhk", value := .svoneg }
  , { walsCode := "mup", iso := "sur", value := .svoneg_5 }
  , { walsCode := "nke", iso := "isi", value := .sVO }
  , { walsCode := "one", iso := "aun", value := .svoneg }
  , { walsCode := "paa", iso := "pqa", value := .svoneg }
  , { walsCode := "plh", iso := "plh", value := .snegvo }
  , { walsCode := "rwe", iso := "rmw", value := .svoVsoNegvVnegNegvneg }
  , { walsCode := "tmn", iso := "teq", value := .negsVO }
  , { walsCode := "ter", iso := "ttr", value := .svoneg }
  , { walsCode := "tid", iso := "tvo", value := .svoneg }
  , { walsCode := "urt", iso := "urt", value := .snegvo }
  , { walsCode := "wrn", iso := "wnd", value := .sNegVO_12 }
  , { walsCode := "zch", iso := "zoh", value := .sVONegv }
  , { walsCode := "zul", iso := "zul", value := .sNegVO_12 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144G
