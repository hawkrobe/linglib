import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144W: Verb-Initial with Negative that is Immediately Postverbal or between Subject and Object
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144W`.

Chapter 144, 151 languages.
-/

namespace Datasets.WALS.F144W

/-- WALS 144W values. -/
inductive VerbInitialWithNegativeThatIsImmediatelyPostverbalOrBetweenSubjectAndObject where
  /-- Suffix&NoDoubleNeg (2 languages). -/
  | suffixNodoubleneg
  /-- Word&OnlyWithAnotherNeg (5 languages). -/
  | wordOnlywithanotherneg
  /-- Suffix&OptDoubleNeg (1 languages). -/
  | suffixOptdoubleneg
  /-- Suffix&OnlyWithAnotherNeg (3 languages). -/
  | suffixOnlywithanotherneg
  /-- WordBetweenSAndO (1 languages). -/
  | wordbetweensando
  /-- None (139 languages). -/
  | none
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144W dataset (151 languages). -/
def allData : List (Datapoint VerbInitialWithNegativeThatIsImmediatelyPostverbalOrBetweenSubjectAndObject) :=
  [ { walsCode := "agc", iso := "agt", value := .none }
  , { walsCode := "agd", iso := "duo", value := .none }
  , { walsCode := "als", iso := "aes", value := .none }
  , { walsCode := "anj", iso := "aty", value := .none }
  , { walsCode := "ann", iso := "aoi", value := .none }
  , { walsCode := "ams", iso := "arb", value := .none }
  , { walsCode := "amr", iso := "ary", value := .suffixOnlywithanotherneg }
  , { walsCode := "asy", iso := "apc", value := .none }
  , { walsCode := "ata", iso := "tay", value := .none }
  , { walsCode := "bwc", iso := "bdr", value := .none }
  , { walsCode := "bbu", iso := "brm", value := .none }
  , { walsCode := "bkr", iso := "btx", value := .none }
  , { walsCode := "bto", iso := "bbc", value := .none }
  , { walsCode := "baq", iso := "brg", value := .none }
  , { walsCode := "bco", iso := "blc", value := .none }
  , { walsCode := "bch", iso := "shy", value := .none }
  , { walsCode := "bfg", iso := "grr", value := .none }
  , { walsCode := "btk", iso := "lbk", value := .none }
  , { walsCode := "cak", iso := "cak", value := .wordOnlywithanotherneg }
  , { walsCode := "cyv", iso := "cyb", value := .none }
  , { walsCode := "cha", iso := "cha", value := .none }
  , { walsCode := "cso", iso := "ctp", value := .none }
  , { walsCode := "cya", iso := "ctp", value := .none }
  , { walsCode := "ccm", iso := "cco", value := .none }
  , { walsCode := "cle", iso := "cle", value := .none }
  , { walsCode := "cpl", iso := "cpa", value := .none }
  , { walsCode := "chq", iso := "chq", value := .none }
  , { walsCode := "ckl", iso := "chh", value := .none }
  , { walsCode := "chx", iso := "clo", value := .none }
  , { walsCode := "chj", iso := "cac", value := .suffixOnlywithanotherneg }
  , { walsCode := "cba", iso := "boi", value := .none }
  , { walsCode := "crn", iso := "cor", value := .none }
  , { walsCode := "cem", iso := "cam", value := .none }
  , { walsCode := "did", iso := "did", value := .none }
  , { walsCode := "dom", iso := "rmt", value := .suffixOptdoubleneg }
  , { walsCode := "dre", iso := "dhv", value := .none }
  , { walsCode := "fij", iso := "fij", value := .none }
  , { walsCode := "gae", iso := "gla", value := .none }
  , { walsCode := "grf", iso := "cab", value := .none }
  , { walsCode := "gel", iso := "nlg", value := .none }
  , { walsCode := "goa", iso := "guc", value := .none }
  , { walsCode := "grk", iso := "ell", value := .none }
  , { walsCode := "gjj", iso := "gub", value := .none }
  , { walsCode := "gku", iso := "pue", value := .none }
  , { walsCode := "hlu", iso := "hur", value := .none }
  , { walsCode := "haw", iso := "haw", value := .none }
  , { walsCode := "hdi", iso := "xed", value := .wordOnlywithanotherneg }
  , { walsCode := "hei", iso := "hei", value := .none }
  , { walsCode := "hil", iso := "hil", value := .none }
  , { walsCode := "hoa", iso := "hoa", value := .none }
  , { walsCode := "ifu", iso := "ifb", value := .none }
  , { walsCode := "ign", iso := "ign", value := .none }
  , { walsCode := "ik", iso := "ikx", value := .none }
  , { walsCode := "iri", iso := "gle", value := .none }
  , { walsCode := "jak", iso := "jac", value := .none }
  , { walsCode := "kbl", iso := "kab", value := .wordOnlywithanotherneg }
  , { walsCode := "kdz", iso := "kzj", value := .none }
  , { walsCode := "kls", iso := "fla", value := .none }
  , { walsCode := "kmj", iso := "kdj", value := .none }
  , { walsCode := "klv", iso := "kij", value := .none }
  , { walsCode := "kri", iso := "kzw", value := .suffixNodoubleneg }
  , { walsCode := "krb", iso := "gil", value := .none }
  , { walsCode := "shp", iso := "yak", value := .none }
  , { walsCode := "kkt", iso := "kkk", value := .none }
  , { walsCode := "kro", iso := "kgo", value := .none }
  , { walsCode := "kuo", iso := "kto", value := .none }
  , { walsCode := "kut", iso := "kut", value := .none }
  , { walsCode := "kyq", iso := "nuk", value := .none }
  , { walsCode := "lac", iso := "lac", value := .none }
  , { walsCode := "lmg", iso := "hia", value := .wordOnlywithanotherneg }
  , { walsCode := "lgu", iso := "lgu", value := .none }
  , { walsCode := "maa", iso := "mas", value := .none }
  , { walsCode := "mch", iso := "mcb", value := .none }
  , { walsCode := "mak", iso := "myh", value := .none }
  , { walsCode := "mal", iso := "plt", value := .none }
  , { walsCode := "mam", iso := "mam", value := .none }
  , { walsCode := "mmn", iso := "mmn", value := .none }
  , { walsCode := "mwb", iso := "mbb", value := .none }
  , { walsCode := "mzc", iso := "maq", value := .suffixNodoubleneg }
  , { walsCode := "meh", iso := "gdq", value := .none }
  , { walsCode := "mxc", iso := "mig", value := .none }
  , { walsCode := "mxj", iso := "mio", value := .none }
  , { walsCode := "mxo", iso := "mie", value := .none }
  , { walsCode := "mxp", iso := "mil", value := .none }
  , { walsCode := "miy", iso := "mkf", value := .wordOnlywithanotherneg }
  , { walsCode := "mov", iso := "mzp", value := .none }
  , { walsCode := "mrl", iso := "mur", value := .none }
  , { walsCode := "msq", iso := "hur", value := .none }
  , { walsCode := "ndr", iso := "wyy", value := .none }
  , { walsCode := "nhh", iso := "", value := .none }
  , { walsCode := "nan", iso := "niq", value := .none }
  , { walsCode := "nia", iso := "nia", value := .none }
  , { walsCode := "nca", iso := "caq", value := .none }
  , { walsCode := "nsg", iso := "ncg", value := .none }
  , { walsCode := "nif", iso := "num", value := .none }
  , { walsCode := "niu", iso := "niu", value := .none }
  , { walsCode := "ood", iso := "ood", value := .none }
  , { walsCode := "oji", iso := "", value := .none }
  , { walsCode := "ond", iso := "one", value := .none }
  , { walsCode := "otm", iso := "ote", value := .none }
  , { walsCode := "pai", iso := "pwn", value := .none }
  , { walsCode := "pnn", iso := "pag", value := .none }
  , { walsCode := "pip", iso := "ppl", value := .none }
  , { walsCode := "pod", iso := "pbi", value := .none }
  , { walsCode := "pkt", iso := "pko", value := .suffixOnlywithanotherneg }
  , { walsCode := "qui", iso := "qui", value := .none }
  , { walsCode := "rap", iso := "rap", value := .none }
  , { walsCode := "rov", iso := "rug", value := .none }
  , { walsCode := "ruk", iso := "dru", value := .none }
  , { walsCode := "cos", iso := "", value := .none }
  , { walsCode := "sam", iso := "smo", value := .none }
  , { walsCode := "see", iso := "trv", value := .none }
  , { walsCode := "sml", iso := "sza", value := .none }
  , { walsCode := "shu", iso := "shs", value := .none }
  , { walsCode := "qum", iso := "qum", value := .none }
  , { walsCode := "so", iso := "teu", value := .none }
  , { walsCode := "squ", iso := "squ", value := .none }
  , { walsCode := "tag", iso := "tgl", value := .none }
  , { walsCode := "tah", iso := "tah", value := .none }
  , { walsCode := "tsk", iso := "taq", value := .none }
  , { walsCode := "tsg", iso := "tsg", value := .none }
  , { walsCode := "tbo", iso := "tbl", value := .none }
  , { walsCode := "tee", iso := "tee", value := .none }
  , { walsCode := "tpn", iso := "ntp", value := .none }
  , { walsCode := "tho", iso := "thp", value := .none }
  , { walsCode := "tim", iso := "tih", value := .none }
  , { walsCode := "tin", iso := "cir", value := .none }
  , { walsCode := "tlp", iso := "tcf", value := .none }
  , { walsCode := "tob", iso := "tob", value := .none }
  , { walsCode := "tke", iso := "tkl", value := .none }
  , { walsCode := "tng", iso := "ton", value := .none }
  , { walsCode := "tri", iso := "trc", value := .none }
  , { walsCode := "tsi", iso := "tsi", value := .none }
  , { walsCode := "tuk", iso := "", value := .none }
  , { walsCode := "tna", iso := "tuv", value := .none }
  , { walsCode := "tzo", iso := "tzo", value := .none }
  , { walsCode := "tzu", iso := "tzj", value := .none }
  , { walsCode := "war", iso := "pav", value := .none }
  , { walsCode := "wrb", iso := "gjm", value := .none }
  , { walsCode := "wel", iso := "cym", value := .none }
  , { walsCode := "wec", iso := "cym", value := .wordbetweensando }
  , { walsCode := "wem", iso := "xww", value := .none }
  , { walsCode := "wya", iso := "wya", value := .none }
  , { walsCode := "yag", iso := "yad", value := .none }
  , { walsCode := "yap", iso := "yap", value := .none }
  , { walsCode := "yok", iso := "yok", value := .none }
  , { walsCode := "zai", iso := "zai", value := .none }
  , { walsCode := "zap", iso := "zaw", value := .none }
  , { walsCode := "zzo", iso := "zpq", value := .none }
  , { walsCode := "zqc", iso := "zoc", value := .none }
  , { walsCode := "zqo", iso := "zoc", value := .none }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144W
