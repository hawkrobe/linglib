import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144X: Verb-Initial with Clause-Final Negative
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144X`.

Chapter 144, 151 languages.
-/

namespace Core.WALS.F144X

/-- WALS 144X values. -/
inductive VerbInitialWithClauseFinalNegative where
  /-- NoDoubleNeg (2 languages). -/
  | nodoubleneg
  /-- OptDoubleNeg (1 languages). -/
  | optdoubleneg
  /-- OnlyWithAnotherNeg (4 languages). -/
  | onlywithanotherneg
  /-- No clause-final neg (144 languages). -/
  | noClauseFinalNeg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144X dataset (151 languages). -/
def allData : List (Datapoint VerbInitialWithClauseFinalNegative) :=
  [ { walsCode := "agc", iso := "agt", value := .noClauseFinalNeg }
  , { walsCode := "agd", iso := "duo", value := .noClauseFinalNeg }
  , { walsCode := "als", iso := "aes", value := .noClauseFinalNeg }
  , { walsCode := "anj", iso := "aty", value := .noClauseFinalNeg }
  , { walsCode := "ann", iso := "aoi", value := .noClauseFinalNeg }
  , { walsCode := "ams", iso := "arb", value := .noClauseFinalNeg }
  , { walsCode := "amr", iso := "ary", value := .noClauseFinalNeg }
  , { walsCode := "asy", iso := "apc", value := .noClauseFinalNeg }
  , { walsCode := "ata", iso := "tay", value := .noClauseFinalNeg }
  , { walsCode := "bwc", iso := "bdr", value := .noClauseFinalNeg }
  , { walsCode := "bbu", iso := "brm", value := .onlywithanotherneg }
  , { walsCode := "bkr", iso := "btx", value := .noClauseFinalNeg }
  , { walsCode := "bto", iso := "bbc", value := .noClauseFinalNeg }
  , { walsCode := "baq", iso := "brg", value := .noClauseFinalNeg }
  , { walsCode := "bco", iso := "blc", value := .noClauseFinalNeg }
  , { walsCode := "bch", iso := "shy", value := .noClauseFinalNeg }
  , { walsCode := "bfg", iso := "grr", value := .noClauseFinalNeg }
  , { walsCode := "btk", iso := "lbk", value := .noClauseFinalNeg }
  , { walsCode := "cak", iso := "cak", value := .noClauseFinalNeg }
  , { walsCode := "cyv", iso := "cyb", value := .noClauseFinalNeg }
  , { walsCode := "cha", iso := "cha", value := .noClauseFinalNeg }
  , { walsCode := "cso", iso := "ctp", value := .noClauseFinalNeg }
  , { walsCode := "cya", iso := "ctp", value := .noClauseFinalNeg }
  , { walsCode := "ccm", iso := "cco", value := .noClauseFinalNeg }
  , { walsCode := "cle", iso := "cle", value := .noClauseFinalNeg }
  , { walsCode := "cpl", iso := "cpa", value := .noClauseFinalNeg }
  , { walsCode := "chq", iso := "chq", value := .noClauseFinalNeg }
  , { walsCode := "ckl", iso := "chh", value := .noClauseFinalNeg }
  , { walsCode := "chx", iso := "clo", value := .noClauseFinalNeg }
  , { walsCode := "chj", iso := "cac", value := .noClauseFinalNeg }
  , { walsCode := "cba", iso := "boi", value := .noClauseFinalNeg }
  , { walsCode := "crn", iso := "cor", value := .noClauseFinalNeg }
  , { walsCode := "cem", iso := "cam", value := .noClauseFinalNeg }
  , { walsCode := "did", iso := "did", value := .noClauseFinalNeg }
  , { walsCode := "dom", iso := "rmt", value := .noClauseFinalNeg }
  , { walsCode := "dre", iso := "dhv", value := .noClauseFinalNeg }
  , { walsCode := "fij", iso := "fij", value := .noClauseFinalNeg }
  , { walsCode := "gae", iso := "gla", value := .noClauseFinalNeg }
  , { walsCode := "grf", iso := "cab", value := .noClauseFinalNeg }
  , { walsCode := "gel", iso := "nlg", value := .noClauseFinalNeg }
  , { walsCode := "goa", iso := "guc", value := .noClauseFinalNeg }
  , { walsCode := "grk", iso := "ell", value := .noClauseFinalNeg }
  , { walsCode := "gjj", iso := "gub", value := .noClauseFinalNeg }
  , { walsCode := "gku", iso := "pue", value := .noClauseFinalNeg }
  , { walsCode := "hlu", iso := "hur", value := .noClauseFinalNeg }
  , { walsCode := "haw", iso := "haw", value := .noClauseFinalNeg }
  , { walsCode := "hdi", iso := "xed", value := .onlywithanotherneg }
  , { walsCode := "hei", iso := "hei", value := .noClauseFinalNeg }
  , { walsCode := "hil", iso := "hil", value := .noClauseFinalNeg }
  , { walsCode := "hoa", iso := "hoa", value := .noClauseFinalNeg }
  , { walsCode := "ifu", iso := "ifb", value := .noClauseFinalNeg }
  , { walsCode := "ign", iso := "ign", value := .noClauseFinalNeg }
  , { walsCode := "ik", iso := "ikx", value := .noClauseFinalNeg }
  , { walsCode := "iri", iso := "gle", value := .noClauseFinalNeg }
  , { walsCode := "jak", iso := "jac", value := .noClauseFinalNeg }
  , { walsCode := "kbl", iso := "kab", value := .noClauseFinalNeg }
  , { walsCode := "kdz", iso := "kzj", value := .noClauseFinalNeg }
  , { walsCode := "kls", iso := "fla", value := .noClauseFinalNeg }
  , { walsCode := "kmj", iso := "kdj", value := .noClauseFinalNeg }
  , { walsCode := "klv", iso := "kij", value := .noClauseFinalNeg }
  , { walsCode := "kri", iso := "kzw", value := .noClauseFinalNeg }
  , { walsCode := "krb", iso := "gil", value := .noClauseFinalNeg }
  , { walsCode := "shp", iso := "yak", value := .noClauseFinalNeg }
  , { walsCode := "kkt", iso := "kkk", value := .noClauseFinalNeg }
  , { walsCode := "kro", iso := "kgo", value := .onlywithanotherneg }
  , { walsCode := "kuo", iso := "kto", value := .noClauseFinalNeg }
  , { walsCode := "kut", iso := "kut", value := .noClauseFinalNeg }
  , { walsCode := "kyq", iso := "nuk", value := .noClauseFinalNeg }
  , { walsCode := "lac", iso := "lac", value := .noClauseFinalNeg }
  , { walsCode := "lmg", iso := "hia", value := .optdoubleneg }
  , { walsCode := "lgu", iso := "lgu", value := .noClauseFinalNeg }
  , { walsCode := "maa", iso := "mas", value := .noClauseFinalNeg }
  , { walsCode := "mch", iso := "mcb", value := .noClauseFinalNeg }
  , { walsCode := "mak", iso := "myh", value := .noClauseFinalNeg }
  , { walsCode := "mal", iso := "plt", value := .noClauseFinalNeg }
  , { walsCode := "mam", iso := "mam", value := .noClauseFinalNeg }
  , { walsCode := "mmn", iso := "mmn", value := .noClauseFinalNeg }
  , { walsCode := "mwb", iso := "mbb", value := .noClauseFinalNeg }
  , { walsCode := "mzc", iso := "maq", value := .noClauseFinalNeg }
  , { walsCode := "meh", iso := "gdq", value := .nodoubleneg }
  , { walsCode := "mxc", iso := "mig", value := .noClauseFinalNeg }
  , { walsCode := "mxj", iso := "mio", value := .noClauseFinalNeg }
  , { walsCode := "mxo", iso := "mie", value := .noClauseFinalNeg }
  , { walsCode := "mxp", iso := "mil", value := .noClauseFinalNeg }
  , { walsCode := "miy", iso := "mkf", value := .onlywithanotherneg }
  , { walsCode := "mov", iso := "mzp", value := .noClauseFinalNeg }
  , { walsCode := "mrl", iso := "mur", value := .noClauseFinalNeg }
  , { walsCode := "msq", iso := "hur", value := .noClauseFinalNeg }
  , { walsCode := "ndr", iso := "wyy", value := .noClauseFinalNeg }
  , { walsCode := "nhh", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "nan", iso := "niq", value := .noClauseFinalNeg }
  , { walsCode := "nia", iso := "nia", value := .noClauseFinalNeg }
  , { walsCode := "nca", iso := "caq", value := .noClauseFinalNeg }
  , { walsCode := "nsg", iso := "ncg", value := .noClauseFinalNeg }
  , { walsCode := "nif", iso := "num", value := .noClauseFinalNeg }
  , { walsCode := "niu", iso := "niu", value := .noClauseFinalNeg }
  , { walsCode := "ood", iso := "ood", value := .noClauseFinalNeg }
  , { walsCode := "oji", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "ond", iso := "one", value := .noClauseFinalNeg }
  , { walsCode := "otm", iso := "ote", value := .noClauseFinalNeg }
  , { walsCode := "pai", iso := "pwn", value := .noClauseFinalNeg }
  , { walsCode := "pnn", iso := "pag", value := .noClauseFinalNeg }
  , { walsCode := "pip", iso := "ppl", value := .noClauseFinalNeg }
  , { walsCode := "pod", iso := "pbi", value := .nodoubleneg }
  , { walsCode := "pkt", iso := "pko", value := .noClauseFinalNeg }
  , { walsCode := "qui", iso := "qui", value := .noClauseFinalNeg }
  , { walsCode := "rap", iso := "rap", value := .noClauseFinalNeg }
  , { walsCode := "rov", iso := "rug", value := .noClauseFinalNeg }
  , { walsCode := "ruk", iso := "dru", value := .noClauseFinalNeg }
  , { walsCode := "cos", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "sam", iso := "smo", value := .noClauseFinalNeg }
  , { walsCode := "see", iso := "trv", value := .noClauseFinalNeg }
  , { walsCode := "sml", iso := "sza", value := .noClauseFinalNeg }
  , { walsCode := "shu", iso := "shs", value := .noClauseFinalNeg }
  , { walsCode := "qum", iso := "qum", value := .noClauseFinalNeg }
  , { walsCode := "so", iso := "teu", value := .noClauseFinalNeg }
  , { walsCode := "squ", iso := "squ", value := .noClauseFinalNeg }
  , { walsCode := "tag", iso := "tgl", value := .noClauseFinalNeg }
  , { walsCode := "tah", iso := "tah", value := .noClauseFinalNeg }
  , { walsCode := "tsk", iso := "taq", value := .noClauseFinalNeg }
  , { walsCode := "tsg", iso := "tsg", value := .noClauseFinalNeg }
  , { walsCode := "tbo", iso := "tbl", value := .noClauseFinalNeg }
  , { walsCode := "tee", iso := "tee", value := .noClauseFinalNeg }
  , { walsCode := "tpn", iso := "ntp", value := .noClauseFinalNeg }
  , { walsCode := "tho", iso := "thp", value := .noClauseFinalNeg }
  , { walsCode := "tim", iso := "tih", value := .noClauseFinalNeg }
  , { walsCode := "tin", iso := "cir", value := .noClauseFinalNeg }
  , { walsCode := "tlp", iso := "tcf", value := .noClauseFinalNeg }
  , { walsCode := "tob", iso := "tob", value := .noClauseFinalNeg }
  , { walsCode := "tke", iso := "tkl", value := .noClauseFinalNeg }
  , { walsCode := "tng", iso := "ton", value := .noClauseFinalNeg }
  , { walsCode := "tri", iso := "trc", value := .noClauseFinalNeg }
  , { walsCode := "tsi", iso := "tsi", value := .noClauseFinalNeg }
  , { walsCode := "tuk", iso := "", value := .noClauseFinalNeg }
  , { walsCode := "tna", iso := "tuv", value := .noClauseFinalNeg }
  , { walsCode := "tzo", iso := "tzo", value := .noClauseFinalNeg }
  , { walsCode := "tzu", iso := "tzj", value := .noClauseFinalNeg }
  , { walsCode := "war", iso := "pav", value := .noClauseFinalNeg }
  , { walsCode := "wrb", iso := "gjm", value := .noClauseFinalNeg }
  , { walsCode := "wel", iso := "cym", value := .noClauseFinalNeg }
  , { walsCode := "wec", iso := "cym", value := .noClauseFinalNeg }
  , { walsCode := "wem", iso := "xww", value := .noClauseFinalNeg }
  , { walsCode := "wya", iso := "wya", value := .noClauseFinalNeg }
  , { walsCode := "yag", iso := "yad", value := .noClauseFinalNeg }
  , { walsCode := "yap", iso := "yap", value := .noClauseFinalNeg }
  , { walsCode := "yok", iso := "yok", value := .noClauseFinalNeg }
  , { walsCode := "zai", iso := "zai", value := .noClauseFinalNeg }
  , { walsCode := "zap", iso := "zaw", value := .noClauseFinalNeg }
  , { walsCode := "zzo", iso := "zpq", value := .noClauseFinalNeg }
  , { walsCode := "zqc", iso := "zoc", value := .noClauseFinalNeg }
  , { walsCode := "zqo", iso := "zoc", value := .noClauseFinalNeg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144X
