import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 144V: Verb-Initial with Preverbal Negative
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144V`.

Chapter 144, 152 languages.
-/

namespace Datasets.WALS.F144V

/-- WALS 144V values. -/
inductive VerbInitialWithPreverbalNegative where
  /-- Separate word, no double negation  Word&NoDoubleNeg (117 languages). -/
  | separateWordNoDoubleNegationWordNodoubleneg
  /-- Prefix, no double negation  Prefix&NoDoubleNeg (11 languages). -/
  | prefixNoDoubleNegationPrefixNodoubleneg
  /-- Word&Opt (6 languages). -/
  | wordOpt
  /-- Prefix&OptDoubleNeg (1 languages). -/
  | prefixOptdoubleneg
  /-- Word&OnlyWithAnotherNeg (4 languages). -/
  | wordOnlywithanotherneg
  /-- Prefix&OnlyWithAnotherNeg (1 languages). -/
  | prefixOnlywithanotherneg
  /-- Type 1 / Type 2 (4 languages). -/
  | type1Type2
  /-- Type 3 / Type 6 (1 languages). -/
  | type3Type6
  /-- No preverbal neg (7 languages). -/
  | noPreverbalNeg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144V dataset (152 languages). -/
def allData : List (Datapoint VerbInitialWithPreverbalNegative) :=
  [ { walsCode := "agc", iso := "agt", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "agd", iso := "duo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "als", iso := "aes", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "anj", iso := "aty", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ann", iso := "aoi", value := .wordOpt }
  , { walsCode := "ams", iso := "arb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "amr", iso := "ary", value := .prefixOnlywithanotherneg }
  , { walsCode := "asy", iso := "apc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ata", iso := "tay", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bwc", iso := "bdr", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bbu", iso := "brm", value := .prefixOptdoubleneg }
  , { walsCode := "bkr", iso := "btx", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bto", iso := "bbc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "baq", iso := "brg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bco", iso := "blc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bch", iso := "shy", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "bfg", iso := "grr", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "btk", iso := "lbk", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cak", iso := "cak", value := .wordOnlywithanotherneg }
  , { walsCode := "cyv", iso := "cyb", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "cha", iso := "cha", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cso", iso := "ctp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cya", iso := "ctp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ccm", iso := "cco", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "cle", iso := "cle", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cpl", iso := "cpa", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "chq", iso := "chq", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ckl", iso := "chh", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "chx", iso := "clo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "chj", iso := "cac", value := .wordOpt }
  , { walsCode := "cba", iso := "boi", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "crn", iso := "cor", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cem", iso := "cam", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "did", iso := "did", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "dom", iso := "rmt", value := .type1Type2 }
  , { walsCode := "dre", iso := "dhv", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "fij", iso := "fij", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "gae", iso := "gla", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "grf", iso := "cab", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "gel", iso := "nlg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "goa", iso := "guc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "grk", iso := "ell", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "gjj", iso := "gub", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "gku", iso := "pue", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "hlu", iso := "hur", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "haw", iso := "haw", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "hdi", iso := "xed", value := .noPreverbalNeg }
  , { walsCode := "hei", iso := "hei", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "hil", iso := "hil", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "hoa", iso := "hoa", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ifu", iso := "ifb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ign", iso := "ign", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ik", iso := "ikx", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "iri", iso := "gle", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "jak", iso := "jac", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kbl", iso := "kab", value := .wordOnlywithanotherneg }
  , { walsCode := "kdz", iso := "kzj", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kls", iso := "fla", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kmj", iso := "kdj", value := .type1Type2 }
  , { walsCode := "klv", iso := "kij", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kri", iso := "kzw", value := .noPreverbalNeg }
  , { walsCode := "krb", iso := "gil", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "shp", iso := "yak", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kkt", iso := "kkk", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kro", iso := "kgo", value := .wordOnlywithanotherneg }
  , { walsCode := "kuo", iso := "kto", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kut", iso := "kut", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "kyq", iso := "nuk", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "lac", iso := "lac", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "lmg", iso := "hia", value := .noPreverbalNeg }
  , { walsCode := "lgu", iso := "lgu", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "maa", iso := "mas", value := .type1Type2 }
  , { walsCode := "mch", iso := "mcb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mak", iso := "myh", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mal", iso := "plt", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mam", iso := "mam", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mmn", iso := "mmn", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mwb", iso := "mbb", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mzc", iso := "maq", value := .noPreverbalNeg }
  , { walsCode := "meh", iso := "gdq", value := .noPreverbalNeg }
  , { walsCode := "mxc", iso := "mig", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mxj", iso := "mio", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mxo", iso := "mie", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mxp", iso := "mil", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "miy", iso := "mkf", value := .wordOnlywithanotherneg }
  , { walsCode := "mov", iso := "mzp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "mrl", iso := "mur", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "msq", iso := "hur", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ndr", iso := "wyy", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nhh", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nan", iso := "niq", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "nia", iso := "nia", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nca", iso := "caq", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nsg", iso := "ncg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "nif", iso := "num", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "niu", iso := "niu", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ood", iso := "ood", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "oji", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ond", iso := "one", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "otm", iso := "ote", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pai", iso := "pwn", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pnn", iso := "pag", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pip", iso := "ppl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "pod", iso := "pbi", value := .noPreverbalNeg }
  , { walsCode := "pkt", iso := "pko", value := .type3Type6 }
  , { walsCode := "qui", iso := "qui", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "rap", iso := "rap", value := .wordOpt }
  , { walsCode := "rwe", iso := "rmw", value := .wordOpt }
  , { walsCode := "rov", iso := "rug", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "ruk", iso := "dru", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "cos", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "sam", iso := "smo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "see", iso := "trv", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "sml", iso := "sza", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "shu", iso := "shs", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "qum", iso := "qum", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "so", iso := "teu", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "squ", iso := "squ", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tag", iso := "tgl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tah", iso := "tah", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tsk", iso := "taq", value := .wordOpt }
  , { walsCode := "tsg", iso := "tsg", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tbo", iso := "tbl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tee", iso := "tee", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tpn", iso := "ntp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tho", iso := "thp", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tim", iso := "tih", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tin", iso := "cir", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tlp", iso := "tcf", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "tob", iso := "tob", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "tke", iso := "tkl", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tng", iso := "ton", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tri", iso := "trc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tsi", iso := "tsi", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tuk", iso := "", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tna", iso := "tuv", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "tzo", iso := "tzo", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "tzu", iso := "tzj", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "war", iso := "pav", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wrb", iso := "gjm", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wel", iso := "cym", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wec", iso := "cym", value := .noPreverbalNeg }
  , { walsCode := "wem", iso := "xww", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "wya", iso := "wya", value := .wordOpt }
  , { walsCode := "yag", iso := "yad", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "yap", iso := "yap", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "yok", iso := "yok", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "zai", iso := "zai", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "zap", iso := "zaw", value := .prefixNoDoubleNegationPrefixNodoubleneg }
  , { walsCode := "zzo", iso := "zpq", value := .separateWordNoDoubleNegationWordNodoubleneg }
  , { walsCode := "zqc", iso := "zoc", value := .type1Type2 }
  , { walsCode := "zqo", iso := "zoc", value := .separateWordNoDoubleNegationWordNodoubleneg }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F144V
