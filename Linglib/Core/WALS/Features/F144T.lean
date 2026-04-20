import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 144T: The Position of Negative Morphemes in Verb-Initial Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 144T`.

Chapter 144, 152 languages.
-/

namespace Core.WALS.F144T

/-- WALS 144T values. -/
inductive PositionOfNegativeMorphemesInVerbInitialLanguages where
  /-- NegVSO (57 languages). -/
  | negvso
  /-- VSNegO (1 languages). -/
  | vsnego
  /-- VSONeg (1 languages). -/
  | vsoneg
  /-- NegVOS (18 languages). -/
  | negvos
  /-- NegVSO/NegVOS (11 languages). -/
  | negvsoNegvos
  /-- NegV & VS & VO (16 languages). -/
  | negvVsVo
  /-- SVO but NegVSO (1 languages). -/
  | svoButNegvso
  /-- [Neg-V]SO (7 languages). -/
  | negVSo
  /-- [Neg-V]OS (2 languages). -/
  | negVOs
  /-- [V-Neg]OS (1 languages). -/
  | vNegOs
  /-- [V-Neg] & VS &VO (1 languages). -/
  | vNegVsVo
  /-- NegVSO/[Neg-V]SO (2 languages). -/
  | negvsoNegVSo
  /-- NegVOS/[Neg-V]OS (1 languages). -/
  | negvosNegVOs
  /-- NegVSO/SNegVO (5 languages). -/
  | negvsoSnegvo
  /-- VSONeg/SVONeg (1 languages). -/
  | vsonegSvoneg
  /-- NegVOS/NegSVO (1 languages). -/
  | negvosNegsvo
  /-- NegVOS/SNegVO (2 languages). -/
  | negvosSnegvo
  /-- [Neg-V]OS/S[Neg-V]O (2 languages). -/
  | negVOsSNegVO
  /-- NegV & VSO/SVO (2 languages). -/
  | negvVsoSvo
  /-- NegV & VOS/SVO (2 languages). -/
  | negvVosSvo
  /-- OptSingleNeg (1 languages). -/
  | optsingleneg
  /-- ObligDoubleNeg (7 languages). -/
  | obligdoubleneg
  /-- OptDoubleNeg (10 languages). -/
  | optdoubleneg
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 144T dataset (152 languages). -/
def allData : List (Datapoint PositionOfNegativeMorphemesInVerbInitialLanguages) :=
  [ { walsCode := "agc", iso := "agt", value := .negvso }
  , { walsCode := "agd", iso := "duo", value := .negvso }
  , { walsCode := "als", iso := "aes", value := .negvVsVo }
  , { walsCode := "anj", iso := "aty", value := .negvos }
  , { walsCode := "ann", iso := "aoi", value := .optdoubleneg }
  , { walsCode := "ams", iso := "arb", value := .negvso }
  , { walsCode := "amr", iso := "ary", value := .obligdoubleneg }
  , { walsCode := "asy", iso := "apc", value := .negvsoSnegvo }
  , { walsCode := "ata", iso := "tay", value := .negvVsVo }
  , { walsCode := "bwc", iso := "bdr", value := .negvVsoSvo }
  , { walsCode := "bbu", iso := "brm", value := .optdoubleneg }
  , { walsCode := "bkr", iso := "btx", value := .negvsoSnegvo }
  , { walsCode := "bto", iso := "bbc", value := .negvos }
  , { walsCode := "baq", iso := "brg", value := .negvos }
  , { walsCode := "bco", iso := "blc", value := .negvso }
  , { walsCode := "bch", iso := "shy", value := .negvsoSnegvo }
  , { walsCode := "bfg", iso := "grr", value := .negvso }
  , { walsCode := "btk", iso := "lbk", value := .negvVsoSvo }
  , { walsCode := "cak", iso := "cak", value := .obligdoubleneg }
  , { walsCode := "cyv", iso := "cyb", value := .negVOs }
  , { walsCode := "cha", iso := "cha", value := .negvso }
  , { walsCode := "cso", iso := "ctp", value := .negvso }
  , { walsCode := "cya", iso := "ctp", value := .negvso }
  , { walsCode := "ccm", iso := "cco", value := .negVSo }
  , { walsCode := "cle", iso := "cle", value := .negvos }
  , { walsCode := "cpl", iso := "cpa", value := .negVSo }
  , { walsCode := "chq", iso := "chq", value := .negvso }
  , { walsCode := "ckl", iso := "chh", value := .negvos }
  , { walsCode := "chx", iso := "clo", value := .negvVsVo }
  , { walsCode := "chj", iso := "cac", value := .optdoubleneg }
  , { walsCode := "cba", iso := "boi", value := .negVOs }
  , { walsCode := "crn", iso := "cor", value := .svoButNegvso }
  , { walsCode := "cem", iso := "cam", value := .negvos }
  , { walsCode := "did", iso := "did", value := .negvso }
  , { walsCode := "dom", iso := "rmt", value := .optdoubleneg }
  , { walsCode := "dre", iso := "dhv", value := .negvosNegsvo }
  , { walsCode := "fij", iso := "fij", value := .negvsoNegvos }
  , { walsCode := "gae", iso := "gla", value := .negvso }
  , { walsCode := "grf", iso := "cab", value := .negvso }
  , { walsCode := "gel", iso := "nlg", value := .negvos }
  , { walsCode := "goa", iso := "guc", value := .negvso }
  , { walsCode := "grk", iso := "ell", value := .negvsoSnegvo }
  , { walsCode := "gjj", iso := "gub", value := .negVSo }
  , { walsCode := "gku", iso := "pue", value := .negVOsSNegVO }
  , { walsCode := "hlu", iso := "hur", value := .negvso }
  , { walsCode := "haw", iso := "haw", value := .negvso }
  , { walsCode := "hdi", iso := "xed", value := .obligdoubleneg }
  , { walsCode := "hei", iso := "hei", value := .negvso }
  , { walsCode := "hil", iso := "hil", value := .negvso }
  , { walsCode := "hoa", iso := "hoa", value := .negvso }
  , { walsCode := "ifu", iso := "ifb", value := .negvVsVo }
  , { walsCode := "ign", iso := "ign", value := .negvVsVo }
  , { walsCode := "ik", iso := "ikx", value := .negvso }
  , { walsCode := "iri", iso := "gle", value := .negvso }
  , { walsCode := "jak", iso := "jac", value := .negvso }
  , { walsCode := "kbl", iso := "kab", value := .obligdoubleneg }
  , { walsCode := "kdz", iso := "kzj", value := .negvso }
  , { walsCode := "kls", iso := "fla", value := .negvso }
  , { walsCode := "kmj", iso := "kdj", value := .negvsoNegVSo }
  , { walsCode := "klv", iso := "kij", value := .negvVosSvo }
  , { walsCode := "kri", iso := "kzw", value := .vNegOs }
  , { walsCode := "krb", iso := "gil", value := .negvos }
  , { walsCode := "shp", iso := "yak", value := .negvso }
  , { walsCode := "kkt", iso := "kkk", value := .negvso }
  , { walsCode := "kro", iso := "kgo", value := .obligdoubleneg }
  , { walsCode := "kuo", iso := "kto", value := .negvso }
  , { walsCode := "kut", iso := "kut", value := .negvsoNegvos }
  , { walsCode := "kyq", iso := "nuk", value := .negvso }
  , { walsCode := "lac", iso := "lac", value := .negvVosSvo }
  , { walsCode := "lmg", iso := "hia", value := .optdoubleneg }
  , { walsCode := "lgu", iso := "lgu", value := .negvos }
  , { walsCode := "maa", iso := "mas", value := .negvsoNegVSo }
  , { walsCode := "mch", iso := "mcb", value := .negvVsVo }
  , { walsCode := "mak", iso := "myh", value := .negvso }
  , { walsCode := "mal", iso := "plt", value := .negvos }
  , { walsCode := "mam", iso := "mam", value := .negvso }
  , { walsCode := "mmn", iso := "mmn", value := .negvso }
  , { walsCode := "mwb", iso := "mbb", value := .negvso }
  , { walsCode := "mzc", iso := "maq", value := .vNegVsVo }
  , { walsCode := "meh", iso := "gdq", value := .vsonegSvoneg }
  , { walsCode := "mxc", iso := "mig", value := .negvso }
  , { walsCode := "mxj", iso := "mio", value := .negvso }
  , { walsCode := "mxo", iso := "mie", value := .negvso }
  , { walsCode := "mxp", iso := "mil", value := .negvso }
  , { walsCode := "miy", iso := "mkf", value := .obligdoubleneg }
  , { walsCode := "mov", iso := "mzp", value := .negvsoNegvos }
  , { walsCode := "mrl", iso := "mur", value := .negvso }
  , { walsCode := "msq", iso := "hur", value := .negvso }
  , { walsCode := "ndr", iso := "wyy", value := .negvVsVo }
  , { walsCode := "nhh", iso := "", value := .negvso }
  , { walsCode := "nan", iso := "niq", value := .negVSo }
  , { walsCode := "nia", iso := "nia", value := .negvos }
  , { walsCode := "nca", iso := "caq", value := .negvos }
  , { walsCode := "nsg", iso := "ncg", value := .negvso }
  , { walsCode := "nif", iso := "num", value := .negvso }
  , { walsCode := "niu", iso := "niu", value := .negvso }
  , { walsCode := "ood", iso := "ood", value := .negvVsVo }
  , { walsCode := "oji", iso := "", value := .negvsoNegvos }
  , { walsCode := "ond", iso := "one", value := .optdoubleneg }
  , { walsCode := "otm", iso := "ote", value := .negvos }
  , { walsCode := "pai", iso := "pwn", value := .negvsoNegvos }
  , { walsCode := "pnn", iso := "pag", value := .negvso }
  , { walsCode := "pip", iso := "ppl", value := .negvVsVo }
  , { walsCode := "pod", iso := "pbi", value := .vsoneg }
  , { walsCode := "pkt", iso := "pko", value := .optdoubleneg }
  , { walsCode := "qui", iso := "qui", value := .negvso }
  , { walsCode := "rap", iso := "rap", value := .optdoubleneg }
  , { walsCode := "rwe", iso := "rmw", value := .optdoubleneg }
  , { walsCode := "rov", iso := "rug", value := .negvso }
  , { walsCode := "ruk", iso := "dru", value := .negvsoNegvos }
  , { walsCode := "cos", iso := "", value := .negvVsVo }
  , { walsCode := "sam", iso := "smo", value := .negvsoNegvos }
  , { walsCode := "see", iso := "trv", value := .negvos }
  , { walsCode := "sml", iso := "sza", value := .negvsoNegvos }
  , { walsCode := "shu", iso := "shs", value := .negvsoNegvos }
  , { walsCode := "qum", iso := "qum", value := .negvso }
  , { walsCode := "so", iso := "teu", value := .negvso }
  , { walsCode := "squ", iso := "squ", value := .negvso }
  , { walsCode := "tag", iso := "tgl", value := .negvso }
  , { walsCode := "tah", iso := "tah", value := .negvso }
  , { walsCode := "tsk", iso := "taq", value := .optdoubleneg }
  , { walsCode := "tsg", iso := "tsg", value := .negvVsVo }
  , { walsCode := "tbo", iso := "tbl", value := .negvso }
  , { walsCode := "tee", iso := "tee", value := .negvsoSnegvo }
  , { walsCode := "tpn", iso := "ntp", value := .negvso }
  , { walsCode := "tho", iso := "thp", value := .negvsoNegvos }
  , { walsCode := "tim", iso := "tih", value := .negvso }
  , { walsCode := "tin", iso := "cir", value := .negvosSnegvo }
  , { walsCode := "tlp", iso := "tcf", value := .negVSo }
  , { walsCode := "tob", iso := "tob", value := .negVOsSNegVO }
  , { walsCode := "tke", iso := "tkl", value := .negvVsVo }
  , { walsCode := "tng", iso := "ton", value := .negvsoNegvos }
  , { walsCode := "tri", iso := "trc", value := .negvso }
  , { walsCode := "tsi", iso := "tsi", value := .obligdoubleneg }
  , { walsCode := "tuk", iso := "", value := .negvos }
  , { walsCode := "tna", iso := "tuv", value := .negVSo }
  , { walsCode := "tzo", iso := "tzo", value := .negvos }
  , { walsCode := "tzu", iso := "tzj", value := .negvosSnegvo }
  , { walsCode := "war", iso := "pav", value := .negvos }
  , { walsCode := "wrb", iso := "gjm", value := .negvVsVo }
  , { walsCode := "wel", iso := "cym", value := .negvso }
  , { walsCode := "wec", iso := "cym", value := .vsnego }
  , { walsCode := "wem", iso := "xww", value := .negvos }
  , { walsCode := "wya", iso := "wya", value := .optsingleneg }
  , { walsCode := "yag", iso := "yad", value := .negvVsVo }
  , { walsCode := "yap", iso := "yap", value := .negvso }
  , { walsCode := "yok", iso := "yok", value := .negvVsVo }
  , { walsCode := "zai", iso := "zai", value := .negvso }
  , { walsCode := "zap", iso := "zaw", value := .negVSo }
  , { walsCode := "zzo", iso := "zpq", value := .negvso }
  , { walsCode := "zqc", iso := "zoc", value := .negvosNegVOs }
  , { walsCode := "zqo", iso := "zoc", value := .negvVsVo }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F144T
