import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 21A: Exponence of Selected Inflectional Formatives
@cite{bickel-nichols-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 21A`.

Chapter 21, 162 languages.
-/

namespace Datasets.WALS.F21A

/-- WALS 21A values. -/
inductive ExponenceType where
  /-- Monoexponential case (71 languages). -/
  | monoexponentialCase
  /-- Case + number (8 languages). -/
  | caseNumber
  /-- Case + referentiality (6 languages). -/
  | caseReferentiality
  /-- Case + TAM (2 languages). -/
  | caseTam
  /-- No case (75 languages). -/
  | noCase
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 21A dataset (162 languages). -/
def allData : List (Datapoint ExponenceType) :=
  [ { walsCode := "abi", iso := "axb", value := .noCase }
  , { walsCode := "abk", iso := "abk", value := .noCase }
  , { walsCode := "aco", iso := "kjq", value := .noCase }
  , { walsCode := "ala", iso := "amp", value := .noCase }
  , { walsCode := "ame", iso := "aey", value := .noCase }
  , { walsCode := "apu", iso := "apu", value := .noCase }
  , { walsCode := "aeg", iso := "arz", value := .noCase }
  , { walsCode := "ana", iso := "aro", value := .monoexponentialCase }
  , { walsCode := "arp", iso := "ape", value := .noCase }
  , { walsCode := "amp", iso := "aer", value := .monoexponentialCase }
  , { walsCode := "asm", iso := "cns", value := .noCase }
  , { walsCode := "atk", iso := "aqp", value := .noCase }
  , { walsCode := "awp", iso := "kwi", value := .monoexponentialCase }
  , { walsCode := "aym", iso := "ayr", value := .monoexponentialCase }
  , { walsCode := "bag", iso := "bmi", value := .noCase }
  , { walsCode := "bnj", iso := "bdy", value := .monoexponentialCase }
  , { walsCode := "brs", iso := "bsn", value := .monoexponentialCase }
  , { walsCode := "bsq", iso := "eus", value := .monoexponentialCase }
  , { walsCode := "bej", iso := "bej", value := .monoexponentialCase }
  , { walsCode := "bel", iso := "byw", value := .monoexponentialCase }
  , { walsCode := "bma", iso := "tzm", value := .monoexponentialCase }
  , { walsCode := "bbw", iso := "gup", value := .noCase }
  , { walsCode := "brr", iso := "bor", value := .noCase }
  , { walsCode := "brh", iso := "brh", value := .monoexponentialCase }
  , { walsCode := "brm", iso := "mya", value := .monoexponentialCase }
  , { walsCode := "bur", iso := "bsk", value := .monoexponentialCase }
  , { walsCode := "cah", iso := "chl", value := .monoexponentialCase }
  , { walsCode := "cnl", iso := "ram", value := .noCase }
  , { walsCode := "cyv", iso := "cyb", value := .noCase }
  , { walsCode := "cha", iso := "cha", value := .noCase }
  , { walsCode := "cku", iso := "wac", value := .noCase }
  , { walsCode := "cho", iso := "chd", value := .noCase }
  , { walsCode := "chk", iso := "ckt", value := .caseNumber }
  , { walsCode := "ccp", iso := "coc", value := .monoexponentialCase }
  , { walsCode := "cre", iso := "crk", value := .caseReferentiality }
  , { walsCode := "dag", iso := "dgz", value := .noCase }
  , { walsCode := "dni", iso := "dni", value := .noCase }
  , { walsCode := "dig", iso := "mhu", value := .monoexponentialCase }
  , { walsCode := "eka", iso := "ekg", value := .noCase }
  , { walsCode := "eng", iso := "eng", value := .noCase }
  , { walsCode := "epe", iso := "sja", value := .monoexponentialCase }
  , { walsCode := "eve", iso := "evn", value := .caseReferentiality }
  , { walsCode := "fij", iso := "fij", value := .noCase }
  , { walsCode := "fin", iso := "fin", value := .caseNumber }
  , { walsCode := "fre", iso := "fra", value := .noCase }
  , { walsCode := "gar", iso := "grt", value := .monoexponentialCase }
  , { walsCode := "geo", iso := "kat", value := .monoexponentialCase }
  , { walsCode := "ger", iso := "deu", value := .caseNumber }
  , { walsCode := "goo", iso := "gni", value := .monoexponentialCase }
  , { walsCode := "grb", iso := "grj", value := .noCase }
  , { walsCode := "grk", iso := "ell", value := .caseNumber }
  , { walsCode := "grw", iso := "kal", value := .caseNumber }
  , { walsCode := "gua", iso := "gug", value := .noCase }
  , { walsCode := "hai", iso := "hai", value := .noCase }
  , { walsCode := "hat", iso := "had", value := .noCase }
  , { walsCode := "hau", iso := "hau", value := .noCase }
  , { walsCode := "heb", iso := "heb", value := .noCase }
  , { walsCode := "hin", iso := "hin", value := .monoexponentialCase }
  , { walsCode := "hix", iso := "hix", value := .noCase }
  , { walsCode := "hmo", iso := "hnj", value := .noCase }
  , { walsCode := "hve", iso := "huv", value := .noCase }
  , { walsCode := "hun", iso := "hun", value := .monoexponentialCase }
  , { walsCode := "hzb", iso := "huz", value := .monoexponentialCase }
  , { walsCode := "iau", iso := "tmu", value := .noCase }
  , { walsCode := "imo", iso := "imn", value := .monoexponentialCase }
  , { walsCode := "ind", iso := "ind", value := .noCase }
  , { walsCode := "ing", iso := "inh", value := .monoexponentialCase }
  , { walsCode := "jak", iso := "jac", value := .noCase }
  , { walsCode := "jpn", iso := "jpn", value := .monoexponentialCase }
  , { walsCode := "jel", iso := "jek", value := .noCase }
  , { walsCode := "knd", iso := "kan", value := .monoexponentialCase }
  , { walsCode := "krk", iso := "kyh", value := .noCase }
  , { walsCode := "kay", iso := "gyd", value := .caseTam }
  , { walsCode := "ket", iso := "ket", value := .noCase }
  , { walsCode := "kew", iso := "kew", value := .monoexponentialCase }
  , { walsCode := "kha", iso := "khk", value := .monoexponentialCase }
  , { walsCode := "khs", iso := "kha", value := .monoexponentialCase }
  , { walsCode := "kio", iso := "kio", value := .noCase }
  , { walsCode := "kis", iso := "kss", value := .noCase }
  , { walsCode := "kiw", iso := "kjd", value := .noCase }
  , { walsCode := "koa", iso := "cku", value := .monoexponentialCase }
  , { walsCode := "koi", iso := "kbk", value := .noCase }
  , { walsCode := "kor", iso := "kor", value := .monoexponentialCase }
  , { walsCode := "kch", iso := "khq", value := .noCase }
  , { walsCode := "kro", iso := "kgo", value := .noCase }
  , { walsCode := "knm", iso := "kun", value := .monoexponentialCase }
  , { walsCode := "kut", iso := "kut", value := .caseReferentiality }
  , { walsCode := "lah", iso := "lhu", value := .monoexponentialCase }
  , { walsCode := "lai", iso := "cnh", value := .monoexponentialCase }
  , { walsCode := "lkt", iso := "lkt", value := .noCase }
  , { walsCode := "lan", iso := "laj", value := .noCase }
  , { walsCode := "lav", iso := "lvk", value := .noCase }
  , { walsCode := "lez", iso := "lez", value := .monoexponentialCase }
  , { walsCode := "lug", iso := "lgg", value := .caseTam }
  , { walsCode := "luv", iso := "lue", value := .noCase }
  , { walsCode := "maa", iso := "mas", value := .monoexponentialCase }
  , { walsCode := "mal", iso := "plt", value := .monoexponentialCase }
  , { walsCode := "mnd", iso := "cmn", value := .monoexponentialCase }
  , { walsCode := "myi", iso := "mpc", value := .monoexponentialCase }
  , { walsCode := "mao", iso := "mri", value := .monoexponentialCase }
  , { walsCode := "map", iso := "arn", value := .noCase }
  , { walsCode := "mrg", iso := "mrt", value := .noCase }
  , { walsCode := "mar", iso := "mrc", value := .monoexponentialCase }
  , { walsCode := "mrt", iso := "vma", value := .monoexponentialCase }
  , { walsCode := "mau", iso := "mph", value := .noCase }
  , { walsCode := "may", iso := "ayz", value := .noCase }
  , { walsCode := "mei", iso := "mni", value := .monoexponentialCase }
  , { walsCode := "mss", iso := "skd", value := .monoexponentialCase }
  , { walsCode := "mxc", iso := "mig", value := .noCase }
  , { walsCode := "mun", iso := "unr", value := .monoexponentialCase }
  , { walsCode := "nah", iso := "nll", value := .monoexponentialCase }
  , { walsCode := "kho", iso := "naq", value := .monoexponentialCase }
  , { walsCode := "nmb", iso := "nab", value := .noCase }
  , { walsCode := "nan", iso := "niq", value := .monoexponentialCase }
  , { walsCode := "ntu", iso := "yrk", value := .caseNumber }
  , { walsCode := "ngi", iso := "wyb", value := .monoexponentialCase }
  , { walsCode := "niv", iso := "niv", value := .noCase }
  , { walsCode := "nbd", iso := "dgl", value := .monoexponentialCase }
  , { walsCode := "ond", iso := "one", value := .noCase }
  , { walsCode := "orh", iso := "hae", value := .monoexponentialCase }
  , { walsCode := "otm", iso := "ote", value := .noCase }
  , { walsCode := "pai", iso := "pwn", value := .caseReferentiality }
  , { walsCode := "prs", iso := "pes", value := .monoexponentialCase }
  , { walsCode := "prh", iso := "myp", value := .noCase }
  , { walsCode := "pur", iso := "tsz", value := .monoexponentialCase }
  , { walsCode := "qim", iso := "qvi", value := .monoexponentialCase }
  , { walsCode := "ram", iso := "rma", value := .monoexponentialCase }
  , { walsCode := "rap", iso := "rap", value := .monoexponentialCase }
  , { walsCode := "rus", iso := "rus", value := .caseNumber }
  , { walsCode := "san", iso := "sag", value := .noCase }
  , { walsCode := "snm", iso := "xsu", value := .monoexponentialCase }
  , { walsCode := "sla", iso := "den", value := .noCase }
  , { walsCode := "spa", iso := "spa", value := .monoexponentialCase }
  , { walsCode := "squ", iso := "squ", value := .monoexponentialCase }
  , { walsCode := "sup", iso := "spp", value := .noCase }
  , { walsCode := "swa", iso := "swh", value := .noCase }
  , { walsCode := "tag", iso := "tgl", value := .caseReferentiality }
  , { walsCode := "ter", iso := "ttr", value := .noCase }
  , { walsCode := "tha", iso := "tha", value := .noCase }
  , { walsCode := "tib", iso := "bod", value := .monoexponentialCase }
  , { walsCode := "tiw", iso := "tiw", value := .noCase }
  , { walsCode := "tli", iso := "tli", value := .monoexponentialCase }
  , { walsCode := "tot", iso := "tlc", value := .noCase }
  , { walsCode := "tru", iso := "tpy", value := .monoexponentialCase }
  , { walsCode := "tuk", iso := "", value := .caseReferentiality }
  , { walsCode := "tur", iso := "tur", value := .monoexponentialCase }
  , { walsCode := "vie", iso := "vie", value := .noCase }
  , { walsCode := "wra", iso := "wba", value := .monoexponentialCase }
  , { walsCode := "wrd", iso := "wrr", value := .monoexponentialCase }
  , { walsCode := "wrm", iso := "wsa", value := .noCase }
  , { walsCode := "war", iso := "pav", value := .noCase }
  , { walsCode := "wem", iso := "xww", value := .monoexponentialCase }
  , { walsCode := "wic", iso := "wic", value := .monoexponentialCase }
  , { walsCode := "wch", iso := "mzh", value := .noCase }
  , { walsCode := "yag", iso := "yad", value := .noCase }
  , { walsCode := "yaq", iso := "yaq", value := .caseNumber }
  , { walsCode := "yid", iso := "yii", value := .monoexponentialCase }
  , { walsCode := "yor", iso := "yor", value := .monoexponentialCase }
  , { walsCode := "yuc", iso := "yuc", value := .noCase }
  , { walsCode := "yur", iso := "yur", value := .noCase }
  , { walsCode := "zqc", iso := "zoc", value := .monoexponentialCase }
  , { walsCode := "zul", iso := "zul", value := .noCase }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F21A
