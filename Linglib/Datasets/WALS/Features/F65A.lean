import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 65A: Perfective/Imperfective Aspect
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 65A`.

Chapter 65, 222 languages.
-/

namespace Datasets.WALS.F65A

/-- WALS 65A values. -/
inductive PerfectiveImperfective where
  /-- Grammatical marking (101 languages). -/
  | grammaticalMarking
  /-- No grammatical marking (121 languages). -/
  | noGrammaticalMarking
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 65A dataset (222 languages). -/
def allData : List (Datapoint PerfectiveImperfective) :=
  [ { walsCode := "abi", iso := "axb", value := .noGrammaticalMarking }
  , { walsCode := "abk", iso := "abk", value := .grammaticalMarking }
  , { walsCode := "aco", iso := "kjq", value := .noGrammaticalMarking }
  , { walsCode := "afr", iso := "afr", value := .noGrammaticalMarking }
  , { walsCode := "ain", iso := "ain", value := .noGrammaticalMarking }
  , { walsCode := "akn", iso := "aka", value := .grammaticalMarking }
  , { walsCode := "ala", iso := "amp", value := .grammaticalMarking }
  , { walsCode := "alw", iso := "alh", value := .grammaticalMarking }
  , { walsCode := "aly", iso := "aly", value := .grammaticalMarking }
  , { walsCode := "ame", iso := "aey", value := .noGrammaticalMarking }
  , { walsCode := "amh", iso := "amh", value := .noGrammaticalMarking }
  , { walsCode := "apu", iso := "apu", value := .noGrammaticalMarking }
  , { walsCode := "aeg", iso := "arz", value := .grammaticalMarking }
  , { walsCode := "atu", iso := "aeb", value := .grammaticalMarking }
  , { walsCode := "ana", iso := "aro", value := .noGrammaticalMarking }
  , { walsCode := "arp", iso := "ape", value := .noGrammaticalMarking }
  , { walsCode := "arm", iso := "hye", value := .grammaticalMarking }
  , { walsCode := "asm", iso := "cns", value := .noGrammaticalMarking }
  , { walsCode := "atc", iso := "upv", value := .noGrammaticalMarking }
  , { walsCode := "avo", iso := "avu", value := .grammaticalMarking }
  , { walsCode := "awp", iso := "kwi", value := .grammaticalMarking }
  , { walsCode := "awn", iso := "awn", value := .noGrammaticalMarking }
  , { walsCode := "aze", iso := "", value := .grammaticalMarking }
  , { walsCode := "bag", iso := "bmi", value := .grammaticalMarking }
  , { walsCode := "blc", iso := "bgn", value := .noGrammaticalMarking }
  , { walsCode := "bnj", iso := "bdy", value := .grammaticalMarking }
  , { walsCode := "brs", iso := "bsn", value := .noGrammaticalMarking }
  , { walsCode := "bar", iso := "bfa", value := .noGrammaticalMarking }
  , { walsCode := "bsq", iso := "eus", value := .grammaticalMarking }
  , { walsCode := "bej", iso := "bej", value := .grammaticalMarking }
  , { walsCode := "ben", iso := "ben", value := .noGrammaticalMarking }
  , { walsCode := "bma", iso := "tzm", value := .grammaticalMarking }
  , { walsCode := "bon", iso := "bpu", value := .noGrammaticalMarking }
  , { walsCode := "brh", iso := "brh", value := .grammaticalMarking }
  , { walsCode := "bul", iso := "bul", value := .grammaticalMarking }
  , { walsCode := "bui", iso := "bzq", value := .noGrammaticalMarking }
  , { walsCode := "but", iso := "bxm", value := .grammaticalMarking }
  , { walsCode := "brm", iso := "mya", value := .noGrammaticalMarking }
  , { walsCode := "bur", iso := "bsk", value := .grammaticalMarking }
  , { walsCode := "cnl", iso := "ram", value := .noGrammaticalMarking }
  , { walsCode := "cnt", iso := "yue", value := .grammaticalMarking }
  , { walsCode := "ceb", iso := "ceb", value := .grammaticalMarking }
  , { walsCode := "cha", iso := "cha", value := .grammaticalMarking }
  , { walsCode := "cpn", iso := "cdm", value := .grammaticalMarking }
  , { walsCode := "cyn", iso := "chy", value := .noGrammaticalMarking }
  , { walsCode := "cpl", iso := "cpa", value := .noGrammaticalMarking }
  , { walsCode := "chk", iso := "ckt", value := .grammaticalMarking }
  , { walsCode := "cuu", iso := "chk", value := .grammaticalMarking }
  , { walsCode := "cbo", iso := "cao", value := .grammaticalMarking }
  , { walsCode := "coc", iso := "cod", value := .noGrammaticalMarking }
  , { walsCode := "cre", iso := "crk", value := .noGrammaticalMarking }
  , { walsCode := "dag", iso := "dgz", value := .noGrammaticalMarking }
  , { walsCode := "dni", iso := "dni", value := .grammaticalMarking }
  , { walsCode := "did", iso := "did", value := .noGrammaticalMarking }
  , { walsCode := "dio", iso := "dyo", value := .noGrammaticalMarking }
  , { walsCode := "egn", iso := "enn", value := .grammaticalMarking }
  , { walsCode := "eng", iso := "eng", value := .noGrammaticalMarking }
  , { walsCode := "eve", iso := "evn", value := .grammaticalMarking }
  , { walsCode := "ewe", iso := "ewe", value := .noGrammaticalMarking }
  , { walsCode := "fij", iso := "fij", value := .noGrammaticalMarking }
  , { walsCode := "fin", iso := "fin", value := .noGrammaticalMarking }
  , { walsCode := "fre", iso := "fra", value := .grammaticalMarking }
  , { walsCode := "grf", iso := "cab", value := .grammaticalMarking }
  , { walsCode := "geo", iso := "kat", value := .grammaticalMarking }
  , { walsCode := "ger", iso := "deu", value := .noGrammaticalMarking }
  , { walsCode := "goo", iso := "gni", value := .noGrammaticalMarking }
  , { walsCode := "grb", iso := "grj", value := .grammaticalMarking }
  , { walsCode := "grk", iso := "ell", value := .grammaticalMarking }
  , { walsCode := "grw", iso := "kal", value := .noGrammaticalMarking }
  , { walsCode := "gua", iso := "gug", value := .noGrammaticalMarking }
  , { walsCode := "gug", iso := "ktd", value := .noGrammaticalMarking }
  , { walsCode := "hal", iso := "hla", value := .noGrammaticalMarking }
  , { walsCode := "hau", iso := "hau", value := .noGrammaticalMarking }
  , { walsCode := "haw", iso := "haw", value := .grammaticalMarking }
  , { walsCode := "hwc", iso := "hwc", value := .grammaticalMarking }
  , { walsCode := "heb", iso := "heb", value := .noGrammaticalMarking }
  , { walsCode := "hin", iso := "hin", value := .grammaticalMarking }
  , { walsCode := "hix", iso := "hix", value := .grammaticalMarking }
  , { walsCode := "hmo", iso := "hnj", value := .noGrammaticalMarking }
  , { walsCode := "hun", iso := "hun", value := .noGrammaticalMarking }
  , { walsCode := "ice", iso := "isl", value := .noGrammaticalMarking }
  , { walsCode := "imo", iso := "imn", value := .grammaticalMarking }
  , { walsCode := "ind", iso := "ind", value := .noGrammaticalMarking }
  , { walsCode := "ins", iso := "ike", value := .noGrammaticalMarking }
  , { walsCode := "ise", iso := "its", value := .noGrammaticalMarking }
  , { walsCode := "jak", iso := "jac", value := .grammaticalMarking }
  , { walsCode := "jpn", iso := "jpn", value := .noGrammaticalMarking }
  , { walsCode := "jav", iso := "jav", value := .noGrammaticalMarking }
  , { walsCode := "jiv", iso := "jiv", value := .noGrammaticalMarking }
  , { walsCode := "juh", iso := "ktz", value := .grammaticalMarking }
  , { walsCode := "knk", iso := "kna", value := .grammaticalMarking }
  , { walsCode := "knd", iso := "kan", value := .noGrammaticalMarking }
  , { walsCode := "knr", iso := "knc", value := .grammaticalMarking }
  , { walsCode := "krk", iso := "kyh", value := .noGrammaticalMarking }
  , { walsCode := "kay", iso := "gyd", value := .noGrammaticalMarking }
  , { walsCode := "ket", iso := "ket", value := .grammaticalMarking }
  , { walsCode := "kew", iso := "kew", value := .noGrammaticalMarking }
  , { walsCode := "kha", iso := "khk", value := .noGrammaticalMarking }
  , { walsCode := "khm", iso := "khm", value := .noGrammaticalMarking }
  , { walsCode := "kmu", iso := "kjg", value := .noGrammaticalMarking }
  , { walsCode := "kik", iso := "kik", value := .grammaticalMarking }
  , { walsCode := "kio", iso := "kio", value := .grammaticalMarking }
  , { walsCode := "koa", iso := "cku", value := .noGrammaticalMarking }
  , { walsCode := "kor", iso := "kor", value := .grammaticalMarking }
  , { walsCode := "kse", iso := "ses", value := .grammaticalMarking }
  , { walsCode := "kfc", iso := "rop", value := .noGrammaticalMarking }
  , { walsCode := "kro", iso := "kgo", value := .grammaticalMarking }
  , { walsCode := "kui", iso := "kxu", value := .noGrammaticalMarking }
  , { walsCode := "kya", iso := "gvn", value := .noGrammaticalMarking }
  , { walsCode := "kji", iso := "kmr", value := .grammaticalMarking }
  , { walsCode := "kut", iso := "kut", value := .noGrammaticalMarking }
  , { walsCode := "lah", iso := "lhu", value := .noGrammaticalMarking }
  , { walsCode := "lai", iso := "cnh", value := .noGrammaticalMarking }
  , { walsCode := "lkt", iso := "lkt", value := .noGrammaticalMarking }
  , { walsCode := "lan", iso := "laj", value := .grammaticalMarking }
  , { walsCode := "lao", iso := "lao", value := .noGrammaticalMarking }
  , { walsCode := "lat", iso := "lav", value := .noGrammaticalMarking }
  , { walsCode := "lav", iso := "lvk", value := .noGrammaticalMarking }
  , { walsCode := "lez", iso := "lez", value := .grammaticalMarking }
  , { walsCode := "lda", iso := "lug", value := .noGrammaticalMarking }
  , { walsCode := "luv", iso := "lue", value := .noGrammaticalMarking }
  , { walsCode := "mne", iso := "nmu", value := .noGrammaticalMarking }
  , { walsCode := "mai", iso := "mai", value := .noGrammaticalMarking }
  , { walsCode := "mak", iso := "myh", value := .grammaticalMarking }
  , { walsCode := "mal", iso := "plt", value := .grammaticalMarking }
  , { walsCode := "mlt", iso := "mlt", value := .grammaticalMarking }
  , { walsCode := "mnd", iso := "cmn", value := .grammaticalMarking }
  , { walsCode := "myi", iso := "mpc", value := .noGrammaticalMarking }
  , { walsCode := "man", iso := "mev", value := .noGrammaticalMarking }
  , { walsCode := "mao", iso := "mri", value := .noGrammaticalMarking }
  , { walsCode := "map", iso := "arn", value := .noGrammaticalMarking }
  , { walsCode := "mrg", iso := "mrt", value := .grammaticalMarking }
  , { walsCode := "mar", iso := "mrc", value := .noGrammaticalMarking }
  , { walsCode := "mrt", iso := "vma", value := .noGrammaticalMarking }
  , { walsCode := "mau", iso := "mph", value := .grammaticalMarking }
  , { walsCode := "may", iso := "ayz", value := .noGrammaticalMarking }
  , { walsCode := "mei", iso := "mni", value := .noGrammaticalMarking }
  , { walsCode := "mxc", iso := "mig", value := .grammaticalMarking }
  , { walsCode := "mtg", iso := "moe", value := .noGrammaticalMarking }
  , { walsCode := "mtu", iso := "meu", value := .noGrammaticalMarking }
  , { walsCode := "mwe", iso := "mwe", value := .grammaticalMarking }
  , { walsCode := "nak", iso := "nak", value := .grammaticalMarking }
  , { walsCode := "kho", iso := "naq", value := .grammaticalMarking }
  , { walsCode := "ntu", iso := "yrk", value := .noGrammaticalMarking }
  , { walsCode := "ngm", iso := "sba", value := .grammaticalMarking }
  , { walsCode := "ngi", iso := "wyb", value := .noGrammaticalMarking }
  , { walsCode := "nbr", iso := "gym", value := .grammaticalMarking }
  , { walsCode := "nca", iso := "caq", value := .noGrammaticalMarking }
  , { walsCode := "nim", iso := "nir", value := .noGrammaticalMarking }
  , { walsCode := "niv", iso := "niv", value := .noGrammaticalMarking }
  , { walsCode := "ood", iso := "ood", value := .grammaticalMarking }
  , { walsCode := "ond", iso := "one", value := .grammaticalMarking }
  , { walsCode := "ono", iso := "ons", value := .noGrammaticalMarking }
  , { walsCode := "orh", iso := "hae", value := .grammaticalMarking }
  , { walsCode := "pai", iso := "pwn", value := .noGrammaticalMarking }
  , { walsCode := "plg", iso := "pll", value := .noGrammaticalMarking }
  , { walsCode := "pnn", iso := "pag", value := .grammaticalMarking }
  , { walsCode := "pan", iso := "pan", value := .grammaticalMarking }
  , { walsCode := "prs", iso := "pes", value := .grammaticalMarking }
  , { walsCode := "prh", iso := "myp", value := .grammaticalMarking }
  , { walsCode := "por", iso := "por", value := .grammaticalMarking }
  , { walsCode := "bng", iso := "byx", value := .grammaticalMarking }
  , { walsCode := "qco", iso := "quh", value := .noGrammaticalMarking }
  , { walsCode := "qim", iso := "qvi", value := .noGrammaticalMarking }
  , { walsCode := "ram", iso := "rma", value := .noGrammaticalMarking }
  , { walsCode := "rap", iso := "rap", value := .noGrammaticalMarking }
  , { walsCode := "raw", iso := "raw", value := .noGrammaticalMarking }
  , { walsCode := "ren", iso := "rel", value := .grammaticalMarking }
  , { walsCode := "rom", iso := "ron", value := .grammaticalMarking }
  , { walsCode := "ruk", iso := "dru", value := .grammaticalMarking }
  , { walsCode := "rus", iso := "rus", value := .grammaticalMarking }
  , { walsCode := "san", iso := "sag", value := .noGrammaticalMarking }
  , { walsCode := "snm", iso := "xsu", value := .noGrammaticalMarking }
  , { walsCode := "sml", iso := "sza", value := .noGrammaticalMarking }
  , { walsCode := "snc", iso := "see", value := .grammaticalMarking }
  , { walsCode := "ses", iso := "sot", value := .grammaticalMarking }
  , { walsCode := "shu", iso := "shs", value := .grammaticalMarking }
  , { walsCode := "sla", iso := "den", value := .grammaticalMarking }
  , { walsCode := "som", iso := "som", value := .noGrammaticalMarking }
  , { walsCode := "spa", iso := "spa", value := .grammaticalMarking }
  , { walsCode := "sue", iso := "sue", value := .noGrammaticalMarking }
  , { walsCode := "sun", iso := "sun", value := .noGrammaticalMarking }
  , { walsCode := "sup", iso := "spp", value := .grammaticalMarking }
  , { walsCode := "swa", iso := "swh", value := .noGrammaticalMarking }
  , { walsCode := "swe", iso := "swe", value := .noGrammaticalMarking }
  , { walsCode := "tag", iso := "tgl", value := .grammaticalMarking }
  , { walsCode := "tah", iso := "tah", value := .grammaticalMarking }
  , { walsCode := "tml", iso := "tam", value := .noGrammaticalMarking }
  , { walsCode := "tga", iso := "hrc", value := .noGrammaticalMarking }
  , { walsCode := "tem", iso := "kdh", value := .grammaticalMarking }
  , { walsCode := "tne", iso := "tem", value := .noGrammaticalMarking }
  , { walsCode := "tny", iso := "kza", value := .grammaticalMarking }
  , { walsCode := "tha", iso := "tha", value := .noGrammaticalMarking }
  , { walsCode := "tig", iso := "tir", value := .noGrammaticalMarking }
  , { walsCode := "tgr", iso := "tig", value := .noGrammaticalMarking }
  , { walsCode := "tiw", iso := "tiw", value := .noGrammaticalMarking }
  , { walsCode := "toj", iso := "toj", value := .grammaticalMarking }
  , { walsCode := "tpi", iso := "tpi", value := .noGrammaticalMarking }
  , { walsCode := "tug", iso := "thv", value := .grammaticalMarking }
  , { walsCode := "tuc", iso := "tuo", value := .noGrammaticalMarking }
  , { walsCode := "tuk", iso := "", value := .noGrammaticalMarking }
  , { walsCode := "tur", iso := "tur", value := .grammaticalMarking }
  , { walsCode := "udm", iso := "udm", value := .noGrammaticalMarking }
  , { walsCode := "uyg", iso := "uig", value := .grammaticalMarking }
  , { walsCode := "vie", iso := "vie", value := .noGrammaticalMarking }
  , { walsCode := "wra", iso := "wba", value := .noGrammaticalMarking }
  , { walsCode := "war", iso := "pav", value := .noGrammaticalMarking }
  , { walsCode := "wic", iso := "wic", value := .grammaticalMarking }
  , { walsCode := "wch", iso := "mzh", value := .noGrammaticalMarking }
  , { walsCode := "wly", iso := "wal", value := .grammaticalMarking }
  , { walsCode := "wlf", iso := "wol", value := .noGrammaticalMarking }
  , { walsCode := "wor", iso := "wro", value := .grammaticalMarking }
  , { walsCode := "ygr", iso := "ygr", value := .grammaticalMarking }
  , { walsCode := "yag", iso := "yad", value := .grammaticalMarking }
  , { walsCode := "yaq", iso := "yaq", value := .grammaticalMarking }
  , { walsCode := "yes", iso := "yss", value := .noGrammaticalMarking }
  , { walsCode := "yor", iso := "yor", value := .noGrammaticalMarking }
  , { walsCode := "yct", iso := "yua", value := .grammaticalMarking }
  , { walsCode := "yko", iso := "yux", value := .noGrammaticalMarking }
  , { walsCode := "zqc", iso := "zoc", value := .grammaticalMarking }
  , { walsCode := "zul", iso := "zul", value := .grammaticalMarking }
  , { walsCode := "zun", iso := "zun", value := .noGrammaticalMarking }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F65A
