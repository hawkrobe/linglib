import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 67A: The Future Tense
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 67A`.

Chapter 67, 222 languages.
-/

namespace Core.WALS.F67A

/-- WALS 67A values. -/
inductive FutureTenseType where
  /-- Inflectional future exists (110 languages). -/
  | inflectionalFutureExists
  /-- No inflectional future (112 languages). -/
  | noInflectionalFuture
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 67A dataset (222 languages). -/
def allData : List (Datapoint FutureTenseType) :=
  [ { walsCode := "abi", iso := "axb", value := .noInflectionalFuture }
  , { walsCode := "abk", iso := "abk", value := .inflectionalFutureExists }
  , { walsCode := "aco", iso := "kjq", value := .noInflectionalFuture }
  , { walsCode := "afr", iso := "afr", value := .noInflectionalFuture }
  , { walsCode := "ain", iso := "ain", value := .noInflectionalFuture }
  , { walsCode := "akn", iso := "aka", value := .inflectionalFutureExists }
  , { walsCode := "ala", iso := "amp", value := .inflectionalFutureExists }
  , { walsCode := "alw", iso := "alh", value := .inflectionalFutureExists }
  , { walsCode := "aly", iso := "aly", value := .inflectionalFutureExists }
  , { walsCode := "ame", iso := "aey", value := .inflectionalFutureExists }
  , { walsCode := "amh", iso := "amh", value := .noInflectionalFuture }
  , { walsCode := "apu", iso := "apu", value := .inflectionalFutureExists }
  , { walsCode := "aeg", iso := "arz", value := .inflectionalFutureExists }
  , { walsCode := "atu", iso := "aeb", value := .noInflectionalFuture }
  , { walsCode := "ana", iso := "aro", value := .noInflectionalFuture }
  , { walsCode := "arp", iso := "ape", value := .inflectionalFutureExists }
  , { walsCode := "arm", iso := "hye", value := .noInflectionalFuture }
  , { walsCode := "asm", iso := "cns", value := .inflectionalFutureExists }
  , { walsCode := "atc", iso := "upv", value := .noInflectionalFuture }
  , { walsCode := "avo", iso := "avu", value := .noInflectionalFuture }
  , { walsCode := "awp", iso := "kwi", value := .inflectionalFutureExists }
  , { walsCode := "awn", iso := "awn", value := .inflectionalFutureExists }
  , { walsCode := "aze", iso := "", value := .inflectionalFutureExists }
  , { walsCode := "bag", iso := "bmi", value := .noInflectionalFuture }
  , { walsCode := "blc", iso := "bgn", value := .inflectionalFutureExists }
  , { walsCode := "bnj", iso := "bdy", value := .inflectionalFutureExists }
  , { walsCode := "brs", iso := "bsn", value := .noInflectionalFuture }
  , { walsCode := "bar", iso := "bfa", value := .noInflectionalFuture }
  , { walsCode := "bsq", iso := "eus", value := .inflectionalFutureExists }
  , { walsCode := "bej", iso := "bej", value := .noInflectionalFuture }
  , { walsCode := "ben", iso := "ben", value := .inflectionalFutureExists }
  , { walsCode := "bma", iso := "tzm", value := .noInflectionalFuture }
  , { walsCode := "bon", iso := "bpu", value := .inflectionalFutureExists }
  , { walsCode := "brh", iso := "brh", value := .noInflectionalFuture }
  , { walsCode := "bul", iso := "bul", value := .noInflectionalFuture }
  , { walsCode := "bui", iso := "bzq", value := .inflectionalFutureExists }
  , { walsCode := "but", iso := "bxm", value := .noInflectionalFuture }
  , { walsCode := "brm", iso := "mya", value := .noInflectionalFuture }
  , { walsCode := "bur", iso := "bsk", value := .inflectionalFutureExists }
  , { walsCode := "cnl", iso := "ram", value := .noInflectionalFuture }
  , { walsCode := "cnt", iso := "yue", value := .noInflectionalFuture }
  , { walsCode := "ceb", iso := "ceb", value := .noInflectionalFuture }
  , { walsCode := "cha", iso := "cha", value := .noInflectionalFuture }
  , { walsCode := "cpn", iso := "cdm", value := .inflectionalFutureExists }
  , { walsCode := "cyn", iso := "chy", value := .inflectionalFutureExists }
  , { walsCode := "cpl", iso := "cpa", value := .inflectionalFutureExists }
  , { walsCode := "chk", iso := "ckt", value := .inflectionalFutureExists }
  , { walsCode := "cuu", iso := "chk", value := .noInflectionalFuture }
  , { walsCode := "cbo", iso := "cao", value := .inflectionalFutureExists }
  , { walsCode := "coc", iso := "cod", value := .inflectionalFutureExists }
  , { walsCode := "cre", iso := "crk", value := .noInflectionalFuture }
  , { walsCode := "dag", iso := "dgz", value := .inflectionalFutureExists }
  , { walsCode := "dni", iso := "dni", value := .inflectionalFutureExists }
  , { walsCode := "did", iso := "did", value := .noInflectionalFuture }
  , { walsCode := "dio", iso := "dyo", value := .inflectionalFutureExists }
  , { walsCode := "egn", iso := "enn", value := .inflectionalFutureExists }
  , { walsCode := "eng", iso := "eng", value := .noInflectionalFuture }
  , { walsCode := "eve", iso := "evn", value := .inflectionalFutureExists }
  , { walsCode := "ewe", iso := "ewe", value := .inflectionalFutureExists }
  , { walsCode := "fij", iso := "fij", value := .noInflectionalFuture }
  , { walsCode := "fin", iso := "fin", value := .noInflectionalFuture }
  , { walsCode := "fre", iso := "fra", value := .inflectionalFutureExists }
  , { walsCode := "grf", iso := "cab", value := .inflectionalFutureExists }
  , { walsCode := "geo", iso := "kat", value := .inflectionalFutureExists }
  , { walsCode := "ger", iso := "deu", value := .noInflectionalFuture }
  , { walsCode := "goo", iso := "gni", value := .inflectionalFutureExists }
  , { walsCode := "grb", iso := "grj", value := .inflectionalFutureExists }
  , { walsCode := "grk", iso := "ell", value := .noInflectionalFuture }
  , { walsCode := "grw", iso := "kal", value := .inflectionalFutureExists }
  , { walsCode := "gua", iso := "gug", value := .inflectionalFutureExists }
  , { walsCode := "gug", iso := "ktd", value := .inflectionalFutureExists }
  , { walsCode := "hal", iso := "hla", value := .inflectionalFutureExists }
  , { walsCode := "hau", iso := "hau", value := .noInflectionalFuture }
  , { walsCode := "haw", iso := "haw", value := .noInflectionalFuture }
  , { walsCode := "hwc", iso := "hwc", value := .noInflectionalFuture }
  , { walsCode := "heb", iso := "heb", value := .inflectionalFutureExists }
  , { walsCode := "hin", iso := "hin", value := .inflectionalFutureExists }
  , { walsCode := "hix", iso := "hix", value := .noInflectionalFuture }
  , { walsCode := "hmo", iso := "hnj", value := .noInflectionalFuture }
  , { walsCode := "hun", iso := "hun", value := .noInflectionalFuture }
  , { walsCode := "ice", iso := "isl", value := .noInflectionalFuture }
  , { walsCode := "imo", iso := "imn", value := .inflectionalFutureExists }
  , { walsCode := "ind", iso := "ind", value := .noInflectionalFuture }
  , { walsCode := "ins", iso := "ike", value := .inflectionalFutureExists }
  , { walsCode := "ise", iso := "its", value := .noInflectionalFuture }
  , { walsCode := "jak", iso := "jac", value := .noInflectionalFuture }
  , { walsCode := "jpn", iso := "jpn", value := .noInflectionalFuture }
  , { walsCode := "jav", iso := "jav", value := .noInflectionalFuture }
  , { walsCode := "jiv", iso := "jiv", value := .inflectionalFutureExists }
  , { walsCode := "juh", iso := "ktz", value := .noInflectionalFuture }
  , { walsCode := "knk", iso := "kna", value := .inflectionalFutureExists }
  , { walsCode := "knd", iso := "kan", value := .inflectionalFutureExists }
  , { walsCode := "knr", iso := "knc", value := .inflectionalFutureExists }
  , { walsCode := "krk", iso := "kyh", value := .inflectionalFutureExists }
  , { walsCode := "kay", iso := "gyd", value := .inflectionalFutureExists }
  , { walsCode := "ket", iso := "ket", value := .noInflectionalFuture }
  , { walsCode := "kew", iso := "kew", value := .inflectionalFutureExists }
  , { walsCode := "kha", iso := "khk", value := .noInflectionalFuture }
  , { walsCode := "khm", iso := "khm", value := .noInflectionalFuture }
  , { walsCode := "kmu", iso := "kjg", value := .noInflectionalFuture }
  , { walsCode := "kik", iso := "kik", value := .noInflectionalFuture }
  , { walsCode := "kio", iso := "kio", value := .inflectionalFutureExists }
  , { walsCode := "koa", iso := "cku", value := .inflectionalFutureExists }
  , { walsCode := "kor", iso := "kor", value := .noInflectionalFuture }
  , { walsCode := "kse", iso := "ses", value := .noInflectionalFuture }
  , { walsCode := "kfc", iso := "rop", value := .noInflectionalFuture }
  , { walsCode := "kro", iso := "kgo", value := .noInflectionalFuture }
  , { walsCode := "kui", iso := "kxu", value := .inflectionalFutureExists }
  , { walsCode := "kya", iso := "gvn", value := .noInflectionalFuture }
  , { walsCode := "kji", iso := "kmr", value := .inflectionalFutureExists }
  , { walsCode := "kut", iso := "kut", value := .inflectionalFutureExists }
  , { walsCode := "lah", iso := "lhu", value := .noInflectionalFuture }
  , { walsCode := "lai", iso := "cnh", value := .noInflectionalFuture }
  , { walsCode := "lkt", iso := "lkt", value := .noInflectionalFuture }
  , { walsCode := "lan", iso := "laj", value := .noInflectionalFuture }
  , { walsCode := "lao", iso := "lao", value := .noInflectionalFuture }
  , { walsCode := "lat", iso := "lav", value := .inflectionalFutureExists }
  , { walsCode := "lav", iso := "lvk", value := .inflectionalFutureExists }
  , { walsCode := "lez", iso := "lez", value := .inflectionalFutureExists }
  , { walsCode := "lda", iso := "lug", value := .inflectionalFutureExists }
  , { walsCode := "luv", iso := "lue", value := .inflectionalFutureExists }
  , { walsCode := "mne", iso := "nmu", value := .inflectionalFutureExists }
  , { walsCode := "mai", iso := "mai", value := .inflectionalFutureExists }
  , { walsCode := "mak", iso := "myh", value := .noInflectionalFuture }
  , { walsCode := "mal", iso := "plt", value := .noInflectionalFuture }
  , { walsCode := "mlt", iso := "mlt", value := .noInflectionalFuture }
  , { walsCode := "mnd", iso := "cmn", value := .noInflectionalFuture }
  , { walsCode := "myi", iso := "mpc", value := .noInflectionalFuture }
  , { walsCode := "man", iso := "mev", value := .noInflectionalFuture }
  , { walsCode := "mao", iso := "mri", value := .noInflectionalFuture }
  , { walsCode := "map", iso := "arn", value := .inflectionalFutureExists }
  , { walsCode := "mrg", iso := "mrt", value := .inflectionalFutureExists }
  , { walsCode := "mar", iso := "mrc", value := .inflectionalFutureExists }
  , { walsCode := "mrt", iso := "vma", value := .inflectionalFutureExists }
  , { walsCode := "mau", iso := "mph", value := .inflectionalFutureExists }
  , { walsCode := "may", iso := "ayz", value := .noInflectionalFuture }
  , { walsCode := "mei", iso := "mni", value := .noInflectionalFuture }
  , { walsCode := "mxc", iso := "mig", value := .inflectionalFutureExists }
  , { walsCode := "mtg", iso := "moe", value := .inflectionalFutureExists }
  , { walsCode := "mtu", iso := "meu", value := .noInflectionalFuture }
  , { walsCode := "mwe", iso := "mwe", value := .inflectionalFutureExists }
  , { walsCode := "nak", iso := "nak", value := .noInflectionalFuture }
  , { walsCode := "kho", iso := "naq", value := .noInflectionalFuture }
  , { walsCode := "ntu", iso := "yrk", value := .inflectionalFutureExists }
  , { walsCode := "ngm", iso := "sba", value := .inflectionalFutureExists }
  , { walsCode := "ngi", iso := "wyb", value := .inflectionalFutureExists }
  , { walsCode := "nbr", iso := "gym", value := .noInflectionalFuture }
  , { walsCode := "nca", iso := "caq", value := .noInflectionalFuture }
  , { walsCode := "nim", iso := "nir", value := .inflectionalFutureExists }
  , { walsCode := "niv", iso := "niv", value := .inflectionalFutureExists }
  , { walsCode := "ood", iso := "ood", value := .noInflectionalFuture }
  , { walsCode := "ond", iso := "one", value := .inflectionalFutureExists }
  , { walsCode := "ono", iso := "ons", value := .inflectionalFutureExists }
  , { walsCode := "orh", iso := "hae", value := .noInflectionalFuture }
  , { walsCode := "pai", iso := "pwn", value := .noInflectionalFuture }
  , { walsCode := "plg", iso := "pll", value := .noInflectionalFuture }
  , { walsCode := "pnn", iso := "pag", value := .inflectionalFutureExists }
  , { walsCode := "pan", iso := "pan", value := .inflectionalFutureExists }
  , { walsCode := "prs", iso := "pes", value := .noInflectionalFuture }
  , { walsCode := "prh", iso := "myp", value := .noInflectionalFuture }
  , { walsCode := "por", iso := "por", value := .noInflectionalFuture }
  , { walsCode := "bng", iso := "byx", value := .inflectionalFutureExists }
  , { walsCode := "qco", iso := "quh", value := .noInflectionalFuture }
  , { walsCode := "qim", iso := "qvi", value := .inflectionalFutureExists }
  , { walsCode := "ram", iso := "rma", value := .inflectionalFutureExists }
  , { walsCode := "rap", iso := "rap", value := .noInflectionalFuture }
  , { walsCode := "raw", iso := "raw", value := .noInflectionalFuture }
  , { walsCode := "ren", iso := "rel", value := .noInflectionalFuture }
  , { walsCode := "rom", iso := "ron", value := .noInflectionalFuture }
  , { walsCode := "ruk", iso := "dru", value := .inflectionalFutureExists }
  , { walsCode := "rus", iso := "rus", value := .noInflectionalFuture }
  , { walsCode := "san", iso := "sag", value := .noInflectionalFuture }
  , { walsCode := "snm", iso := "xsu", value := .noInflectionalFuture }
  , { walsCode := "sml", iso := "sza", value := .noInflectionalFuture }
  , { walsCode := "snc", iso := "see", value := .inflectionalFutureExists }
  , { walsCode := "ses", iso := "sot", value := .noInflectionalFuture }
  , { walsCode := "shu", iso := "shs", value := .noInflectionalFuture }
  , { walsCode := "sla", iso := "den", value := .inflectionalFutureExists }
  , { walsCode := "som", iso := "som", value := .inflectionalFutureExists }
  , { walsCode := "spa", iso := "spa", value := .inflectionalFutureExists }
  , { walsCode := "sue", iso := "sue", value := .inflectionalFutureExists }
  , { walsCode := "sun", iso := "sun", value := .noInflectionalFuture }
  , { walsCode := "sup", iso := "spp", value := .noInflectionalFuture }
  , { walsCode := "swa", iso := "swh", value := .inflectionalFutureExists }
  , { walsCode := "swe", iso := "swe", value := .noInflectionalFuture }
  , { walsCode := "tag", iso := "tgl", value := .inflectionalFutureExists }
  , { walsCode := "tah", iso := "tah", value := .noInflectionalFuture }
  , { walsCode := "tml", iso := "tam", value := .inflectionalFutureExists }
  , { walsCode := "tga", iso := "hrc", value := .noInflectionalFuture }
  , { walsCode := "tem", iso := "kdh", value := .inflectionalFutureExists }
  , { walsCode := "tne", iso := "tem", value := .inflectionalFutureExists }
  , { walsCode := "tny", iso := "kza", value := .noInflectionalFuture }
  , { walsCode := "tha", iso := "tha", value := .noInflectionalFuture }
  , { walsCode := "tig", iso := "tir", value := .inflectionalFutureExists }
  , { walsCode := "tgr", iso := "tig", value := .noInflectionalFuture }
  , { walsCode := "tiw", iso := "tiw", value := .inflectionalFutureExists }
  , { walsCode := "toj", iso := "toj", value := .noInflectionalFuture }
  , { walsCode := "tpi", iso := "tpi", value := .noInflectionalFuture }
  , { walsCode := "tug", iso := "thv", value := .inflectionalFutureExists }
  , { walsCode := "tuc", iso := "tuo", value := .inflectionalFutureExists }
  , { walsCode := "tuk", iso := "", value := .inflectionalFutureExists }
  , { walsCode := "tur", iso := "tur", value := .inflectionalFutureExists }
  , { walsCode := "udm", iso := "udm", value := .inflectionalFutureExists }
  , { walsCode := "uyg", iso := "uig", value := .noInflectionalFuture }
  , { walsCode := "vie", iso := "vie", value := .noInflectionalFuture }
  , { walsCode := "wra", iso := "wba", value := .noInflectionalFuture }
  , { walsCode := "war", iso := "pav", value := .noInflectionalFuture }
  , { walsCode := "wic", iso := "wic", value := .inflectionalFutureExists }
  , { walsCode := "wch", iso := "mzh", value := .inflectionalFutureExists }
  , { walsCode := "wly", iso := "wal", value := .inflectionalFutureExists }
  , { walsCode := "wlf", iso := "wol", value := .noInflectionalFuture }
  , { walsCode := "wor", iso := "wro", value := .noInflectionalFuture }
  , { walsCode := "ygr", iso := "ygr", value := .inflectionalFutureExists }
  , { walsCode := "yag", iso := "yad", value := .noInflectionalFuture }
  , { walsCode := "yaq", iso := "yaq", value := .inflectionalFutureExists }
  , { walsCode := "yes", iso := "yss", value := .inflectionalFutureExists }
  , { walsCode := "yor", iso := "yor", value := .noInflectionalFuture }
  , { walsCode := "yct", iso := "yua", value := .noInflectionalFuture }
  , { walsCode := "yko", iso := "yux", value := .inflectionalFutureExists }
  , { walsCode := "zqc", iso := "zoc", value := .noInflectionalFuture }
  , { walsCode := "zul", iso := "zul", value := .inflectionalFutureExists }
  , { walsCode := "zun", iso := "zun", value := .noInflectionalFuture }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F67A
