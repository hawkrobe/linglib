import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 68A: The Perfect
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 68A`.

Chapter 68, 222 languages.
-/

namespace Datasets.WALS.F68A

/-- WALS 68A values. -/
inductive PerfectType where
  /-- From possessive (7 languages). -/
  | fromPossessive
  /-- From 'finish', 'already' (21 languages). -/
  | fromFinishAlready
  /-- Other perfect (80 languages). -/
  | otherPerfect
  /-- No perfect (114 languages). -/
  | noPerfect
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 68A dataset (222 languages). -/
def allData : List (Datapoint PerfectType) :=
  [ { walsCode := "abi", iso := "axb", value := .noPerfect }
  , { walsCode := "abk", iso := "abk", value := .otherPerfect }
  , { walsCode := "aco", iso := "kjq", value := .noPerfect }
  , { walsCode := "afr", iso := "afr", value := .fromFinishAlready }
  , { walsCode := "ain", iso := "ain", value := .noPerfect }
  , { walsCode := "akn", iso := "aka", value := .otherPerfect }
  , { walsCode := "ala", iso := "amp", value := .noPerfect }
  , { walsCode := "alw", iso := "alh", value := .noPerfect }
  , { walsCode := "aly", iso := "aly", value := .otherPerfect }
  , { walsCode := "ame", iso := "aey", value := .fromFinishAlready }
  , { walsCode := "amh", iso := "amh", value := .otherPerfect }
  , { walsCode := "apu", iso := "apu", value := .noPerfect }
  , { walsCode := "aeg", iso := "arz", value := .noPerfect }
  , { walsCode := "atu", iso := "aeb", value := .noPerfect }
  , { walsCode := "ana", iso := "aro", value := .noPerfect }
  , { walsCode := "arp", iso := "ape", value := .noPerfect }
  , { walsCode := "arm", iso := "hye", value := .otherPerfect }
  , { walsCode := "asm", iso := "cns", value := .otherPerfect }
  , { walsCode := "atc", iso := "upv", value := .noPerfect }
  , { walsCode := "avo", iso := "avu", value := .noPerfect }
  , { walsCode := "awp", iso := "kwi", value := .noPerfect }
  , { walsCode := "awn", iso := "awn", value := .otherPerfect }
  , { walsCode := "aze", iso := "", value := .otherPerfect }
  , { walsCode := "bag", iso := "bmi", value := .noPerfect }
  , { walsCode := "blc", iso := "bgn", value := .otherPerfect }
  , { walsCode := "bnj", iso := "bdy", value := .noPerfect }
  , { walsCode := "brs", iso := "bsn", value := .noPerfect }
  , { walsCode := "bar", iso := "bfa", value := .otherPerfect }
  , { walsCode := "bsq", iso := "eus", value := .otherPerfect }
  , { walsCode := "bej", iso := "bej", value := .otherPerfect }
  , { walsCode := "ben", iso := "ben", value := .otherPerfect }
  , { walsCode := "bma", iso := "tzm", value := .noPerfect }
  , { walsCode := "bon", iso := "bpu", value := .fromFinishAlready }
  , { walsCode := "brh", iso := "brh", value := .otherPerfect }
  , { walsCode := "bul", iso := "bul", value := .otherPerfect }
  , { walsCode := "bui", iso := "bzq", value := .fromFinishAlready }
  , { walsCode := "but", iso := "bxm", value := .otherPerfect }
  , { walsCode := "brm", iso := "mya", value := .fromFinishAlready }
  , { walsCode := "bur", iso := "bsk", value := .otherPerfect }
  , { walsCode := "cnl", iso := "ram", value := .noPerfect }
  , { walsCode := "cnt", iso := "yue", value := .otherPerfect }
  , { walsCode := "ceb", iso := "ceb", value := .noPerfect }
  , { walsCode := "cha", iso := "cha", value := .noPerfect }
  , { walsCode := "cpn", iso := "cdm", value := .otherPerfect }
  , { walsCode := "cyn", iso := "chy", value := .noPerfect }
  , { walsCode := "cpl", iso := "cpa", value := .otherPerfect }
  , { walsCode := "chk", iso := "ckt", value := .noPerfect }
  , { walsCode := "cuu", iso := "chk", value := .noPerfect }
  , { walsCode := "cbo", iso := "cao", value := .noPerfect }
  , { walsCode := "coc", iso := "cod", value := .otherPerfect }
  , { walsCode := "cre", iso := "crk", value := .noPerfect }
  , { walsCode := "dag", iso := "dgz", value := .noPerfect }
  , { walsCode := "dni", iso := "dni", value := .noPerfect }
  , { walsCode := "did", iso := "did", value := .noPerfect }
  , { walsCode := "dio", iso := "dyo", value := .noPerfect }
  , { walsCode := "egn", iso := "enn", value := .fromFinishAlready }
  , { walsCode := "eng", iso := "eng", value := .fromPossessive }
  , { walsCode := "eve", iso := "evn", value := .otherPerfect }
  , { walsCode := "ewe", iso := "ewe", value := .noPerfect }
  , { walsCode := "fij", iso := "fij", value := .fromFinishAlready }
  , { walsCode := "fin", iso := "fin", value := .otherPerfect }
  , { walsCode := "fre", iso := "fra", value := .fromPossessive }
  , { walsCode := "grf", iso := "cab", value := .otherPerfect }
  , { walsCode := "geo", iso := "kat", value := .noPerfect }
  , { walsCode := "ger", iso := "deu", value := .fromPossessive }
  , { walsCode := "goo", iso := "gni", value := .noPerfect }
  , { walsCode := "grb", iso := "grj", value := .otherPerfect }
  , { walsCode := "grk", iso := "ell", value := .fromPossessive }
  , { walsCode := "grw", iso := "kal", value := .noPerfect }
  , { walsCode := "gua", iso := "gug", value := .noPerfect }
  , { walsCode := "gug", iso := "ktd", value := .noPerfect }
  , { walsCode := "hal", iso := "hla", value := .noPerfect }
  , { walsCode := "hau", iso := "hau", value := .noPerfect }
  , { walsCode := "haw", iso := "haw", value := .noPerfect }
  , { walsCode := "hwc", iso := "hwc", value := .noPerfect }
  , { walsCode := "heb", iso := "heb", value := .noPerfect }
  , { walsCode := "hin", iso := "hin", value := .otherPerfect }
  , { walsCode := "hix", iso := "hix", value := .noPerfect }
  , { walsCode := "hmo", iso := "hnj", value := .noPerfect }
  , { walsCode := "hun", iso := "hun", value := .noPerfect }
  , { walsCode := "ice", iso := "isl", value := .fromPossessive }
  , { walsCode := "imo", iso := "imn", value := .otherPerfect }
  , { walsCode := "ind", iso := "ind", value := .fromFinishAlready }
  , { walsCode := "ins", iso := "ike", value := .fromFinishAlready }
  , { walsCode := "ise", iso := "its", value := .fromFinishAlready }
  , { walsCode := "jak", iso := "jac", value := .noPerfect }
  , { walsCode := "jpn", iso := "jpn", value := .noPerfect }
  , { walsCode := "jav", iso := "jav", value := .fromFinishAlready }
  , { walsCode := "jiv", iso := "jiv", value := .otherPerfect }
  , { walsCode := "juh", iso := "ktz", value := .noPerfect }
  , { walsCode := "knk", iso := "kna", value := .noPerfect }
  , { walsCode := "knd", iso := "kan", value := .otherPerfect }
  , { walsCode := "knr", iso := "knc", value := .otherPerfect }
  , { walsCode := "krk", iso := "kyh", value := .otherPerfect }
  , { walsCode := "kay", iso := "gyd", value := .noPerfect }
  , { walsCode := "ket", iso := "ket", value := .noPerfect }
  , { walsCode := "kew", iso := "kew", value := .otherPerfect }
  , { walsCode := "kha", iso := "khk", value := .otherPerfect }
  , { walsCode := "khm", iso := "khm", value := .fromFinishAlready }
  , { walsCode := "kmu", iso := "kjg", value := .fromFinishAlready }
  , { walsCode := "kik", iso := "kik", value := .otherPerfect }
  , { walsCode := "kio", iso := "kio", value := .noPerfect }
  , { walsCode := "koa", iso := "cku", value := .noPerfect }
  , { walsCode := "kor", iso := "kor", value := .noPerfect }
  , { walsCode := "kse", iso := "ses", value := .noPerfect }
  , { walsCode := "kfc", iso := "rop", value := .noPerfect }
  , { walsCode := "kro", iso := "kgo", value := .otherPerfect }
  , { walsCode := "kui", iso := "kxu", value := .otherPerfect }
  , { walsCode := "kya", iso := "gvn", value := .noPerfect }
  , { walsCode := "kji", iso := "kmr", value := .noPerfect }
  , { walsCode := "kut", iso := "kut", value := .noPerfect }
  , { walsCode := "lah", iso := "lhu", value := .otherPerfect }
  , { walsCode := "lai", iso := "cnh", value := .otherPerfect }
  , { walsCode := "lkt", iso := "lkt", value := .noPerfect }
  , { walsCode := "lan", iso := "laj", value := .noPerfect }
  , { walsCode := "lao", iso := "lao", value := .fromFinishAlready }
  , { walsCode := "lat", iso := "lav", value := .otherPerfect }
  , { walsCode := "lav", iso := "lvk", value := .noPerfect }
  , { walsCode := "lez", iso := "lez", value := .otherPerfect }
  , { walsCode := "lda", iso := "lug", value := .otherPerfect }
  , { walsCode := "luv", iso := "lue", value := .otherPerfect }
  , { walsCode := "mne", iso := "nmu", value := .otherPerfect }
  , { walsCode := "mai", iso := "mai", value := .otherPerfect }
  , { walsCode := "mak", iso := "myh", value := .noPerfect }
  , { walsCode := "mal", iso := "plt", value := .noPerfect }
  , { walsCode := "mlt", iso := "mlt", value := .noPerfect }
  , { walsCode := "mnd", iso := "cmn", value := .noPerfect }
  , { walsCode := "myi", iso := "mpc", value := .noPerfect }
  , { walsCode := "man", iso := "mev", value := .otherPerfect }
  , { walsCode := "mao", iso := "mri", value := .otherPerfect }
  , { walsCode := "map", iso := "arn", value := .noPerfect }
  , { walsCode := "mrg", iso := "mrt", value := .otherPerfect }
  , { walsCode := "mar", iso := "mrc", value := .noPerfect }
  , { walsCode := "mrt", iso := "vma", value := .noPerfect }
  , { walsCode := "mau", iso := "mph", value := .noPerfect }
  , { walsCode := "may", iso := "ayz", value := .noPerfect }
  , { walsCode := "mei", iso := "mni", value := .fromFinishAlready }
  , { walsCode := "mxc", iso := "mig", value := .noPerfect }
  , { walsCode := "mtg", iso := "moe", value := .otherPerfect }
  , { walsCode := "mtu", iso := "meu", value := .otherPerfect }
  , { walsCode := "mwe", iso := "mwe", value := .otherPerfect }
  , { walsCode := "nak", iso := "nak", value := .otherPerfect }
  , { walsCode := "kho", iso := "naq", value := .otherPerfect }
  , { walsCode := "ntu", iso := "yrk", value := .noPerfect }
  , { walsCode := "ngm", iso := "sba", value := .noPerfect }
  , { walsCode := "ngi", iso := "wyb", value := .noPerfect }
  , { walsCode := "nbr", iso := "gym", value := .otherPerfect }
  , { walsCode := "nca", iso := "caq", value := .noPerfect }
  , { walsCode := "nim", iso := "nir", value := .noPerfect }
  , { walsCode := "niv", iso := "niv", value := .noPerfect }
  , { walsCode := "ood", iso := "ood", value := .otherPerfect }
  , { walsCode := "ond", iso := "one", value := .noPerfect }
  , { walsCode := "ono", iso := "ons", value := .noPerfect }
  , { walsCode := "orh", iso := "hae", value := .otherPerfect }
  , { walsCode := "pai", iso := "pwn", value := .otherPerfect }
  , { walsCode := "plg", iso := "pll", value := .otherPerfect }
  , { walsCode := "pnn", iso := "pag", value := .noPerfect }
  , { walsCode := "pan", iso := "pan", value := .otherPerfect }
  , { walsCode := "prs", iso := "pes", value := .noPerfect }
  , { walsCode := "prh", iso := "myp", value := .noPerfect }
  , { walsCode := "por", iso := "por", value := .noPerfect }
  , { walsCode := "bng", iso := "byx", value := .otherPerfect }
  , { walsCode := "qco", iso := "quh", value := .noPerfect }
  , { walsCode := "qim", iso := "qvi", value := .noPerfect }
  , { walsCode := "ram", iso := "rma", value := .otherPerfect }
  , { walsCode := "rap", iso := "rap", value := .otherPerfect }
  , { walsCode := "raw", iso := "raw", value := .otherPerfect }
  , { walsCode := "ren", iso := "rel", value := .noPerfect }
  , { walsCode := "rom", iso := "ron", value := .noPerfect }
  , { walsCode := "ruk", iso := "dru", value := .otherPerfect }
  , { walsCode := "rus", iso := "rus", value := .noPerfect }
  , { walsCode := "san", iso := "sag", value := .noPerfect }
  , { walsCode := "snm", iso := "xsu", value := .noPerfect }
  , { walsCode := "sml", iso := "sza", value := .fromFinishAlready }
  , { walsCode := "snc", iso := "see", value := .noPerfect }
  , { walsCode := "ses", iso := "sot", value := .otherPerfect }
  , { walsCode := "shu", iso := "shs", value := .noPerfect }
  , { walsCode := "sla", iso := "den", value := .otherPerfect }
  , { walsCode := "som", iso := "som", value := .noPerfect }
  , { walsCode := "spa", iso := "spa", value := .fromPossessive }
  , { walsCode := "sue", iso := "sue", value := .noPerfect }
  , { walsCode := "sun", iso := "sun", value := .fromFinishAlready }
  , { walsCode := "sup", iso := "spp", value := .otherPerfect }
  , { walsCode := "swa", iso := "swh", value := .otherPerfect }
  , { walsCode := "swe", iso := "swe", value := .fromPossessive }
  , { walsCode := "tag", iso := "tgl", value := .noPerfect }
  , { walsCode := "tah", iso := "tah", value := .otherPerfect }
  , { walsCode := "tml", iso := "tam", value := .otherPerfect }
  , { walsCode := "tga", iso := "hrc", value := .noPerfect }
  , { walsCode := "tem", iso := "kdh", value := .otherPerfect }
  , { walsCode := "tne", iso := "tem", value := .fromFinishAlready }
  , { walsCode := "tny", iso := "kza", value := .fromFinishAlready }
  , { walsCode := "tha", iso := "tha", value := .fromFinishAlready }
  , { walsCode := "tig", iso := "tir", value := .noPerfect }
  , { walsCode := "tgr", iso := "tig", value := .otherPerfect }
  , { walsCode := "tiw", iso := "tiw", value := .noPerfect }
  , { walsCode := "toj", iso := "toj", value := .otherPerfect }
  , { walsCode := "tpi", iso := "tpi", value := .noPerfect }
  , { walsCode := "tug", iso := "thv", value := .noPerfect }
  , { walsCode := "tuc", iso := "tuo", value := .otherPerfect }
  , { walsCode := "tuk", iso := "", value := .noPerfect }
  , { walsCode := "tur", iso := "tur", value := .noPerfect }
  , { walsCode := "udm", iso := "udm", value := .otherPerfect }
  , { walsCode := "uyg", iso := "uig", value := .otherPerfect }
  , { walsCode := "vie", iso := "vie", value := .otherPerfect }
  , { walsCode := "wra", iso := "wba", value := .noPerfect }
  , { walsCode := "war", iso := "pav", value := .noPerfect }
  , { walsCode := "wic", iso := "wic", value := .noPerfect }
  , { walsCode := "wch", iso := "mzh", value := .noPerfect }
  , { walsCode := "wly", iso := "wal", value := .noPerfect }
  , { walsCode := "wlf", iso := "wol", value := .otherPerfect }
  , { walsCode := "wor", iso := "wro", value := .noPerfect }
  , { walsCode := "ygr", iso := "ygr", value := .otherPerfect }
  , { walsCode := "yag", iso := "yad", value := .noPerfect }
  , { walsCode := "yaq", iso := "yaq", value := .noPerfect }
  , { walsCode := "yes", iso := "yss", value := .noPerfect }
  , { walsCode := "yor", iso := "yor", value := .fromFinishAlready }
  , { walsCode := "yct", iso := "yua", value := .noPerfect }
  , { walsCode := "yko", iso := "yux", value := .noPerfect }
  , { walsCode := "zqc", iso := "zoc", value := .otherPerfect }
  , { walsCode := "zul", iso := "zul", value := .otherPerfect }
  , { walsCode := "zun", iso := "zun", value := .noPerfect }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F68A
