import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 66A: The Past Tense
@cite{dahl-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 66A`.

Chapter 66, 222 languages.
-/

namespace Core.WALS.F66A

/-- WALS 66A values. -/
inductive PastTenseType where
  /-- Present, no remoteness distinctions (94 languages). -/
  | presentNoRemotenessDistinctions
  /-- Present, 2-3 remoteness distinctions (38 languages). -/
  | present23RemotenessDistinctions
  /-- Present, 4 or more remoteness distinctions (2 languages). -/
  | present4OrMoreRemotenessDistinctions
  /-- No past tense (88 languages). -/
  | noPastTense
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 66A dataset (222 languages). -/
def allData : List (Datapoint PastTenseType) :=
  [ { walsCode := "abi", iso := "axb", value := .noPastTense }
  , { walsCode := "abk", iso := "abk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "aco", iso := "kjq", value := .noPastTense }
  , { walsCode := "afr", iso := "afr", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ain", iso := "ain", value := .noPastTense }
  , { walsCode := "akn", iso := "aka", value := .noPastTense }
  , { walsCode := "ala", iso := "amp", value := .present23RemotenessDistinctions }
  , { walsCode := "alw", iso := "alh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "aly", iso := "aly", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ame", iso := "aey", value := .present23RemotenessDistinctions }
  , { walsCode := "amh", iso := "amh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "apu", iso := "apu", value := .noPastTense }
  , { walsCode := "aeg", iso := "arz", value := .presentNoRemotenessDistinctions }
  , { walsCode := "atu", iso := "aeb", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ana", iso := "aro", value := .noPastTense }
  , { walsCode := "arp", iso := "ape", value := .noPastTense }
  , { walsCode := "arm", iso := "hye", value := .presentNoRemotenessDistinctions }
  , { walsCode := "asm", iso := "cns", value := .present23RemotenessDistinctions }
  , { walsCode := "atc", iso := "upv", value := .presentNoRemotenessDistinctions }
  , { walsCode := "avo", iso := "avu", value := .presentNoRemotenessDistinctions }
  , { walsCode := "awp", iso := "kwi", value := .presentNoRemotenessDistinctions }
  , { walsCode := "awn", iso := "awn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "aze", iso := "", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bag", iso := "bmi", value := .noPastTense }
  , { walsCode := "blc", iso := "bgn", value := .present23RemotenessDistinctions }
  , { walsCode := "bnj", iso := "bdy", value := .presentNoRemotenessDistinctions }
  , { walsCode := "brs", iso := "bsn", value := .present23RemotenessDistinctions }
  , { walsCode := "bar", iso := "bfa", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bsq", iso := "eus", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bej", iso := "bej", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ben", iso := "ben", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bma", iso := "tzm", value := .noPastTense }
  , { walsCode := "bon", iso := "bpu", value := .present23RemotenessDistinctions }
  , { walsCode := "brh", iso := "brh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bul", iso := "bul", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bui", iso := "bzq", value := .noPastTense }
  , { walsCode := "but", iso := "bxm", value := .present23RemotenessDistinctions }
  , { walsCode := "brm", iso := "mya", value := .noPastTense }
  , { walsCode := "bur", iso := "bsk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "cnl", iso := "ram", value := .present23RemotenessDistinctions }
  , { walsCode := "cnt", iso := "yue", value := .noPastTense }
  , { walsCode := "ceb", iso := "ceb", value := .noPastTense }
  , { walsCode := "cha", iso := "cha", value := .noPastTense }
  , { walsCode := "cpn", iso := "cdm", value := .noPastTense }
  , { walsCode := "cyn", iso := "chy", value := .present23RemotenessDistinctions }
  , { walsCode := "cpl", iso := "cpa", value := .present23RemotenessDistinctions }
  , { walsCode := "chk", iso := "ckt", value := .noPastTense }
  , { walsCode := "cuu", iso := "chk", value := .noPastTense }
  , { walsCode := "cbo", iso := "cao", value := .present4OrMoreRemotenessDistinctions }
  , { walsCode := "coc", iso := "cod", value := .present23RemotenessDistinctions }
  , { walsCode := "cre", iso := "crk", value := .noPastTense }
  , { walsCode := "dag", iso := "dgz", value := .presentNoRemotenessDistinctions }
  , { walsCode := "dni", iso := "dni", value := .present23RemotenessDistinctions }
  , { walsCode := "did", iso := "did", value := .presentNoRemotenessDistinctions }
  , { walsCode := "dio", iso := "dyo", value := .noPastTense }
  , { walsCode := "egn", iso := "enn", value := .noPastTense }
  , { walsCode := "eng", iso := "eng", value := .presentNoRemotenessDistinctions }
  , { walsCode := "eve", iso := "evn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ewe", iso := "ewe", value := .noPastTense }
  , { walsCode := "fij", iso := "fij", value := .presentNoRemotenessDistinctions }
  , { walsCode := "fin", iso := "fin", value := .presentNoRemotenessDistinctions }
  , { walsCode := "fre", iso := "fra", value := .presentNoRemotenessDistinctions }
  , { walsCode := "grf", iso := "cab", value := .noPastTense }
  , { walsCode := "geo", iso := "kat", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ger", iso := "deu", value := .presentNoRemotenessDistinctions }
  , { walsCode := "goo", iso := "gni", value := .presentNoRemotenessDistinctions }
  , { walsCode := "grb", iso := "grj", value := .present23RemotenessDistinctions }
  , { walsCode := "grk", iso := "ell", value := .presentNoRemotenessDistinctions }
  , { walsCode := "grw", iso := "kal", value := .noPastTense }
  , { walsCode := "gua", iso := "gug", value := .presentNoRemotenessDistinctions }
  , { walsCode := "gug", iso := "ktd", value := .presentNoRemotenessDistinctions }
  , { walsCode := "hal", iso := "hla", value := .noPastTense }
  , { walsCode := "hau", iso := "hau", value := .noPastTense }
  , { walsCode := "haw", iso := "haw", value := .noPastTense }
  , { walsCode := "hwc", iso := "hwc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "heb", iso := "heb", value := .presentNoRemotenessDistinctions }
  , { walsCode := "hin", iso := "hin", value := .presentNoRemotenessDistinctions }
  , { walsCode := "hix", iso := "hix", value := .present23RemotenessDistinctions }
  , { walsCode := "hmo", iso := "hnj", value := .noPastTense }
  , { walsCode := "hun", iso := "hun", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ice", iso := "isl", value := .presentNoRemotenessDistinctions }
  , { walsCode := "imo", iso := "imn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ind", iso := "ind", value := .noPastTense }
  , { walsCode := "ins", iso := "ike", value := .present23RemotenessDistinctions }
  , { walsCode := "ise", iso := "its", value := .noPastTense }
  , { walsCode := "jak", iso := "jac", value := .noPastTense }
  , { walsCode := "jpn", iso := "jpn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "jav", iso := "jav", value := .noPastTense }
  , { walsCode := "jiv", iso := "jiv", value := .presentNoRemotenessDistinctions }
  , { walsCode := "juh", iso := "ktz", value := .noPastTense }
  , { walsCode := "knk", iso := "kna", value := .presentNoRemotenessDistinctions }
  , { walsCode := "knd", iso := "kan", value := .presentNoRemotenessDistinctions }
  , { walsCode := "knr", iso := "knc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "krk", iso := "kyh", value := .noPastTense }
  , { walsCode := "kay", iso := "gyd", value := .noPastTense }
  , { walsCode := "ket", iso := "ket", value := .noPastTense }
  , { walsCode := "kew", iso := "kew", value := .present23RemotenessDistinctions }
  , { walsCode := "kha", iso := "khk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "khm", iso := "khm", value := .noPastTense }
  , { walsCode := "kmu", iso := "kjg", value := .noPastTense }
  , { walsCode := "kik", iso := "kik", value := .present23RemotenessDistinctions }
  , { walsCode := "kio", iso := "kio", value := .noPastTense }
  , { walsCode := "koa", iso := "cku", value := .present23RemotenessDistinctions }
  , { walsCode := "kor", iso := "kor", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kse", iso := "ses", value := .noPastTense }
  , { walsCode := "kfc", iso := "rop", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kro", iso := "kgo", value := .noPastTense }
  , { walsCode := "kui", iso := "kxu", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kya", iso := "gvn", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kji", iso := "kmr", value := .presentNoRemotenessDistinctions }
  , { walsCode := "kut", iso := "kut", value := .noPastTense }
  , { walsCode := "lah", iso := "lhu", value := .noPastTense }
  , { walsCode := "lai", iso := "cnh", value := .noPastTense }
  , { walsCode := "lkt", iso := "lkt", value := .noPastTense }
  , { walsCode := "lan", iso := "laj", value := .noPastTense }
  , { walsCode := "lao", iso := "lao", value := .noPastTense }
  , { walsCode := "lat", iso := "lav", value := .presentNoRemotenessDistinctions }
  , { walsCode := "lav", iso := "lvk", value := .noPastTense }
  , { walsCode := "lez", iso := "lez", value := .presentNoRemotenessDistinctions }
  , { walsCode := "lda", iso := "lug", value := .present23RemotenessDistinctions }
  , { walsCode := "luv", iso := "lue", value := .present23RemotenessDistinctions }
  , { walsCode := "mne", iso := "nmu", value := .present23RemotenessDistinctions }
  , { walsCode := "mai", iso := "mai", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mak", iso := "myh", value := .noPastTense }
  , { walsCode := "mal", iso := "plt", value := .noPastTense }
  , { walsCode := "mlt", iso := "mlt", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mnd", iso := "cmn", value := .noPastTense }
  , { walsCode := "myi", iso := "mpc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "man", iso := "mev", value := .noPastTense }
  , { walsCode := "mao", iso := "mri", value := .presentNoRemotenessDistinctions }
  , { walsCode := "map", iso := "arn", value := .noPastTense }
  , { walsCode := "mrg", iso := "mrt", value := .noPastTense }
  , { walsCode := "mar", iso := "mrc", value := .noPastTense }
  , { walsCode := "mrt", iso := "vma", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mau", iso := "mph", value := .presentNoRemotenessDistinctions }
  , { walsCode := "may", iso := "ayz", value := .noPastTense }
  , { walsCode := "mei", iso := "mni", value := .noPastTense }
  , { walsCode := "mxc", iso := "mig", value := .noPastTense }
  , { walsCode := "mtg", iso := "moe", value := .presentNoRemotenessDistinctions }
  , { walsCode := "mtu", iso := "meu", value := .noPastTense }
  , { walsCode := "mwe", iso := "mwe", value := .present23RemotenessDistinctions }
  , { walsCode := "nak", iso := "nak", value := .noPastTense }
  , { walsCode := "kho", iso := "naq", value := .present23RemotenessDistinctions }
  , { walsCode := "ntu", iso := "yrk", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ngm", iso := "sba", value := .noPastTense }
  , { walsCode := "ngi", iso := "wyb", value := .presentNoRemotenessDistinctions }
  , { walsCode := "nbr", iso := "gym", value := .present23RemotenessDistinctions }
  , { walsCode := "nca", iso := "caq", value := .noPastTense }
  , { walsCode := "nim", iso := "nir", value := .present23RemotenessDistinctions }
  , { walsCode := "niv", iso := "niv", value := .noPastTense }
  , { walsCode := "ood", iso := "ood", value := .present23RemotenessDistinctions }
  , { walsCode := "ond", iso := "one", value := .noPastTense }
  , { walsCode := "ono", iso := "ons", value := .present23RemotenessDistinctions }
  , { walsCode := "orh", iso := "hae", value := .presentNoRemotenessDistinctions }
  , { walsCode := "pai", iso := "pwn", value := .noPastTense }
  , { walsCode := "plg", iso := "pll", value := .noPastTense }
  , { walsCode := "pnn", iso := "pag", value := .noPastTense }
  , { walsCode := "pan", iso := "pan", value := .presentNoRemotenessDistinctions }
  , { walsCode := "prs", iso := "pes", value := .presentNoRemotenessDistinctions }
  , { walsCode := "prh", iso := "myp", value := .noPastTense }
  , { walsCode := "por", iso := "por", value := .presentNoRemotenessDistinctions }
  , { walsCode := "bng", iso := "byx", value := .noPastTense }
  , { walsCode := "qco", iso := "quh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "qim", iso := "qvi", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ram", iso := "rma", value := .presentNoRemotenessDistinctions }
  , { walsCode := "rap", iso := "rap", value := .presentNoRemotenessDistinctions }
  , { walsCode := "raw", iso := "raw", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ren", iso := "rel", value := .noPastTense }
  , { walsCode := "rom", iso := "ron", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ruk", iso := "dru", value := .presentNoRemotenessDistinctions }
  , { walsCode := "rus", iso := "rus", value := .presentNoRemotenessDistinctions }
  , { walsCode := "san", iso := "sag", value := .noPastTense }
  , { walsCode := "snm", iso := "xsu", value := .present23RemotenessDistinctions }
  , { walsCode := "sml", iso := "sza", value := .noPastTense }
  , { walsCode := "snc", iso := "see", value := .noPastTense }
  , { walsCode := "ses", iso := "sot", value := .present23RemotenessDistinctions }
  , { walsCode := "shu", iso := "shs", value := .noPastTense }
  , { walsCode := "sla", iso := "den", value := .present23RemotenessDistinctions }
  , { walsCode := "som", iso := "som", value := .presentNoRemotenessDistinctions }
  , { walsCode := "spa", iso := "spa", value := .presentNoRemotenessDistinctions }
  , { walsCode := "sue", iso := "sue", value := .present23RemotenessDistinctions }
  , { walsCode := "sun", iso := "sun", value := .noPastTense }
  , { walsCode := "sup", iso := "spp", value := .present23RemotenessDistinctions }
  , { walsCode := "swa", iso := "swh", value := .presentNoRemotenessDistinctions }
  , { walsCode := "swe", iso := "swe", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tag", iso := "tgl", value := .noPastTense }
  , { walsCode := "tah", iso := "tah", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tml", iso := "tam", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tga", iso := "hrc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tem", iso := "kdh", value := .noPastTense }
  , { walsCode := "tne", iso := "tem", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tny", iso := "kza", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tha", iso := "tha", value := .noPastTense }
  , { walsCode := "tig", iso := "tir", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tgr", iso := "tig", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tiw", iso := "tiw", value := .presentNoRemotenessDistinctions }
  , { walsCode := "toj", iso := "toj", value := .noPastTense }
  , { walsCode := "tpi", iso := "tpi", value := .presentNoRemotenessDistinctions }
  , { walsCode := "tug", iso := "thv", value := .noPastTense }
  , { walsCode := "tuc", iso := "tuo", value := .present23RemotenessDistinctions }
  , { walsCode := "tuk", iso := "", value := .noPastTense }
  , { walsCode := "tur", iso := "tur", value := .presentNoRemotenessDistinctions }
  , { walsCode := "udm", iso := "udm", value := .present23RemotenessDistinctions }
  , { walsCode := "uyg", iso := "uig", value := .present23RemotenessDistinctions }
  , { walsCode := "vie", iso := "vie", value := .noPastTense }
  , { walsCode := "wra", iso := "wba", value := .presentNoRemotenessDistinctions }
  , { walsCode := "war", iso := "pav", value := .noPastTense }
  , { walsCode := "wic", iso := "wic", value := .noPastTense }
  , { walsCode := "wch", iso := "mzh", value := .present23RemotenessDistinctions }
  , { walsCode := "wly", iso := "wal", value := .noPastTense }
  , { walsCode := "wlf", iso := "wol", value := .presentNoRemotenessDistinctions }
  , { walsCode := "wor", iso := "wro", value := .presentNoRemotenessDistinctions }
  , { walsCode := "ygr", iso := "ygr", value := .noPastTense }
  , { walsCode := "yag", iso := "yad", value := .present4OrMoreRemotenessDistinctions }
  , { walsCode := "yaq", iso := "yaq", value := .presentNoRemotenessDistinctions }
  , { walsCode := "yes", iso := "yss", value := .present23RemotenessDistinctions }
  , { walsCode := "yor", iso := "yor", value := .noPastTense }
  , { walsCode := "yct", iso := "yua", value := .noPastTense }
  , { walsCode := "yko", iso := "yux", value := .noPastTense }
  , { walsCode := "zqc", iso := "zoc", value := .presentNoRemotenessDistinctions }
  , { walsCode := "zul", iso := "zul", value := .present23RemotenessDistinctions }
  , { walsCode := "zun", iso := "zun", value := .presentNoRemotenessDistinctions }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F66A
