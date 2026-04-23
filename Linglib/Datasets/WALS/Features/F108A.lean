import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 108A: Antipassive Constructions
@cite{polinsky-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 108A`.

Chapter 108, 194 languages.
-/

namespace Datasets.WALS.F108A

/-- WALS 108A values. -/
inductive AntipassiveType where
  /-- Implicit patient (18 languages). -/
  | implicitPatient
  /-- Oblique patient (30 languages). -/
  | obliquePatient
  /-- No antipassive (146 languages). -/
  | noAntipassive
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 108A dataset (194 languages). -/
def allData : List (Datapoint AntipassiveType) :=
  [ { walsCode := "abk", iso := "abk", value := .noAntipassive }
  , { walsCode := "aco", iso := "kjq", value := .implicitPatient }
  , { walsCode := "ain", iso := "ain", value := .noAntipassive }
  , { walsCode := "ala", iso := "amp", value := .noAntipassive }
  , { walsCode := "ame", iso := "aey", value := .noAntipassive }
  , { walsCode := "apu", iso := "apu", value := .noAntipassive }
  , { walsCode := "aeg", iso := "arz", value := .noAntipassive }
  , { walsCode := "arp", iso := "ape", value := .noAntipassive }
  , { walsCode := "arc", iso := "aqc", value := .obliquePatient }
  , { walsCode := "arm", iso := "hye", value := .noAntipassive }
  , { walsCode := "asm", iso := "cns", value := .noAntipassive }
  , { walsCode := "awp", iso := "kwi", value := .noAntipassive }
  , { walsCode := "bag", iso := "bmi", value := .noAntipassive }
  , { walsCode := "brs", iso := "bsn", value := .noAntipassive }
  , { walsCode := "bsq", iso := "eus", value := .obliquePatient }
  , { walsCode := "bkr", iso := "btx", value := .noAntipassive }
  , { walsCode := "bej", iso := "bej", value := .noAntipassive }
  , { walsCode := "bma", iso := "tzm", value := .noAntipassive }
  , { walsCode := "bez", iso := "kap", value := .obliquePatient }
  , { walsCode := "brh", iso := "brh", value := .noAntipassive }
  , { walsCode := "brm", iso := "mya", value := .noAntipassive }
  , { walsCode := "bur", iso := "bsk", value := .noAntipassive }
  , { walsCode := "cah", iso := "chl", value := .implicitPatient }
  , { walsCode := "cak", iso := "cak", value := .implicitPatient }
  , { walsCode := "cnl", iso := "ram", value := .obliquePatient }
  , { walsCode := "chh", iso := "sgw", value := .noAntipassive }
  , { walsCode := "cha", iso := "cha", value := .obliquePatient }
  , { walsCode := "chc", iso := "che", value := .obliquePatient }
  , { walsCode := "cic", iso := "nya", value := .noAntipassive }
  , { walsCode := "cct", iso := "cho", value := .obliquePatient }
  , { walsCode := "chk", iso := "ckt", value := .obliquePatient }
  , { walsCode := "cmn", iso := "com", value := .implicitPatient }
  , { walsCode := "cre", iso := "crk", value := .implicitPatient }
  , { walsCode := "dag", iso := "dgz", value := .noAntipassive }
  , { walsCode := "dni", iso := "dni", value := .noAntipassive }
  , { walsCode := "diy", iso := "dif", value := .implicitPatient }
  , { walsCode := "djr", iso := "ddj", value := .obliquePatient }
  , { walsCode := "dji", iso := "jig", value := .noAntipassive }
  , { walsCode := "don", iso := "kmc", value := .noAntipassive }
  , { walsCode := "dyi", iso := "dbl", value := .obliquePatient }
  , { walsCode := "eml", iso := "emb", value := .obliquePatient }
  , { walsCode := "eng", iso := "eng", value := .noAntipassive }
  , { walsCode := "epe", iso := "sja", value := .noAntipassive }
  , { walsCode := "eve", iso := "evn", value := .noAntipassive }
  , { walsCode := "ewe", iso := "ewe", value := .noAntipassive }
  , { walsCode := "fij", iso := "fij", value := .noAntipassive }
  , { walsCode := "fin", iso := "fin", value := .noAntipassive }
  , { walsCode := "fre", iso := "fra", value := .noAntipassive }
  , { walsCode := "gae", iso := "gla", value := .noAntipassive }
  , { walsCode := "geo", iso := "kat", value := .noAntipassive }
  , { walsCode := "ger", iso := "deu", value := .noAntipassive }
  , { walsCode := "gdi", iso := "god", value := .noAntipassive }
  , { walsCode := "god", iso := "gdo", value := .implicitPatient }
  , { walsCode := "goo", iso := "gni", value := .obliquePatient }
  , { walsCode := "grb", iso := "grj", value := .noAntipassive }
  , { walsCode := "grk", iso := "ell", value := .noAntipassive }
  , { walsCode := "grw", iso := "kal", value := .obliquePatient }
  , { walsCode := "gua", iso := "gug", value := .noAntipassive }
  , { walsCode := "hli", iso := "hur", value := .obliquePatient }
  , { walsCode := "hau", iso := "hau", value := .noAntipassive }
  , { walsCode := "heb", iso := "heb", value := .noAntipassive }
  , { walsCode := "hin", iso := "hin", value := .noAntipassive }
  , { walsCode := "hix", iso := "hix", value := .noAntipassive }
  , { walsCode := "hmo", iso := "hnj", value := .noAntipassive }
  , { walsCode := "hun", iso := "hun", value := .noAntipassive }
  , { walsCode := "hzb", iso := "huz", value := .implicitPatient }
  , { walsCode := "ice", iso := "isl", value := .noAntipassive }
  , { walsCode := "igb", iso := "ibo", value := .noAntipassive }
  , { walsCode := "ika", iso := "arh", value := .noAntipassive }
  , { walsCode := "imo", iso := "imn", value := .noAntipassive }
  , { walsCode := "ind", iso := "ind", value := .noAntipassive }
  , { walsCode := "ing", iso := "inh", value := .noAntipassive }
  , { walsCode := "irq", iso := "irk", value := .noAntipassive }
  , { walsCode := "jak", iso := "jac", value := .implicitPatient }
  , { walsCode := "jpn", iso := "jpn", value := .noAntipassive }
  , { walsCode := "juh", iso := "ktz", value := .noAntipassive }
  , { walsCode := "kab", iso := "kbd", value := .obliquePatient }
  , { walsCode := "kam", iso := "xbr", value := .noAntipassive }
  , { walsCode := "knd", iso := "kan", value := .noAntipassive }
  , { walsCode := "knr", iso := "knc", value := .noAntipassive }
  , { walsCode := "kpm", iso := "pam", value := .implicitPatient }
  , { walsCode := "krk", iso := "kyh", value := .noAntipassive }
  , { walsCode := "kas", iso := "kas", value := .noAntipassive }
  , { walsCode := "kay", iso := "gyd", value := .noAntipassive }
  , { walsCode := "ket", iso := "ket", value := .noAntipassive }
  , { walsCode := "kew", iso := "kew", value := .noAntipassive }
  , { walsCode := "khk", iso := "kjh", value := .noAntipassive }
  , { walsCode := "kha", iso := "khk", value := .noAntipassive }
  , { walsCode := "khs", iso := "kha", value := .noAntipassive }
  , { walsCode := "klv", iso := "kij", value := .noAntipassive }
  , { walsCode := "kio", iso := "kio", value := .implicitPatient }
  , { walsCode := "kgz", iso := "kir", value := .noAntipassive }
  , { walsCode := "koa", iso := "cku", value := .noAntipassive }
  , { walsCode := "kob", iso := "kpw", value := .noAntipassive }
  , { walsCode := "kor", iso := "kor", value := .noAntipassive }
  , { walsCode := "kfe", iso := "kfz", value := .noAntipassive }
  , { walsCode := "kse", iso := "ses", value := .implicitPatient }
  , { walsCode := "kro", iso := "kgo", value := .implicitPatient }
  , { walsCode := "kut", iso := "kut", value := .noAntipassive }
  , { walsCode := "lai", iso := "cnh", value := .obliquePatient }
  , { walsCode := "lak", iso := "lbe", value := .obliquePatient }
  , { walsCode := "lkt", iso := "lkt", value := .noAntipassive }
  , { walsCode := "lan", iso := "laj", value := .implicitPatient }
  , { walsCode := "lat", iso := "lav", value := .noAntipassive }
  , { walsCode := "lav", iso := "lvk", value := .implicitPatient }
  , { walsCode := "lez", iso := "lez", value := .noAntipassive }
  , { walsCode := "lin", iso := "lin", value := .noAntipassive }
  , { walsCode := "luv", iso := "lue", value := .noAntipassive }
  , { walsCode := "mac", iso := "mbc", value := .noAntipassive }
  , { walsCode := "mak", iso := "myh", value := .noAntipassive }
  , { walsCode := "mal", iso := "plt", value := .noAntipassive }
  , { walsCode := "mam", iso := "mam", value := .obliquePatient }
  , { walsCode := "mnd", iso := "cmn", value := .noAntipassive }
  , { walsCode := "myi", iso := "mpc", value := .implicitPatient }
  , { walsCode := "mao", iso := "mri", value := .noAntipassive }
  , { walsCode := "map", iso := "arn", value := .noAntipassive }
  , { walsCode := "mar", iso := "mrc", value := .noAntipassive }
  , { walsCode := "mrt", iso := "vma", value := .noAntipassive }
  , { walsCode := "mau", iso := "mph", value := .noAntipassive }
  , { walsCode := "may", iso := "ayz", value := .noAntipassive }
  , { walsCode := "mei", iso := "mni", value := .noAntipassive }
  , { walsCode := "mxc", iso := "mig", value := .noAntipassive }
  , { walsCode := "mrl", iso := "mur", value := .noAntipassive }
  , { walsCode := "kho", iso := "naq", value := .noAntipassive }
  , { walsCode := "ndy", iso := "djk", value := .noAntipassive }
  , { walsCode := "nez", iso := "nez", value := .obliquePatient }
  , { walsCode := "ngi", iso := "wyb", value := .noAntipassive }
  , { walsCode := "niv", iso := "niv", value := .noAntipassive }
  , { walsCode := "nko", iso := "cgg", value := .noAntipassive }
  , { walsCode := "nug", iso := "nuy", value := .noAntipassive }
  , { walsCode := "oji", iso := "", value := .obliquePatient }
  , { walsCode := "ond", iso := "one", value := .noAntipassive }
  , { walsCode := "orh", iso := "hae", value := .noAntipassive }
  , { walsCode := "otm", iso := "ote", value := .noAntipassive }
  , { walsCode := "pms", iso := "pma", value := .noAntipassive }
  , { walsCode := "pai", iso := "pwn", value := .obliquePatient }
  , { walsCode := "pan", iso := "pan", value := .noAntipassive }
  , { walsCode := "psm", iso := "pqm", value := .noAntipassive }
  , { walsCode := "pau", iso := "pad", value := .noAntipassive }
  , { walsCode := "prs", iso := "pes", value := .noAntipassive }
  , { walsCode := "prh", iso := "myp", value := .noAntipassive }
  , { walsCode := "pmc", iso := "poo", value := .noAntipassive }
  , { walsCode := "par", iso := "lkr", value := .obliquePatient }
  , { walsCode := "qaf", iso := "aar", value := .noAntipassive }
  , { walsCode := "qim", iso := "qvi", value := .noAntipassive }
  , { walsCode := "ram", iso := "rma", value := .noAntipassive }
  , { walsCode := "rap", iso := "rap", value := .noAntipassive }
  , { walsCode := "rus", iso := "rus", value := .noAntipassive }
  , { walsCode := "sam", iso := "smo", value := .noAntipassive }
  , { walsCode := "san", iso := "sag", value := .noAntipassive }
  , { walsCode := "snm", iso := "xsu", value := .obliquePatient }
  , { walsCode := "snc", iso := "see", value := .noAntipassive }
  , { walsCode := "shk", iso := "shp", value := .noAntipassive }
  , { walsCode := "sla", iso := "den", value := .noAntipassive }
  , { walsCode := "spa", iso := "spa", value := .noAntipassive }
  , { walsCode := "sue", iso := "sue", value := .noAntipassive }
  , { walsCode := "sup", iso := "spp", value := .noAntipassive }
  , { walsCode := "swa", iso := "swh", value := .noAntipassive }
  , { walsCode := "tab", iso := "mky", value := .noAntipassive }
  , { walsCode := "tag", iso := "tgl", value := .noAntipassive }
  , { walsCode := "tap", iso := "gpn", value := .noAntipassive }
  , { walsCode := "tml", iso := "tam", value := .noAntipassive }
  , { walsCode := "tau", iso := "tya", value := .noAntipassive }
  , { walsCode := "tha", iso := "tha", value := .noAntipassive }
  , { walsCode := "tho", iso := "thp", value := .implicitPatient }
  , { walsCode := "tiw", iso := "tiw", value := .noAntipassive }
  , { walsCode := "tsz", iso := "ddo", value := .obliquePatient }
  , { walsCode := "tuk", iso := "", value := .noAntipassive }
  , { walsCode := "tur", iso := "tur", value := .noAntipassive }
  , { walsCode := "tvl", iso := "tvl", value := .noAntipassive }
  , { walsCode := "tzu", iso := "tzj", value := .obliquePatient }
  , { walsCode := "ukr", iso := "ukr", value := .noAntipassive }
  , { walsCode := "una", iso := "mtg", value := .noAntipassive }
  , { walsCode := "usa", iso := "wnu", value := .noAntipassive }
  , { walsCode := "uzb", iso := "", value := .noAntipassive }
  , { walsCode := "vie", iso := "vie", value := .noAntipassive }
  , { walsCode := "wam", iso := "wmb", value := .noAntipassive }
  , { walsCode := "wra", iso := "wba", value := .noAntipassive }
  , { walsCode := "wrd", iso := "wrr", value := .obliquePatient }
  , { walsCode := "war", iso := "pav", value := .noAntipassive }
  , { walsCode := "wgu", iso := "wrg", value := .obliquePatient }
  , { walsCode := "wic", iso := "wic", value := .noAntipassive }
  , { walsCode := "wch", iso := "mzh", value := .noAntipassive }
  , { walsCode := "yag", iso := "yad", value := .noAntipassive }
  , { walsCode := "yaq", iso := "yaq", value := .noAntipassive }
  , { walsCode := "yaz", iso := "yah", value := .noAntipassive }
  , { walsCode := "yid", iso := "yii", value := .obliquePatient }
  , { walsCode := "yim", iso := "yee", value := .noAntipassive }
  , { walsCode := "yor", iso := "yor", value := .noAntipassive }
  , { walsCode := "yuk", iso := "gcd", value := .obliquePatient }
  , { walsCode := "ypk", iso := "esu", value := .obliquePatient }
  , { walsCode := "yur", iso := "yur", value := .noAntipassive }
  , { walsCode := "zqc", iso := "zoc", value := .implicitPatient }
  , { walsCode := "zul", iso := "zul", value := .noAntipassive }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F108A
