import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 22A: Inflectional Synthesis of the Verb
@cite{bickel-nichols-2013c}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 22A`.

Chapter 22, 145 languages.
-/

namespace Datasets.WALS.F22A

/-- WALS 22A values. -/
inductive InflectionalSynthesis where
  /-- 0-1 category per word (5 languages). -/
  | categoryPerWord0_1
  /-- 2-3 categories per word (24 languages). -/
  | categoriesPerWord2_3
  /-- 4-5 categories per word (52 languages). -/
  | categoriesPerWord4_5
  /-- 6-7 categories per word (31 languages). -/
  | categoriesPerWord6_7
  /-- 8-9 categories per word (24 languages). -/
  | categoriesPerWord8_9
  /-- 10-11 categories per word (7 languages). -/
  | categoriesPerWord10_11
  /-- 12-13 categories per word (2 languages). -/
  | categoriesPerWord12_13
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 22A dataset (145 languages). -/
def allData : List (Datapoint InflectionalSynthesis) :=
  [ { walsCode := "abk", iso := "abk", value := .categoriesPerWord10_11 }
  , { walsCode := "aco", iso := "kjq", value := .categoriesPerWord4_5 }
  , { walsCode := "ash", iso := "ady", value := .categoriesPerWord8_9 }
  , { walsCode := "ain", iso := "ain", value := .categoriesPerWord4_5 }
  , { walsCode := "ala", iso := "amp", value := .categoriesPerWord10_11 }
  , { walsCode := "ame", iso := "aey", value := .categoriesPerWord6_7 }
  , { walsCode := "apu", iso := "apu", value := .categoriesPerWord6_7 }
  , { walsCode := "aeg", iso := "arz", value := .categoriesPerWord6_7 }
  , { walsCode := "arp", iso := "ape", value := .categoriesPerWord4_5 }
  , { walsCode := "arm", iso := "hye", value := .categoriesPerWord2_3 }
  , { walsCode := "amp", iso := "aer", value := .categoriesPerWord4_5 }
  , { walsCode := "asm", iso := "cns", value := .categoriesPerWord4_5 }
  , { walsCode := "atk", iso := "aqp", value := .categoriesPerWord8_9 }
  , { walsCode := "awp", iso := "kwi", value := .categoriesPerWord8_9 }
  , { walsCode := "aym", iso := "ayr", value := .categoriesPerWord8_9 }
  , { walsCode := "bag", iso := "bmi", value := .categoriesPerWord6_7 }
  , { walsCode := "brs", iso := "bsn", value := .categoriesPerWord4_5 }
  , { walsCode := "bsq", iso := "eus", value := .categoriesPerWord4_5 }
  , { walsCode := "bej", iso := "bej", value := .categoriesPerWord4_5 }
  , { walsCode := "bel", iso := "byw", value := .categoriesPerWord6_7 }
  , { walsCode := "bma", iso := "tzm", value := .categoriesPerWord6_7 }
  , { walsCode := "brr", iso := "bor", value := .categoriesPerWord4_5 }
  , { walsCode := "brh", iso := "brh", value := .categoriesPerWord2_3 }
  , { walsCode := "brm", iso := "mya", value := .categoriesPerWord2_3 }
  , { walsCode := "bur", iso := "bsk", value := .categoriesPerWord8_9 }
  , { walsCode := "cnl", iso := "ram", value := .categoriesPerWord4_5 }
  , { walsCode := "cyv", iso := "cyb", value := .categoriesPerWord6_7 }
  , { walsCode := "cha", iso := "cha", value := .categoriesPerWord6_7 }
  , { walsCode := "cku", iso := "wac", value := .categoriesPerWord10_11 }
  , { walsCode := "chk", iso := "ckt", value := .categoriesPerWord4_5 }
  , { walsCode := "cre", iso := "crk", value := .categoriesPerWord6_7 }
  , { walsCode := "dag", iso := "dgz", value := .categoriesPerWord8_9 }
  , { walsCode := "dni", iso := "dni", value := .categoriesPerWord6_7 }
  , { walsCode := "dig", iso := "mhu", value := .categoriesPerWord4_5 }
  , { walsCode := "eka", iso := "ekg", value := .categoriesPerWord4_5 }
  , { walsCode := "eng", iso := "eng", value := .categoriesPerWord2_3 }
  , { walsCode := "epe", iso := "sja", value := .categoriesPerWord4_5 }
  , { walsCode := "eve", iso := "evn", value := .categoriesPerWord6_7 }
  , { walsCode := "fij", iso := "fij", value := .categoriesPerWord6_7 }
  , { walsCode := "fin", iso := "fin", value := .categoriesPerWord2_3 }
  , { walsCode := "fre", iso := "fra", value := .categoriesPerWord4_5 }
  , { walsCode := "gar", iso := "grt", value := .categoriesPerWord2_3 }
  , { walsCode := "geo", iso := "kat", value := .categoriesPerWord8_9 }
  , { walsCode := "ger", iso := "deu", value := .categoriesPerWord2_3 }
  , { walsCode := "goo", iso := "gni", value := .categoriesPerWord6_7 }
  , { walsCode := "grb", iso := "grj", value := .categoriesPerWord6_7 }
  , { walsCode := "grk", iso := "ell", value := .categoriesPerWord4_5 }
  , { walsCode := "grw", iso := "kal", value := .categoriesPerWord4_5 }
  , { walsCode := "gua", iso := "gug", value := .categoriesPerWord4_5 }
  , { walsCode := "hai", iso := "hai", value := .categoriesPerWord8_9 }
  , { walsCode := "hat", iso := "had", value := .categoriesPerWord2_3 }
  , { walsCode := "hau", iso := "hau", value := .categoriesPerWord6_7 }
  , { walsCode := "heb", iso := "heb", value := .categoriesPerWord4_5 }
  , { walsCode := "hin", iso := "hin", value := .categoriesPerWord2_3 }
  , { walsCode := "hix", iso := "hix", value := .categoriesPerWord4_5 }
  , { walsCode := "hmo", iso := "hnj", value := .categoriesPerWord2_3 }
  , { walsCode := "hve", iso := "huv", value := .categoriesPerWord4_5 }
  , { walsCode := "hun", iso := "hun", value := .categoriesPerWord4_5 }
  , { walsCode := "hzb", iso := "huz", value := .categoriesPerWord6_7 }
  , { walsCode := "imo", iso := "imn", value := .categoriesPerWord10_11 }
  , { walsCode := "ind", iso := "ind", value := .categoriesPerWord4_5 }
  , { walsCode := "ing", iso := "inh", value := .categoriesPerWord10_11 }
  , { walsCode := "jak", iso := "jac", value := .categoriesPerWord4_5 }
  , { walsCode := "jpn", iso := "jpn", value := .categoriesPerWord4_5 }
  , { walsCode := "knd", iso := "kan", value := .categoriesPerWord2_3 }
  , { walsCode := "ksg", iso := "ksw", value := .categoriesPerWord2_3 }
  , { walsCode := "krk", iso := "kyh", value := .categoriesPerWord8_9 }
  , { walsCode := "kay", iso := "gyd", value := .categoriesPerWord4_5 }
  , { walsCode := "ket", iso := "ket", value := .categoriesPerWord2_3 }
  , { walsCode := "kew", iso := "kew", value := .categoriesPerWord6_7 }
  , { walsCode := "kha", iso := "khk", value := .categoriesPerWord2_3 }
  , { walsCode := "khs", iso := "kha", value := .categoriesPerWord4_5 }
  , { walsCode := "kio", iso := "kio", value := .categoriesPerWord8_9 }
  , { walsCode := "kis", iso := "kss", value := .categoriesPerWord2_3 }
  , { walsCode := "koa", iso := "cku", value := .categoriesPerWord12_13 }
  , { walsCode := "kor", iso := "kor", value := .categoriesPerWord6_7 }
  , { walsCode := "kch", iso := "khq", value := .categoriesPerWord2_3 }
  , { walsCode := "kro", iso := "kgo", value := .categoriesPerWord4_5 }
  , { walsCode := "kut", iso := "kut", value := .categoriesPerWord4_5 }
  , { walsCode := "lai", iso := "cnh", value := .categoriesPerWord8_9 }
  , { walsCode := "lkt", iso := "lkt", value := .categoriesPerWord10_11 }
  , { walsCode := "lan", iso := "laj", value := .categoriesPerWord6_7 }
  , { walsCode := "lav", iso := "lvk", value := .categoriesPerWord4_5 }
  , { walsCode := "lez", iso := "lez", value := .categoriesPerWord2_3 }
  , { walsCode := "luv", iso := "lue", value := .categoriesPerWord8_9 }
  , { walsCode := "maa", iso := "mas", value := .categoriesPerWord6_7 }
  , { walsCode := "mal", iso := "plt", value := .categoriesPerWord4_5 }
  , { walsCode := "mnd", iso := "cmn", value := .categoryPerWord0_1 }
  , { walsCode := "myi", iso := "mpc", value := .categoriesPerWord6_7 }
  , { walsCode := "map", iso := "arn", value := .categoriesPerWord8_9 }
  , { walsCode := "mar", iso := "mrc", value := .categoriesPerWord8_9 }
  , { walsCode := "mrt", iso := "vma", value := .categoriesPerWord2_3 }
  , { walsCode := "mau", iso := "mph", value := .categoriesPerWord4_5 }
  , { walsCode := "may", iso := "ayz", value := .categoryPerWord0_1 }
  , { walsCode := "mei", iso := "mni", value := .categoriesPerWord4_5 }
  , { walsCode := "mss", iso := "skd", value := .categoriesPerWord4_5 }
  , { walsCode := "mxc", iso := "mig", value := .categoriesPerWord4_5 }
  , { walsCode := "mun", iso := "unr", value := .categoriesPerWord6_7 }
  , { walsCode := "nah", iso := "nll", value := .categoryPerWord0_1 }
  , { walsCode := "kho", iso := "naq", value := .categoriesPerWord6_7 }
  , { walsCode := "nmb", iso := "nab", value := .categoriesPerWord8_9 }
  , { walsCode := "nan", iso := "niq", value := .categoriesPerWord4_5 }
  , { walsCode := "ntu", iso := "yrk", value := .categoriesPerWord2_3 }
  , { walsCode := "ngi", iso := "wyb", value := .categoriesPerWord4_5 }
  , { walsCode := "nca", iso := "caq", value := .categoriesPerWord6_7 }
  , { walsCode := "nsg", iso := "ncg", value := .categoriesPerWord4_5 }
  , { walsCode := "niv", iso := "niv", value := .categoriesPerWord8_9 }
  , { walsCode := "ond", iso := "one", value := .categoriesPerWord8_9 }
  , { walsCode := "orh", iso := "hae", value := .categoriesPerWord6_7 }
  , { walsCode := "otm", iso := "ote", value := .categoriesPerWord8_9 }
  , { walsCode := "pai", iso := "pwn", value := .categoriesPerWord4_5 }
  , { walsCode := "prs", iso := "pes", value := .categoriesPerWord4_5 }
  , { walsCode := "pip", iso := "ppl", value := .categoriesPerWord4_5 }
  , { walsCode := "prh", iso := "myp", value := .categoriesPerWord8_9 }
  , { walsCode := "pso", iso := "pom", value := .categoriesPerWord4_5 }
  , { walsCode := "qim", iso := "qvi", value := .categoriesPerWord8_9 }
  , { walsCode := "ram", iso := "rma", value := .categoriesPerWord2_3 }
  , { walsCode := "rap", iso := "rap", value := .categoriesPerWord8_9 }
  , { walsCode := "rus", iso := "rus", value := .categoriesPerWord4_5 }
  , { walsCode := "san", iso := "sag", value := .categoryPerWord0_1 }
  , { walsCode := "snm", iso := "xsu", value := .categoriesPerWord4_5 }
  , { walsCode := "shk", iso := "shp", value := .categoriesPerWord6_7 }
  , { walsCode := "sla", iso := "den", value := .categoriesPerWord8_9 }
  , { walsCode := "spa", iso := "spa", value := .categoriesPerWord4_5 }
  , { walsCode := "squ", iso := "squ", value := .categoriesPerWord8_9 }
  , { walsCode := "sup", iso := "spp", value := .categoriesPerWord2_3 }
  , { walsCode := "swa", iso := "swh", value := .categoriesPerWord4_5 }
  , { walsCode := "tag", iso := "tgl", value := .categoriesPerWord2_3 }
  , { walsCode := "tha", iso := "tha", value := .categoriesPerWord2_3 }
  , { walsCode := "tib", iso := "bod", value := .categoriesPerWord4_5 }
  , { walsCode := "tiw", iso := "tiw", value := .categoriesPerWord4_5 }
  , { walsCode := "tru", iso := "tpy", value := .categoriesPerWord8_9 }
  , { walsCode := "tuk", iso := "", value := .categoriesPerWord6_7 }
  , { walsCode := "tur", iso := "tur", value := .categoriesPerWord6_7 }
  , { walsCode := "vie", iso := "vie", value := .categoryPerWord0_1 }
  , { walsCode := "wra", iso := "wba", value := .categoriesPerWord4_5 }
  , { walsCode := "war", iso := "pav", value := .categoriesPerWord4_5 }
  , { walsCode := "wic", iso := "wic", value := .categoriesPerWord12_13 }
  , { walsCode := "wch", iso := "mzh", value := .categoriesPerWord2_3 }
  , { walsCode := "yag", iso := "yad", value := .categoriesPerWord10_11 }
  , { walsCode := "yaq", iso := "yaq", value := .categoriesPerWord4_5 }
  , { walsCode := "yor", iso := "yor", value := .categoriesPerWord6_7 }
  , { walsCode := "yur", iso := "yur", value := .categoriesPerWord6_7 }
  , { walsCode := "zqc", iso := "zoc", value := .categoriesPerWord6_7 }
  , { walsCode := "zul", iso := "zul", value := .categoriesPerWord4_5 }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F22A
