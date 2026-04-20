import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 79A: Suppletion According to Tense and Aspect
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 79A`.

Chapter 79, 193 languages.
-/

namespace Core.WALS.F79A

/-- WALS 79A values. -/
inductive SuppletionAccordingToTenseAndAspect where
  /-- Tense (36 languages). -/
  | tense
  /-- Aspect (10 languages). -/
  | aspect
  /-- Tense and aspect (24 languages). -/
  | tenseAndAspect
  /-- None (123 languages). -/
  | none
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 79A dataset (193 languages). -/
def allData : List (Datapoint SuppletionAccordingToTenseAndAspect) :=
  [ { walsCode := "xun", iso := "knw", value := .none }
  , { walsCode := "abk", iso := "abk", value := .tense }
  , { walsCode := "aco", iso := "kjq", value := .none }
  , { walsCode := "ain", iso := "ain", value := .none }
  , { walsCode := "agw", iso := "wbj", value := .none }
  , { walsCode := "ala", iso := "amp", value := .tense }
  , { walsCode := "ame", iso := "aey", value := .none }
  , { walsCode := "apu", iso := "apu", value := .none }
  , { walsCode := "abn", iso := "ard", value := .none }
  , { walsCode := "aeg", iso := "arz", value := .none }
  , { walsCode := "amr", iso := "ary", value := .none }
  , { walsCode := "atu", iso := "aeb", value := .none }
  , { walsCode := "ana", iso := "aro", value := .none }
  , { walsCode := "arp", iso := "ape", value := .none }
  , { walsCode := "arm", iso := "hye", value := .tenseAndAspect }
  , { walsCode := "asm", iso := "cns", value := .none }
  , { walsCode := "awp", iso := "kwi", value := .tense }
  , { walsCode := "aym", iso := "ayr", value := .none }
  , { walsCode := "bag", iso := "bmi", value := .none }
  , { walsCode := "brs", iso := "bsn", value := .none }
  , { walsCode := "bsq", iso := "eus", value := .tense }
  , { walsCode := "blr", iso := "bel", value := .tenseAndAspect }
  , { walsCode := "ben", iso := "ben", value := .tenseAndAspect }
  , { walsCode := "bma", iso := "tzm", value := .none }
  , { walsCode := "brh", iso := "brh", value := .tense }
  , { walsCode := "bul", iso := "bul", value := .tense }
  , { walsCode := "brm", iso := "mya", value := .none }
  , { walsCode := "bur", iso := "bsk", value := .tenseAndAspect }
  , { walsCode := "cah", iso := "chl", value := .none }
  , { walsCode := "cnl", iso := "ram", value := .none }
  , { walsCode := "cnt", iso := "yue", value := .none }
  , { walsCode := "car", iso := "car", value := .tense }
  , { walsCode := "cyv", iso := "cyb", value := .none }
  , { walsCode := "cha", iso := "cha", value := .tense }
  , { walsCode := "cle", iso := "cle", value := .aspect }
  , { walsCode := "chk", iso := "ckt", value := .none }
  , { walsCode := "cmn", iso := "com", value := .none }
  , { walsCode := "cre", iso := "crk", value := .none }
  , { walsCode := "cze", iso := "ces", value := .tenseAndAspect }
  , { walsCode := "dag", iso := "dgz", value := .none }
  , { walsCode := "dni", iso := "dni", value := .none }
  , { walsCode := "dio", iso := "dyo", value := .none }
  , { walsCode := "dut", iso := "nld", value := .tense }
  , { walsCode := "eng", iso := "eng", value := .tense }
  , { walsCode := "eve", iso := "evn", value := .none }
  , { walsCode := "ewe", iso := "ewe", value := .tense }
  , { walsCode := "fij", iso := "fij", value := .none }
  , { walsCode := "fin", iso := "fin", value := .none }
  , { walsCode := "fre", iso := "fra", value := .tenseAndAspect }
  , { walsCode := "fur", iso := "fvr", value := .tense }
  , { walsCode := "gar", iso := "grt", value := .none }
  , { walsCode := "grf", iso := "cab", value := .none }
  , { walsCode := "geo", iso := "kat", value := .tenseAndAspect }
  , { walsCode := "ger", iso := "deu", value := .tense }
  , { walsCode := "goo", iso := "gni", value := .none }
  , { walsCode := "grb", iso := "grj", value := .none }
  , { walsCode := "grk", iso := "ell", value := .tenseAndAspect }
  , { walsCode := "grw", iso := "kal", value := .none }
  , { walsCode := "gua", iso := "gug", value := .none }
  , { walsCode := "hau", iso := "hau", value := .none }
  , { walsCode := "heb", iso := "heb", value := .tense }
  , { walsCode := "hin", iso := "hin", value := .tenseAndAspect }
  , { walsCode := "hix", iso := "hix", value := .tense }
  , { walsCode := "hop", iso := "hop", value := .none }
  , { walsCode := "hun", iso := "hun", value := .tense }
  , { walsCode := "hzb", iso := "huz", value := .tense }
  , { walsCode := "hup", iso := "hup", value := .none }
  , { walsCode := "igb", iso := "ibo", value := .none }
  , { walsCode := "ika", iso := "arh", value := .aspect }
  , { walsCode := "imo", iso := "imn", value := .none }
  , { walsCode := "ind", iso := "ind", value := .none }
  , { walsCode := "ing", iso := "inh", value := .tenseAndAspect }
  , { walsCode := "irq", iso := "irk", value := .none }
  , { walsCode := "iri", iso := "gle", value := .tenseAndAspect }
  , { walsCode := "jak", iso := "jac", value := .none }
  , { walsCode := "jpn", iso := "jpn", value := .none }
  , { walsCode := "knd", iso := "kan", value := .tense }
  , { walsCode := "knr", iso := "knc", value := .tense }
  , { walsCode := "kay", iso := "gyd", value := .none }
  , { walsCode := "ket", iso := "ket", value := .none }
  , { walsCode := "kew", iso := "kew", value := .tense }
  , { walsCode := "kha", iso := "khk", value := .none }
  , { walsCode := "khs", iso := "kha", value := .none }
  , { walsCode := "khm", iso := "khm", value := .none }
  , { walsCode := "klv", iso := "kij", value := .none }
  , { walsCode := "kio", iso := "kio", value := .none }
  , { walsCode := "koa", iso := "cku", value := .none }
  , { walsCode := "kor", iso := "kor", value := .none }
  , { walsCode := "kse", iso := "ses", value := .none }
  , { walsCode := "kro", iso := "kgo", value := .none }
  , { walsCode := "knm", iso := "kun", value := .none }
  , { walsCode := "kuo", iso := "kto", value := .tense }
  , { walsCode := "kut", iso := "kut", value := .none }
  , { walsCode := "lad", iso := "lbj", value := .none }
  , { walsCode := "lkt", iso := "lkt", value := .none }
  , { walsCode := "lan", iso := "laj", value := .none }
  , { walsCode := "lat", iso := "lav", value := .tense }
  , { walsCode := "lav", iso := "lvk", value := .none }
  , { walsCode := "lez", iso := "lez", value := .tenseAndAspect }
  , { walsCode := "luv", iso := "lue", value := .none }
  , { walsCode := "mcd", iso := "mkd", value := .tense }
  , { walsCode := "mac", iso := "mbc", value := .tense }
  , { walsCode := "mak", iso := "myh", value := .none }
  , { walsCode := "mal", iso := "plt", value := .none }
  , { walsCode := "mlt", iso := "mlt", value := .none }
  , { walsCode := "mnd", iso := "cmn", value := .none }
  , { walsCode := "myi", iso := "mpc", value := .none }
  , { walsCode := "maw", iso := "mlq", value := .none }
  , { walsCode := "mao", iso := "mri", value := .none }
  , { walsCode := "map", iso := "arn", value := .none }
  , { walsCode := "mra", iso := "mec", value := .aspect }
  , { walsCode := "mku", iso := "zmr", value := .none }
  , { walsCode := "mar", iso := "mrc", value := .none }
  , { walsCode := "mrt", iso := "vma", value := .none }
  , { walsCode := "mau", iso := "mph", value := .tense }
  , { walsCode := "may", iso := "ayz", value := .none }
  , { walsCode := "mei", iso := "mni", value := .none }
  , { walsCode := "mss", iso := "skd", value := .none }
  , { walsCode := "mxc", iso := "mig", value := .aspect }
  , { walsCode := "mok", iso := "mkj", value := .none }
  , { walsCode := "mun", iso := "unr", value := .tense }
  , { walsCode := "mup", iso := "sur", value := .none }
  , { walsCode := "mrl", iso := "mur", value := .none }
  , { walsCode := "nht", iso := "nhg", value := .tenseAndAspect }
  , { walsCode := "kho", iso := "naq", value := .tense }
  , { walsCode := "nav", iso := "nav", value := .none }
  , { walsCode := "ndy", iso := "djk", value := .none }
  , { walsCode := "ntu", iso := "yrk", value := .none }
  , { walsCode := "ngi", iso := "wyb", value := .none }
  , { walsCode := "niv", iso := "niv", value := .none }
  , { walsCode := "nug", iso := "nuy", value := .aspect }
  , { walsCode := "ond", iso := "one", value := .aspect }
  , { walsCode := "orb", iso := "gax", value := .none }
  , { walsCode := "orh", iso := "hae", value := .tense }
  , { walsCode := "oix", iso := "otz", value := .aspect }
  , { walsCode := "psh", iso := "pst", value := .tenseAndAspect }
  , { walsCode := "psm", iso := "pqm", value := .none }
  , { walsCode := "prs", iso := "pes", value := .tenseAndAspect }
  , { walsCode := "pip", iso := "ppl", value := .tense }
  , { walsCode := "prh", iso := "myp", value := .none }
  , { walsCode := "pol", iso := "pol", value := .tenseAndAspect }
  , { walsCode := "pme", iso := "peb", value := .none }
  , { walsCode := "qaw", iso := "alc", value := .none }
  , { walsCode := "qim", iso := "qvi", value := .none }
  , { walsCode := "ram", iso := "rma", value := .none }
  , { walsCode := "rap", iso := "rap", value := .none }
  , { walsCode := "rus", iso := "rus", value := .tenseAndAspect }
  , { walsCode := "sam", iso := "smo", value := .none }
  , { walsCode := "san", iso := "sag", value := .none }
  , { walsCode := "snm", iso := "xsu", value := .none }
  , { walsCode := "sel", iso := "ona", value := .none }
  , { walsCode := "sml", iso := "sza", value := .none }
  , { walsCode := "snc", iso := "see", value := .none }
  , { walsCode := "snt", iso := "set", value := .none }
  , { walsCode := "scr", iso := "hbs", value := .tenseAndAspect }
  , { walsCode := "ses", iso := "sot", value := .none }
  , { walsCode := "shk", iso := "shp", value := .none }
  , { walsCode := "sla", iso := "den", value := .aspect }
  , { walsCode := "svk", iso := "slk", value := .tenseAndAspect }
  , { walsCode := "slo", iso := "slv", value := .tenseAndAspect }
  , { walsCode := "sou", iso := "hsb", value := .tenseAndAspect }
  , { walsCode := "spa", iso := "spa", value := .tenseAndAspect }
  , { walsCode := "squ", iso := "squ", value := .none }
  , { walsCode := "sue", iso := "sue", value := .tense }
  , { walsCode := "sup", iso := "spp", value := .tenseAndAspect }
  , { walsCode := "swa", iso := "swh", value := .none }
  , { walsCode := "swe", iso := "swe", value := .tense }
  , { walsCode := "tab", iso := "mky", value := .none }
  , { walsCode := "tag", iso := "tgl", value := .none }
  , { walsCode := "tpn", iso := "ntp", value := .aspect }
  , { walsCode := "tha", iso := "tha", value := .none }
  , { walsCode := "tiw", iso := "tiw", value := .none }
  , { walsCode := "tru", iso := "tpy", value := .none }
  , { walsCode := "tuk", iso := "", value := .tense }
  , { walsCode := "tna", iso := "tuv", value := .tense }
  , { walsCode := "tur", iso := "tur", value := .tense }
  , { walsCode := "ukr", iso := "ukr", value := .tenseAndAspect }
  , { walsCode := "usa", iso := "wnu", value := .tense }
  , { walsCode := "ute", iso := "ute", value := .none }
  , { walsCode := "vie", iso := "vie", value := .none }
  , { walsCode := "wra", iso := "wba", value := .none }
  , { walsCode := "war", iso := "pav", value := .none }
  , { walsCode := "wic", iso := "wic", value := .aspect }
  , { walsCode := "wch", iso := "mzh", value := .none }
  , { walsCode := "wly", iso := "wal", value := .none }
  , { walsCode := "yag", iso := "yad", value := .none }
  , { walsCode := "yaq", iso := "yaq", value := .none }
  , { walsCode := "yim", iso := "yee", value := .tense }
  , { walsCode := "yor", iso := "yor", value := .none }
  , { walsCode := "yko", iso := "yux", value := .none }
  , { walsCode := "ypk", iso := "esu", value := .none }
  , { walsCode := "zul", iso := "zul", value := .none }
  , { walsCode := "zun", iso := "zun", value := .none }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F79A
