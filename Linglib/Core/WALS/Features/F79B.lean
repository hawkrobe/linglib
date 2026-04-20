import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 79B: Suppletion in Imperatives and Hortatives
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 79B`.

Chapter 79, 193 languages.
-/

namespace Core.WALS.F79B

/-- WALS 79B values. -/
inductive SuppletionInImperativesAndHortatives where
  /-- A regular and a suppletive form alternate (8 languages). -/
  | aRegularAndASuppletiveFormAlternate
  /-- Imperative (29 languages). -/
  | imperative
  /-- Hortative (2 languages). -/
  | hortative
  /-- Imperative and Hortative (1 languages). -/
  | imperativeAndHortative
  /-- None (= no suppletive imperatives reported in the reference material) (153 languages). -/
  | none
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 79B dataset (193 languages). -/
def allData : List (Datapoint SuppletionInImperativesAndHortatives) :=
  [ { walsCode := "xun", iso := "knw", value := .imperative }
  , { walsCode := "abk", iso := "abk", value := .none }
  , { walsCode := "aco", iso := "kjq", value := .hortative }
  , { walsCode := "ain", iso := "ain", value := .none }
  , { walsCode := "agw", iso := "wbj", value := .imperativeAndHortative }
  , { walsCode := "ala", iso := "amp", value := .none }
  , { walsCode := "ame", iso := "aey", value := .none }
  , { walsCode := "apu", iso := "apu", value := .none }
  , { walsCode := "abn", iso := "ard", value := .none }
  , { walsCode := "aeg", iso := "arz", value := .imperative }
  , { walsCode := "amr", iso := "ary", value := .imperative }
  , { walsCode := "atu", iso := "aeb", value := .imperative }
  , { walsCode := "ana", iso := "aro", value := .none }
  , { walsCode := "arp", iso := "ape", value := .none }
  , { walsCode := "arm", iso := "hye", value := .imperative }
  , { walsCode := "asm", iso := "cns", value := .none }
  , { walsCode := "awp", iso := "kwi", value := .none }
  , { walsCode := "aym", iso := "ayr", value := .none }
  , { walsCode := "bag", iso := "bmi", value := .none }
  , { walsCode := "brs", iso := "bsn", value := .none }
  , { walsCode := "bsq", iso := "eus", value := .none }
  , { walsCode := "blr", iso := "bel", value := .none }
  , { walsCode := "ben", iso := "ben", value := .none }
  , { walsCode := "bma", iso := "tzm", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "brh", iso := "brh", value := .none }
  , { walsCode := "bul", iso := "bul", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "brm", iso := "mya", value := .none }
  , { walsCode := "bur", iso := "bsk", value := .none }
  , { walsCode := "cah", iso := "chl", value := .none }
  , { walsCode := "cnl", iso := "ram", value := .none }
  , { walsCode := "cnt", iso := "yue", value := .none }
  , { walsCode := "car", iso := "car", value := .imperative }
  , { walsCode := "cyv", iso := "cyb", value := .none }
  , { walsCode := "cha", iso := "cha", value := .none }
  , { walsCode := "cle", iso := "cle", value := .none }
  , { walsCode := "chk", iso := "ckt", value := .none }
  , { walsCode := "cmn", iso := "com", value := .none }
  , { walsCode := "cre", iso := "crk", value := .none }
  , { walsCode := "cze", iso := "ces", value := .none }
  , { walsCode := "dag", iso := "dgz", value := .none }
  , { walsCode := "dni", iso := "dni", value := .none }
  , { walsCode := "dio", iso := "dyo", value := .none }
  , { walsCode := "dut", iso := "nld", value := .none }
  , { walsCode := "eng", iso := "eng", value := .none }
  , { walsCode := "eve", iso := "evn", value := .none }
  , { walsCode := "ewe", iso := "ewe", value := .none }
  , { walsCode := "fij", iso := "fij", value := .none }
  , { walsCode := "fin", iso := "fin", value := .imperative }
  , { walsCode := "fre", iso := "fra", value := .none }
  , { walsCode := "fur", iso := "fvr", value := .none }
  , { walsCode := "gar", iso := "grt", value := .none }
  , { walsCode := "grf", iso := "cab", value := .none }
  , { walsCode := "geo", iso := "kat", value := .imperative }
  , { walsCode := "ger", iso := "deu", value := .none }
  , { walsCode := "goo", iso := "gni", value := .none }
  , { walsCode := "grb", iso := "grj", value := .none }
  , { walsCode := "grk", iso := "ell", value := .imperative }
  , { walsCode := "grw", iso := "kal", value := .none }
  , { walsCode := "gua", iso := "gug", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "hau", iso := "hau", value := .none }
  , { walsCode := "heb", iso := "heb", value := .none }
  , { walsCode := "hin", iso := "hin", value := .none }
  , { walsCode := "hix", iso := "hix", value := .none }
  , { walsCode := "hop", iso := "hop", value := .imperative }
  , { walsCode := "hun", iso := "hun", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "hzb", iso := "huz", value := .none }
  , { walsCode := "hup", iso := "hup", value := .none }
  , { walsCode := "igb", iso := "ibo", value := .none }
  , { walsCode := "ika", iso := "arh", value := .none }
  , { walsCode := "imo", iso := "imn", value := .none }
  , { walsCode := "ind", iso := "ind", value := .none }
  , { walsCode := "ing", iso := "inh", value := .imperative }
  , { walsCode := "irq", iso := "irk", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "iri", iso := "gle", value := .imperative }
  , { walsCode := "jak", iso := "jac", value := .imperative }
  , { walsCode := "jpn", iso := "jpn", value := .none }
  , { walsCode := "knd", iso := "kan", value := .none }
  , { walsCode := "knr", iso := "knc", value := .imperative }
  , { walsCode := "kay", iso := "gyd", value := .none }
  , { walsCode := "ket", iso := "ket", value := .none }
  , { walsCode := "kew", iso := "kew", value := .none }
  , { walsCode := "kha", iso := "khk", value := .none }
  , { walsCode := "khs", iso := "kha", value := .none }
  , { walsCode := "khm", iso := "khm", value := .none }
  , { walsCode := "klv", iso := "kij", value := .none }
  , { walsCode := "kio", iso := "kio", value := .none }
  , { walsCode := "koa", iso := "cku", value := .none }
  , { walsCode := "kor", iso := "kor", value := .none }
  , { walsCode := "kse", iso := "ses", value := .imperative }
  , { walsCode := "kro", iso := "kgo", value := .hortative }
  , { walsCode := "knm", iso := "kun", value := .imperative }
  , { walsCode := "kuo", iso := "kto", value := .none }
  , { walsCode := "kut", iso := "kut", value := .none }
  , { walsCode := "lad", iso := "lbj", value := .none }
  , { walsCode := "lkt", iso := "lkt", value := .none }
  , { walsCode := "lan", iso := "laj", value := .none }
  , { walsCode := "lat", iso := "lav", value := .none }
  , { walsCode := "lav", iso := "lvk", value := .none }
  , { walsCode := "lez", iso := "lez", value := .imperative }
  , { walsCode := "luv", iso := "lue", value := .imperative }
  , { walsCode := "mcd", iso := "mkd", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "mac", iso := "mbc", value := .none }
  , { walsCode := "mak", iso := "myh", value := .none }
  , { walsCode := "mal", iso := "plt", value := .none }
  , { walsCode := "mlt", iso := "mlt", value := .imperative }
  , { walsCode := "mnd", iso := "cmn", value := .none }
  , { walsCode := "myi", iso := "mpc", value := .none }
  , { walsCode := "maw", iso := "mlq", value := .none }
  , { walsCode := "mao", iso := "mri", value := .none }
  , { walsCode := "map", iso := "arn", value := .none }
  , { walsCode := "mra", iso := "mec", value := .none }
  , { walsCode := "mku", iso := "zmr", value := .none }
  , { walsCode := "mar", iso := "mrc", value := .none }
  , { walsCode := "mrt", iso := "vma", value := .none }
  , { walsCode := "mau", iso := "mph", value := .none }
  , { walsCode := "may", iso := "ayz", value := .none }
  , { walsCode := "mei", iso := "mni", value := .none }
  , { walsCode := "mss", iso := "skd", value := .none }
  , { walsCode := "mxc", iso := "mig", value := .imperative }
  , { walsCode := "mok", iso := "mkj", value := .none }
  , { walsCode := "mun", iso := "unr", value := .none }
  , { walsCode := "mup", iso := "sur", value := .none }
  , { walsCode := "mrl", iso := "mur", value := .imperative }
  , { walsCode := "nht", iso := "nhg", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "kho", iso := "naq", value := .none }
  , { walsCode := "nav", iso := "nav", value := .none }
  , { walsCode := "ndy", iso := "djk", value := .none }
  , { walsCode := "ntu", iso := "yrk", value := .imperative }
  , { walsCode := "ngi", iso := "wyb", value := .none }
  , { walsCode := "niv", iso := "niv", value := .none }
  , { walsCode := "nug", iso := "nuy", value := .none }
  , { walsCode := "ond", iso := "one", value := .none }
  , { walsCode := "orb", iso := "gax", value := .imperative }
  , { walsCode := "orh", iso := "hae", value := .imperative }
  , { walsCode := "oix", iso := "otz", value := .none }
  , { walsCode := "psh", iso := "pst", value := .none }
  , { walsCode := "psm", iso := "pqm", value := .none }
  , { walsCode := "prs", iso := "pes", value := .none }
  , { walsCode := "pip", iso := "ppl", value := .none }
  , { walsCode := "prh", iso := "myp", value := .none }
  , { walsCode := "pol", iso := "pol", value := .none }
  , { walsCode := "pme", iso := "peb", value := .none }
  , { walsCode := "qaw", iso := "alc", value := .none }
  , { walsCode := "qim", iso := "qvi", value := .none }
  , { walsCode := "ram", iso := "rma", value := .imperative }
  , { walsCode := "rap", iso := "rap", value := .none }
  , { walsCode := "rus", iso := "rus", value := .imperative }
  , { walsCode := "sam", iso := "smo", value := .none }
  , { walsCode := "san", iso := "sag", value := .none }
  , { walsCode := "snm", iso := "xsu", value := .none }
  , { walsCode := "sel", iso := "ona", value := .none }
  , { walsCode := "sml", iso := "sza", value := .none }
  , { walsCode := "snc", iso := "see", value := .none }
  , { walsCode := "snt", iso := "set", value := .none }
  , { walsCode := "scr", iso := "hbs", value := .aRegularAndASuppletiveFormAlternate }
  , { walsCode := "ses", iso := "sot", value := .none }
  , { walsCode := "shk", iso := "shp", value := .none }
  , { walsCode := "sla", iso := "den", value := .none }
  , { walsCode := "svk", iso := "slk", value := .none }
  , { walsCode := "slo", iso := "slv", value := .none }
  , { walsCode := "sou", iso := "hsb", value := .none }
  , { walsCode := "spa", iso := "spa", value := .imperative }
  , { walsCode := "squ", iso := "squ", value := .none }
  , { walsCode := "sue", iso := "sue", value := .none }
  , { walsCode := "sup", iso := "spp", value := .none }
  , { walsCode := "swa", iso := "swh", value := .imperative }
  , { walsCode := "swe", iso := "swe", value := .none }
  , { walsCode := "tab", iso := "mky", value := .none }
  , { walsCode := "tag", iso := "tgl", value := .none }
  , { walsCode := "tpn", iso := "ntp", value := .none }
  , { walsCode := "tha", iso := "tha", value := .none }
  , { walsCode := "tiw", iso := "tiw", value := .none }
  , { walsCode := "tru", iso := "tpy", value := .none }
  , { walsCode := "tuk", iso := "", value := .none }
  , { walsCode := "tna", iso := "tuv", value := .none }
  , { walsCode := "tur", iso := "tur", value := .none }
  , { walsCode := "ukr", iso := "ukr", value := .none }
  , { walsCode := "usa", iso := "wnu", value := .none }
  , { walsCode := "ute", iso := "ute", value := .none }
  , { walsCode := "vie", iso := "vie", value := .none }
  , { walsCode := "wra", iso := "wba", value := .none }
  , { walsCode := "war", iso := "pav", value := .none }
  , { walsCode := "wic", iso := "wic", value := .none }
  , { walsCode := "wch", iso := "mzh", value := .imperative }
  , { walsCode := "wly", iso := "wal", value := .none }
  , { walsCode := "yag", iso := "yad", value := .none }
  , { walsCode := "yaq", iso := "yaq", value := .none }
  , { walsCode := "yim", iso := "yee", value := .none }
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

end Core.WALS.F79B
