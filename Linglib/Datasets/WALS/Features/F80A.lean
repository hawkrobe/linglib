import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 80A: Verbal Number and Suppletion
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 80A`.

Chapter 80, 193 languages.
-/

namespace Datasets.WALS.F80A

/-- WALS 80A values. -/
inductive VerbalNumberAndSuppletion where
  /-- None (159 languages). -/
  | none
  /-- Singular-plural pairs, no suppletion (12 languages). -/
  | singularPluralPairsNoSuppletion
  /-- Singular-plural pairs, suppletion (15 languages). -/
  | singularPluralPairsSuppletion
  /-- Singular-dual-plural triples, no suppletion (5 languages). -/
  | singularDualPluralTriplesNoSuppletion
  /-- Singular-dual-plural triples, suppletion (2 languages). -/
  | singularDualPluralTriplesSuppletion
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 80A dataset (193 languages). -/
def allData : List (Datapoint VerbalNumberAndSuppletion) :=
  [ { walsCode := "xun", iso := "knw", value := .singularPluralPairsSuppletion }
  , { walsCode := "abk", iso := "abk", value := .none }
  , { walsCode := "aco", iso := "kjq", value := .none }
  , { walsCode := "ain", iso := "ain", value := .singularPluralPairsSuppletion }
  , { walsCode := "agw", iso := "wbj", value := .none }
  , { walsCode := "ala", iso := "amp", value := .none }
  , { walsCode := "ame", iso := "aey", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "apu", iso := "apu", value := .none }
  , { walsCode := "abn", iso := "ard", value := .none }
  , { walsCode := "aeg", iso := "arz", value := .none }
  , { walsCode := "amr", iso := "ary", value := .none }
  , { walsCode := "atu", iso := "aeb", value := .none }
  , { walsCode := "ana", iso := "aro", value := .none }
  , { walsCode := "arp", iso := "ape", value := .none }
  , { walsCode := "arm", iso := "hye", value := .none }
  , { walsCode := "asm", iso := "cns", value := .none }
  , { walsCode := "awp", iso := "kwi", value := .none }
  , { walsCode := "aym", iso := "ayr", value := .none }
  , { walsCode := "bag", iso := "bmi", value := .none }
  , { walsCode := "brs", iso := "bsn", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "bsq", iso := "eus", value := .none }
  , { walsCode := "blr", iso := "bel", value := .none }
  , { walsCode := "ben", iso := "ben", value := .none }
  , { walsCode := "bma", iso := "tzm", value := .none }
  , { walsCode := "brh", iso := "brh", value := .none }
  , { walsCode := "bul", iso := "bul", value := .none }
  , { walsCode := "brm", iso := "mya", value := .none }
  , { walsCode := "bur", iso := "bsk", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "cah", iso := "chl", value := .singularPluralPairsSuppletion }
  , { walsCode := "cnl", iso := "ram", value := .singularPluralPairsSuppletion }
  , { walsCode := "cnt", iso := "yue", value := .none }
  , { walsCode := "car", iso := "car", value := .none }
  , { walsCode := "cyv", iso := "cyb", value := .none }
  , { walsCode := "cha", iso := "cha", value := .none }
  , { walsCode := "cle", iso := "cle", value := .none }
  , { walsCode := "chk", iso := "ckt", value := .none }
  , { walsCode := "cmn", iso := "com", value := .singularPluralPairsNoSuppletion }
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
  , { walsCode := "fin", iso := "fin", value := .none }
  , { walsCode := "fre", iso := "fra", value := .none }
  , { walsCode := "fur", iso := "fvr", value := .none }
  , { walsCode := "gar", iso := "grt", value := .none }
  , { walsCode := "grf", iso := "cab", value := .none }
  , { walsCode := "geo", iso := "kat", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "ger", iso := "deu", value := .none }
  , { walsCode := "goo", iso := "gni", value := .none }
  , { walsCode := "grb", iso := "grj", value := .none }
  , { walsCode := "grk", iso := "ell", value := .none }
  , { walsCode := "grw", iso := "kal", value := .none }
  , { walsCode := "gua", iso := "gug", value := .none }
  , { walsCode := "hau", iso := "hau", value := .none }
  , { walsCode := "heb", iso := "heb", value := .none }
  , { walsCode := "hin", iso := "hin", value := .none }
  , { walsCode := "hix", iso := "hix", value := .none }
  , { walsCode := "hop", iso := "hop", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "hun", iso := "hun", value := .none }
  , { walsCode := "hzb", iso := "huz", value := .none }
  , { walsCode := "hup", iso := "hup", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "igb", iso := "ibo", value := .none }
  , { walsCode := "ika", iso := "arh", value := .none }
  , { walsCode := "imo", iso := "imn", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "ind", iso := "ind", value := .none }
  , { walsCode := "ing", iso := "inh", value := .singularPluralPairsSuppletion }
  , { walsCode := "irq", iso := "irk", value := .none }
  , { walsCode := "iri", iso := "gle", value := .none }
  , { walsCode := "jak", iso := "jac", value := .none }
  , { walsCode := "jpn", iso := "jpn", value := .none }
  , { walsCode := "knd", iso := "kan", value := .none }
  , { walsCode := "knr", iso := "knc", value := .none }
  , { walsCode := "kay", iso := "gyd", value := .none }
  , { walsCode := "ket", iso := "ket", value := .singularPluralPairsSuppletion }
  , { walsCode := "kew", iso := "kew", value := .none }
  , { walsCode := "kha", iso := "khk", value := .none }
  , { walsCode := "khs", iso := "kha", value := .none }
  , { walsCode := "khm", iso := "khm", value := .none }
  , { walsCode := "klv", iso := "kij", value := .none }
  , { walsCode := "kio", iso := "kio", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "koa", iso := "cku", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "kor", iso := "kor", value := .none }
  , { walsCode := "kse", iso := "ses", value := .none }
  , { walsCode := "kro", iso := "kgo", value := .singularPluralPairsSuppletion }
  , { walsCode := "knm", iso := "kun", value := .singularDualPluralTriplesSuppletion }
  , { walsCode := "kuo", iso := "kto", value := .none }
  , { walsCode := "kut", iso := "kut", value := .none }
  , { walsCode := "lad", iso := "lbj", value := .none }
  , { walsCode := "lkt", iso := "lkt", value := .none }
  , { walsCode := "lan", iso := "laj", value := .none }
  , { walsCode := "lat", iso := "lav", value := .none }
  , { walsCode := "lav", iso := "lvk", value := .none }
  , { walsCode := "lez", iso := "lez", value := .none }
  , { walsCode := "luv", iso := "lue", value := .none }
  , { walsCode := "mcd", iso := "mkd", value := .none }
  , { walsCode := "mac", iso := "mbc", value := .none }
  , { walsCode := "mak", iso := "myh", value := .none }
  , { walsCode := "mal", iso := "plt", value := .none }
  , { walsCode := "mlt", iso := "mlt", value := .none }
  , { walsCode := "mnd", iso := "cmn", value := .none }
  , { walsCode := "myi", iso := "mpc", value := .none }
  , { walsCode := "maw", iso := "mlq", value := .none }
  , { walsCode := "mao", iso := "mri", value := .none }
  , { walsCode := "map", iso := "arn", value := .none }
  , { walsCode := "mra", iso := "mec", value := .none }
  , { walsCode := "mku", iso := "zmr", value := .none }
  , { walsCode := "mar", iso := "mrc", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "mrt", iso := "vma", value := .none }
  , { walsCode := "mau", iso := "mph", value := .none }
  , { walsCode := "may", iso := "ayz", value := .none }
  , { walsCode := "mei", iso := "mni", value := .none }
  , { walsCode := "mss", iso := "skd", value := .none }
  , { walsCode := "mxc", iso := "mig", value := .none }
  , { walsCode := "mok", iso := "mkj", value := .none }
  , { walsCode := "mun", iso := "unr", value := .none }
  , { walsCode := "mup", iso := "sur", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "mrl", iso := "mur", value := .singularPluralPairsSuppletion }
  , { walsCode := "nht", iso := "nhg", value := .none }
  , { walsCode := "kho", iso := "naq", value := .none }
  , { walsCode := "nav", iso := "nav", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "ndy", iso := "djk", value := .none }
  , { walsCode := "ntu", iso := "yrk", value := .none }
  , { walsCode := "ngi", iso := "wyb", value := .none }
  , { walsCode := "niv", iso := "niv", value := .none }
  , { walsCode := "nug", iso := "nuy", value := .none }
  , { walsCode := "ond", iso := "one", value := .none }
  , { walsCode := "orb", iso := "gax", value := .none }
  , { walsCode := "orh", iso := "hae", value := .none }
  , { walsCode := "oix", iso := "otz", value := .none }
  , { walsCode := "psh", iso := "pst", value := .none }
  , { walsCode := "psm", iso := "pqm", value := .singularPluralPairsSuppletion }
  , { walsCode := "prs", iso := "pes", value := .none }
  , { walsCode := "pip", iso := "ppl", value := .none }
  , { walsCode := "prh", iso := "myp", value := .none }
  , { walsCode := "pol", iso := "pol", value := .none }
  , { walsCode := "pme", iso := "peb", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "qaw", iso := "alc", value := .none }
  , { walsCode := "qim", iso := "qvi", value := .none }
  , { walsCode := "ram", iso := "rma", value := .none }
  , { walsCode := "rap", iso := "rap", value := .none }
  , { walsCode := "rus", iso := "rus", value := .none }
  , { walsCode := "sam", iso := "smo", value := .singularPluralPairsSuppletion }
  , { walsCode := "san", iso := "sag", value := .none }
  , { walsCode := "snm", iso := "xsu", value := .none }
  , { walsCode := "sel", iso := "ona", value := .none }
  , { walsCode := "sml", iso := "sza", value := .none }
  , { walsCode := "snc", iso := "see", value := .none }
  , { walsCode := "snt", iso := "set", value := .none }
  , { walsCode := "scr", iso := "hbs", value := .none }
  , { walsCode := "ses", iso := "sot", value := .none }
  , { walsCode := "shk", iso := "shp", value := .singularPluralPairsSuppletion }
  , { walsCode := "sla", iso := "den", value := .singularDualPluralTriplesSuppletion }
  , { walsCode := "svk", iso := "slk", value := .none }
  , { walsCode := "slo", iso := "slv", value := .none }
  , { walsCode := "sou", iso := "hsb", value := .none }
  , { walsCode := "spa", iso := "spa", value := .none }
  , { walsCode := "squ", iso := "squ", value := .none }
  , { walsCode := "sue", iso := "sue", value := .none }
  , { walsCode := "sup", iso := "spp", value := .none }
  , { walsCode := "swa", iso := "swh", value := .none }
  , { walsCode := "swe", iso := "swe", value := .none }
  , { walsCode := "tab", iso := "mky", value := .none }
  , { walsCode := "tag", iso := "tgl", value := .none }
  , { walsCode := "tpn", iso := "ntp", value := .singularPluralPairsSuppletion }
  , { walsCode := "tha", iso := "tha", value := .none }
  , { walsCode := "tiw", iso := "tiw", value := .none }
  , { walsCode := "tru", iso := "tpy", value := .none }
  , { walsCode := "tuk", iso := "", value := .none }
  , { walsCode := "tna", iso := "tuv", value := .none }
  , { walsCode := "tur", iso := "tur", value := .none }
  , { walsCode := "ukr", iso := "ukr", value := .none }
  , { walsCode := "usa", iso := "wnu", value := .singularPluralPairsSuppletion }
  , { walsCode := "ute", iso := "ute", value := .singularPluralPairsSuppletion }
  , { walsCode := "vie", iso := "vie", value := .none }
  , { walsCode := "wra", iso := "wba", value := .none }
  , { walsCode := "war", iso := "pav", value := .singularPluralPairsSuppletion }
  , { walsCode := "wic", iso := "wic", value := .singularDualPluralTriplesNoSuppletion }
  , { walsCode := "wch", iso := "mzh", value := .none }
  , { walsCode := "wly", iso := "wal", value := .none }
  , { walsCode := "yag", iso := "yad", value := .none }
  , { walsCode := "yaq", iso := "yaq", value := .singularPluralPairsNoSuppletion }
  , { walsCode := "yim", iso := "yee", value := .none }
  , { walsCode := "yor", iso := "yor", value := .none }
  , { walsCode := "yko", iso := "yux", value := .none }
  , { walsCode := "ypk", iso := "esu", value := .none }
  , { walsCode := "zul", iso := "zul", value := .none }
  , { walsCode := "zun", iso := "zun", value := .singularPluralPairsNoSuppletion }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F80A
