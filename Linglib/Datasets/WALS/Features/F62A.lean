import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 62A: Action Nominal Constructions
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 62A`.

Chapter 62, 168 languages.
-/

namespace Datasets.WALS.F62A

/-- WALS 62A values. -/
inductive ActionNominalConstructions where
  /-- Sentential (25 languages). -/
  | sentential
  /-- Possessive-Accusative (29 languages). -/
  | possessiveAccusative
  /-- Ergative-Possessive (21 languages). -/
  | ergativePossessive
  /-- Double-Possessive (7 languages). -/
  | doublePossessive
  /-- Other (6 languages). -/
  | other
  /-- Mixed (14 languages). -/
  | mixed
  /-- Restricted (24 languages). -/
  | restricted
  /-- No action nominals (42 languages). -/
  | noActionNominals
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 62A dataset (168 languages). -/
def allData : List (Datapoint ActionNominalConstructions) :=
  [ { walsCode := "xun", iso := "knw", value := .restricted }
  , { walsCode := "abk", iso := "abk", value := .ergativePossessive }
  , { walsCode := "agl", iso := "agx", value := .mixed }
  , { walsCode := "axv", iso := "akv", value := .sentential }
  , { walsCode := "ala", iso := "amp", value := .noActionNominals }
  , { walsCode := "alb", iso := "sqi", value := .ergativePossessive }
  , { walsCode := "ame", iso := "aey", value := .possessiveAccusative }
  , { walsCode := "amh", iso := "amh", value := .possessiveAccusative }
  , { walsCode := "apl", iso := "apy", value := .ergativePossessive }
  , { walsCode := "apu", iso := "apu", value := .sentential }
  , { walsCode := "aeg", iso := "arz", value := .mixed }
  , { walsCode := "arp", iso := "ape", value := .noActionNominals }
  , { walsCode := "arc", iso := "aqc", value := .sentential }
  , { walsCode := "arm", iso := "hye", value := .possessiveAccusative }
  , { walsCode := "ava", iso := "ava", value := .sentential }
  , { walsCode := "awp", iso := "kwi", value := .noActionNominals }
  , { walsCode := "bam", iso := "bam", value := .doublePossessive }
  , { walsCode := "brs", iso := "bsn", value := .sentential }
  , { walsCode := "bsq", iso := "eus", value := .sentential }
  , { walsCode := "bez", iso := "kap", value := .sentential }
  , { walsCode := "bul", iso := "bul", value := .ergativePossessive }
  , { walsCode := "but", iso := "bxm", value := .possessiveAccusative }
  , { walsCode := "brm", iso := "mya", value := .other }
  , { walsCode := "bur", iso := "bsk", value := .sentential }
  , { walsCode := "bet", iso := "bev", value := .restricted }
  , { walsCode := "cnl", iso := "ram", value := .sentential }
  , { walsCode := "cnt", iso := "yue", value := .noActionNominals }
  , { walsCode := "car", iso := "car", value := .ergativePossessive }
  , { walsCode := "crj", iso := "cbd", value := .ergativePossessive }
  , { walsCode := "chm", iso := "cji", value := .sentential }
  , { walsCode := "cha", iso := "cha", value := .other }
  , { walsCode := "chk", iso := "ckt", value := .restricted }
  , { walsCode := "cre", iso := "crk", value := .restricted }
  , { walsCode := "dan", iso := "dnj", value := .doublePossessive }
  , { walsCode := "die", iso := "dih", value := .noActionNominals }
  , { walsCode := "dut", iso := "nld", value := .ergativePossessive }
  , { walsCode := "eng", iso := "eng", value := .mixed }
  , { walsCode := "est", iso := "ekk", value := .mixed }
  , { walsCode := "eve", iso := "evn", value := .possessiveAccusative }
  , { walsCode := "ewe", iso := "ewe", value := .restricted }
  , { walsCode := "fin", iso := "fin", value := .doublePossessive }
  , { walsCode := "for", iso := "for", value := .noActionNominals }
  , { walsCode := "fre", iso := "fra", value := .ergativePossessive }
  , { walsCode := "fni", iso := "fuv", value := .restricted }
  , { walsCode := "gag", iso := "gag", value := .noActionNominals }
  , { walsCode := "geo", iso := "kat", value := .ergativePossessive }
  , { walsCode := "ger", iso := "deu", value := .ergativePossessive }
  , { walsCode := "god", iso := "gdo", value := .sentential }
  , { walsCode := "goo", iso := "gni", value := .noActionNominals }
  , { walsCode := "grk", iso := "ell", value := .ergativePossessive }
  , { walsCode := "grw", iso := "kal", value := .restricted }
  , { walsCode := "gua", iso := "gug", value := .restricted }
  , { walsCode := "hau", iso := "hau", value := .restricted }
  , { walsCode := "heb", iso := "heb", value := .mixed }
  , { walsCode := "hin", iso := "hin", value := .possessiveAccusative }
  , { walsCode := "hix", iso := "hix", value := .ergativePossessive }
  , { walsCode := "hmo", iso := "hnj", value := .noActionNominals }
  , { walsCode := "hua", iso := "ygr", value := .noActionNominals }
  , { walsCode := "hlp", iso := "yuf", value := .noActionNominals }
  , { walsCode := "hun", iso := "hun", value := .restricted }
  , { walsCode := "ice", iso := "isl", value := .other }
  , { walsCode := "ika", iso := "arh", value := .noActionNominals }
  , { walsCode := "imo", iso := "imn", value := .noActionNominals }
  , { walsCode := "ind", iso := "ind", value := .ergativePossessive }
  , { walsCode := "ing", iso := "inh", value := .sentential }
  , { walsCode := "iql", iso := "ike", value := .restricted }
  , { walsCode := "irq", iso := "irk", value := .restricted }
  , { walsCode := "iri", iso := "gle", value := .mixed }
  , { walsCode := "jpn", iso := "jpn", value := .doublePossessive }
  , { walsCode := "kbl", iso := "kab", value := .ergativePossessive }
  , { walsCode := "knd", iso := "kan", value := .mixed }
  , { walsCode := "knr", iso := "knc", value := .mixed }
  , { walsCode := "kyl", iso := "eky", value := .noActionNominals }
  , { walsCode := "kay", iso := "gyd", value := .noActionNominals }
  , { walsCode := "ket", iso := "ket", value := .restricted }
  , { walsCode := "kha", iso := "khk", value := .possessiveAccusative }
  , { walsCode := "kmu", iso := "kjg", value := .restricted }
  , { walsCode := "klv", iso := "kij", value := .noActionNominals }
  , { walsCode := "kio", iso := "kio", value := .restricted }
  , { walsCode := "kob", iso := "kpw", value := .sentential }
  , { walsCode := "kor", iso := "kor", value := .sentential }
  , { walsCode := "kfe", iso := "kfz", value := .restricted }
  , { walsCode := "kse", iso := "ses", value := .restricted }
  , { walsCode := "kro", iso := "kgo", value := .possessiveAccusative }
  , { walsCode := "kuo", iso := "kto", value := .restricted }
  , { walsCode := "kji", iso := "kmr", value := .ergativePossessive }
  , { walsCode := "kut", iso := "kut", value := .noActionNominals }
  , { walsCode := "lak", iso := "lbe", value := .sentential }
  , { walsCode := "lkt", iso := "lkt", value := .noActionNominals }
  , { walsCode := "lan", iso := "laj", value := .possessiveAccusative }
  , { walsCode := "lat", iso := "lav", value := .doublePossessive }
  , { walsCode := "lav", iso := "lvk", value := .sentential }
  , { walsCode := "lel", iso := "lln", value := .mixed }
  , { walsCode := "lez", iso := "lez", value := .sentential }
  , { walsCode := "lnd", iso := "liy", value := .possessiveAccusative }
  , { walsCode := "luv", iso := "lue", value := .possessiveAccusative }
  , { walsCode := "mak", iso := "myh", value := .noActionNominals }
  , { walsCode := "mlt", iso := "mlt", value := .doublePossessive }
  , { walsCode := "mnd", iso := "cmn", value := .noActionNominals }
  , { walsCode := "myi", iso := "mpc", value := .noActionNominals }
  , { walsCode := "mao", iso := "mri", value := .mixed }
  , { walsCode := "map", iso := "arn", value := .possessiveAccusative }
  , { walsCode := "mme", iso := "mhr", value := .possessiveAccusative }
  , { walsCode := "mar", iso := "mrc", value := .possessiveAccusative }
  , { walsCode := "mrt", iso := "vma", value := .noActionNominals }
  , { walsCode := "mau", iso := "mph", value := .noActionNominals }
  , { walsCode := "may", iso := "ayz", value := .noActionNominals }
  , { walsCode := "mei", iso := "mni", value := .noActionNominals }
  , { walsCode := "mxc", iso := "mig", value := .noActionNominals }
  , { walsCode := "kho", iso := "naq", value := .noActionNominals }
  , { walsCode := "nmb", iso := "nab", value := .sentential }
  , { walsCode := "nav", iso := "nav", value := .noActionNominals }
  , { walsCode := "ntu", iso := "yrk", value := .possessiveAccusative }
  , { walsCode := "nep", iso := "npi", value := .sentential }
  , { walsCode := "nez", iso := "nez", value := .possessiveAccusative }
  , { walsCode := "ngi", iso := "wyb", value := .noActionNominals }
  , { walsCode := "niv", iso := "niv", value := .sentential }
  , { walsCode := "ond", iso := "one", value := .noActionNominals }
  , { walsCode := "orh", iso := "hae", value := .possessiveAccusative }
  , { walsCode := "pms", iso := "pma", value := .restricted }
  , { walsCode := "pan", iso := "pan", value := .possessiveAccusative }
  , { walsCode := "prs", iso := "pes", value := .ergativePossessive }
  , { walsCode := "prh", iso := "myp", value := .sentential }
  , { walsCode := "qim", iso := "qvi", value := .sentential }
  , { walsCode := "qch", iso := "quc", value := .restricted }
  , { walsCode := "ram", iso := "rma", value := .noActionNominals }
  , { walsCode := "rus", iso := "rus", value := .ergativePossessive }
  , { walsCode := "sam", iso := "smo", value := .other }
  , { walsCode := "san", iso := "sag", value := .possessiveAccusative }
  , { walsCode := "snm", iso := "xsu", value := .noActionNominals }
  , { walsCode := "skp", iso := "sel", value := .possessiveAccusative }
  , { walsCode := "sla", iso := "den", value := .noActionNominals }
  , { walsCode := "spa", iso := "spa", value := .ergativePossessive }
  , { walsCode := "squ", iso := "squ", value := .noActionNominals }
  , { walsCode := "sup", iso := "spp", value := .mixed }
  , { walsCode := "swa", iso := "swh", value := .possessiveAccusative }
  , { walsCode := "swe", iso := "swe", value := .other }
  , { walsCode := "tab", iso := "mky", value := .noActionNominals }
  , { walsCode := "tag", iso := "tgl", value := .possessiveAccusative }
  , { walsCode := "tml", iso := "tam", value := .sentential }
  , { walsCode := "tep", iso := "tpt", value := .restricted }
  , { walsCode := "tha", iso := "tha", value := .mixed }
  , { walsCode := "tid", iso := "tvo", value := .noActionNominals }
  , { walsCode := "tms", iso := "dto", value := .restricted }
  , { walsCode := "tru", iso := "tpy", value := .noActionNominals }
  , { walsCode := "tsa", iso := "tkr", value := .mixed }
  , { walsCode := "tuk", iso := "", value := .doublePossessive }
  , { walsCode := "tur", iso := "tur", value := .possessiveAccusative }
  , { walsCode := "tvl", iso := "tvl", value := .mixed }
  , { walsCode := "tuv", iso := "tyv", value := .possessiveAccusative }
  , { walsCode := "vat", iso := "dic", value := .possessiveAccusative }
  , { walsCode := "vie", iso := "vie", value := .possessiveAccusative }
  , { walsCode := "wai", iso := "waw", value := .ergativePossessive }
  , { walsCode := "wam", iso := "wmb", value := .noActionNominals }
  , { walsCode := "wra", iso := "wba", value := .other }
  , { walsCode := "war", iso := "pav", value := .noActionNominals }
  , { walsCode := "wrl", iso := "wbp", value := .noActionNominals }
  , { walsCode := "wyn", iso := "way", value := .ergativePossessive }
  , { walsCode := "wel", iso := "cym", value := .ergativePossessive }
  , { walsCode := "wic", iso := "wic", value := .noActionNominals }
  , { walsCode := "wch", iso := "mzh", value := .restricted }
  , { walsCode := "wik", iso := "yok", value := .possessiveAccusative }
  , { walsCode := "yag", iso := "yad", value := .sentential }
  , { walsCode := "yaq", iso := "yaq", value := .noActionNominals }
  , { walsCode := "yim", iso := "yee", value := .possessiveAccusative }
  , { walsCode := "yor", iso := "yor", value := .restricted }
  , { walsCode := "yko", iso := "yux", value := .possessiveAccusative }
  , { walsCode := "ysi", iso := "ysr", value := .sentential }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F62A
