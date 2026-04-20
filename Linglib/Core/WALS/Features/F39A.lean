import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 39A: Inclusive/Exclusive Distinction in Independent Pronouns
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 39A`.

Chapter 39, 200 languages.
-/

namespace Core.WALS.F39A

/-- WALS 39A values. -/
inductive InclusiveExclusiveDistinctionInIndependentPronouns where
  /-- No 'we' (2 languages). -/
  | noWe
  /-- 'We' the same as 'I' (10 languages). -/
  | weTheSameAsI
  /-- No inclusive/exclusive (120 languages). -/
  | noInclusiveExclusive
  /-- Only inclusive (5 languages). -/
  | onlyInclusive
  /-- Inclusive/exclusive (63 languages). -/
  | inclusiveExclusive
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 39A dataset (200 languages). -/
def allData : List (Datapoint InclusiveExclusiveDistinctionInIndependentPronouns) :=
  [ { walsCode := "abi", iso := "axb", value := .noInclusiveExclusive }
  , { walsCode := "abk", iso := "abk", value := .inclusiveExclusive }
  , { walsCode := "aco", iso := "kjq", value := .noWe }
  , { walsCode := "ain", iso := "ain", value := .inclusiveExclusive }
  , { walsCode := "ala", iso := "amp", value := .noInclusiveExclusive }
  , { walsCode := "ame", iso := "aey", value := .noInclusiveExclusive }
  , { walsCode := "apu", iso := "apu", value := .noInclusiveExclusive }
  , { walsCode := "aeg", iso := "arz", value := .noInclusiveExclusive }
  , { walsCode := "ana", iso := "aro", value := .inclusiveExclusive }
  , { walsCode := "arp", iso := "ape", value := .noInclusiveExclusive }
  , { walsCode := "arm", iso := "hye", value := .noInclusiveExclusive }
  , { walsCode := "asm", iso := "cns", value := .noInclusiveExclusive }
  , { walsCode := "awp", iso := "kwi", value := .noInclusiveExclusive }
  , { walsCode := "aym", iso := "ayr", value := .onlyInclusive }
  , { walsCode := "bag", iso := "bmi", value := .noInclusiveExclusive }
  , { walsCode := "bam", iso := "bam", value := .noInclusiveExclusive }
  , { walsCode := "brs", iso := "bsn", value := .inclusiveExclusive }
  , { walsCode := "bsq", iso := "eus", value := .noInclusiveExclusive }
  , { walsCode := "bkr", iso := "btx", value := .inclusiveExclusive }
  , { walsCode := "baw", iso := "bgr", value := .noInclusiveExclusive }
  , { walsCode := "bej", iso := "bej", value := .noInclusiveExclusive }
  , { walsCode := "bma", iso := "tzm", value := .noInclusiveExclusive }
  , { walsCode := "brh", iso := "brh", value := .noInclusiveExclusive }
  , { walsCode := "bri", iso := "bzd", value := .inclusiveExclusive }
  , { walsCode := "brm", iso := "mya", value := .weTheSameAsI }
  , { walsCode := "bur", iso := "bsk", value := .noInclusiveExclusive }
  , { walsCode := "cah", iso := "chl", value := .noInclusiveExclusive }
  , { walsCode := "cnl", iso := "ram", value := .onlyInclusive }
  , { walsCode := "car", iso := "car", value := .inclusiveExclusive }
  , { walsCode := "cyv", iso := "cyb", value := .inclusiveExclusive }
  , { walsCode := "cha", iso := "cha", value := .inclusiveExclusive }
  , { walsCode := "cle", iso := "cle", value := .inclusiveExclusive }
  , { walsCode := "chk", iso := "ckt", value := .noInclusiveExclusive }
  , { walsCode := "cmn", iso := "com", value := .inclusiveExclusive }
  , { walsCode := "coo", iso := "csz", value := .inclusiveExclusive }
  , { walsCode := "cre", iso := "crk", value := .inclusiveExclusive }
  , { walsCode := "dag", iso := "dgz", value := .noInclusiveExclusive }
  , { walsCode := "dni", iso := "dni", value := .noInclusiveExclusive }
  , { walsCode := "dio", iso := "dyo", value := .inclusiveExclusive }
  , { walsCode := "dre", iso := "dhv", value := .inclusiveExclusive }
  , { walsCode := "eka", iso := "ekg", value := .noInclusiveExclusive }
  , { walsCode := "eng", iso := "eng", value := .noInclusiveExclusive }
  , { walsCode := "epe", iso := "sja", value := .noInclusiveExclusive }
  , { walsCode := "eve", iso := "evn", value := .inclusiveExclusive }
  , { walsCode := "ewe", iso := "ewe", value := .noInclusiveExclusive }
  , { walsCode := "fij", iso := "fij", value := .inclusiveExclusive }
  , { walsCode := "fin", iso := "fin", value := .noInclusiveExclusive }
  , { walsCode := "fre", iso := "fra", value := .noInclusiveExclusive }
  , { walsCode := "fur", iso := "fvr", value := .noInclusiveExclusive }
  , { walsCode := "gar", iso := "grt", value := .inclusiveExclusive }
  , { walsCode := "geo", iso := "kat", value := .noInclusiveExclusive }
  , { walsCode := "ger", iso := "deu", value := .noInclusiveExclusive }
  , { walsCode := "goo", iso := "gni", value := .inclusiveExclusive }
  , { walsCode := "grb", iso := "grj", value := .noInclusiveExclusive }
  , { walsCode := "grk", iso := "ell", value := .noInclusiveExclusive }
  , { walsCode := "grw", iso := "kal", value := .noInclusiveExclusive }
  , { walsCode := "gua", iso := "gug", value := .inclusiveExclusive }
  , { walsCode := "hai", iso := "hai", value := .noInclusiveExclusive }
  , { walsCode := "ham", iso := "hmt", value := .noInclusiveExclusive }
  , { walsCode := "hau", iso := "hau", value := .noInclusiveExclusive }
  , { walsCode := "heb", iso := "heb", value := .noInclusiveExclusive }
  , { walsCode := "hin", iso := "hin", value := .noInclusiveExclusive }
  , { walsCode := "hix", iso := "hix", value := .inclusiveExclusive }
  , { walsCode := "hmo", iso := "hnj", value := .noInclusiveExclusive }
  , { walsCode := "hum", iso := "huu", value := .noInclusiveExclusive }
  , { walsCode := "hun", iso := "hun", value := .noInclusiveExclusive }
  , { walsCode := "hzb", iso := "huz", value := .noInclusiveExclusive }
  , { walsCode := "igb", iso := "ibo", value := .noInclusiveExclusive }
  , { walsCode := "ika", iso := "arh", value := .noInclusiveExclusive }
  , { walsCode := "imo", iso := "imn", value := .onlyInclusive }
  , { walsCode := "ind", iso := "ind", value := .inclusiveExclusive }
  , { walsCode := "ing", iso := "inh", value := .inclusiveExclusive }
  , { walsCode := "irq", iso := "irk", value := .noInclusiveExclusive }
  , { walsCode := "iri", iso := "gle", value := .noInclusiveExclusive }
  , { walsCode := "jak", iso := "jac", value := .noInclusiveExclusive }
  , { walsCode := "jpn", iso := "jpn", value := .noInclusiveExclusive }
  , { walsCode := "juh", iso := "ktz", value := .inclusiveExclusive }
  , { walsCode := "knd", iso := "kan", value := .noInclusiveExclusive }
  , { walsCode := "knr", iso := "knc", value := .noInclusiveExclusive }
  , { walsCode := "krk", iso := "kyh", value := .noInclusiveExclusive }
  , { walsCode := "kyl", iso := "eky", value := .noInclusiveExclusive }
  , { walsCode := "kay", iso := "gyd", value := .inclusiveExclusive }
  , { walsCode := "ker", iso := "ker", value := .inclusiveExclusive }
  , { walsCode := "ket", iso := "ket", value := .noInclusiveExclusive }
  , { walsCode := "kew", iso := "kew", value := .noInclusiveExclusive }
  , { walsCode := "kha", iso := "khk", value := .noInclusiveExclusive }
  , { walsCode := "khs", iso := "kha", value := .noInclusiveExclusive }
  , { walsCode := "khm", iso := "khm", value := .noInclusiveExclusive }
  , { walsCode := "kmu", iso := "kjg", value := .noInclusiveExclusive }
  , { walsCode := "klv", iso := "kij", value := .inclusiveExclusive }
  , { walsCode := "kio", iso := "kio", value := .weTheSameAsI }
  , { walsCode := "krb", iso := "gil", value := .noInclusiveExclusive }
  , { walsCode := "koa", iso := "cku", value := .noInclusiveExclusive }
  , { walsCode := "kob", iso := "kpw", value := .noInclusiveExclusive }
  , { walsCode := "kon", iso := "kng", value := .noInclusiveExclusive }
  , { walsCode := "kor", iso := "kor", value := .noInclusiveExclusive }
  , { walsCode := "kfe", iso := "kfz", value := .noInclusiveExclusive }
  , { walsCode := "kse", iso := "ses", value := .noInclusiveExclusive }
  , { walsCode := "kro", iso := "kgo", value := .inclusiveExclusive }
  , { walsCode := "knm", iso := "kun", value := .inclusiveExclusive }
  , { walsCode := "kut", iso := "kut", value := .noInclusiveExclusive }
  , { walsCode := "lad", iso := "lbj", value := .inclusiveExclusive }
  , { walsCode := "lak", iso := "lbe", value := .noInclusiveExclusive }
  , { walsCode := "lkt", iso := "lkt", value := .noInclusiveExclusive }
  , { walsCode := "lan", iso := "laj", value := .noInclusiveExclusive }
  , { walsCode := "lat", iso := "lav", value := .noInclusiveExclusive }
  , { walsCode := "lav", iso := "lvk", value := .inclusiveExclusive }
  , { walsCode := "lep", iso := "lep", value := .noInclusiveExclusive }
  , { walsCode := "lez", iso := "lez", value := .noInclusiveExclusive }
  , { walsCode := "luv", iso := "lue", value := .noInclusiveExclusive }
  , { walsCode := "mab", iso := "mde", value := .noInclusiveExclusive }
  , { walsCode := "mak", iso := "myh", value := .noInclusiveExclusive }
  , { walsCode := "mal", iso := "plt", value := .inclusiveExclusive }
  , { walsCode := "mnd", iso := "cmn", value := .inclusiveExclusive }
  , { walsCode := "myi", iso := "mpc", value := .inclusiveExclusive }
  , { walsCode := "mao", iso := "mri", value := .inclusiveExclusive }
  , { walsCode := "map", iso := "arn", value := .weTheSameAsI }
  , { walsCode := "mku", iso := "zmr", value := .inclusiveExclusive }
  , { walsCode := "mar", iso := "mrc", value := .weTheSameAsI }
  , { walsCode := "mrd", iso := "mrz", value := .weTheSameAsI }
  , { walsCode := "mrt", iso := "vma", value := .inclusiveExclusive }
  , { walsCode := "mau", iso := "mph", value := .inclusiveExclusive }
  , { walsCode := "may", iso := "ayz", value := .noInclusiveExclusive }
  , { walsCode := "mei", iso := "mni", value := .noInclusiveExclusive }
  , { walsCode := "mss", iso := "skd", value := .inclusiveExclusive }
  , { walsCode := "mxc", iso := "mig", value := .onlyInclusive }
  , { walsCode := "mun", iso := "unr", value := .inclusiveExclusive }
  , { walsCode := "mrl", iso := "mur", value := .noInclusiveExclusive }
  , { walsCode := "nht", iso := "nhg", value := .noInclusiveExclusive }
  , { walsCode := "kho", iso := "naq", value := .inclusiveExclusive }
  , { walsCode := "nav", iso := "nav", value := .noInclusiveExclusive }
  , { walsCode := "ndy", iso := "djk", value := .noInclusiveExclusive }
  , { walsCode := "ntu", iso := "yrk", value := .noInclusiveExclusive }
  , { walsCode := "nez", iso := "nez", value := .noInclusiveExclusive }
  , { walsCode := "nti", iso := "niy", value := .inclusiveExclusive }
  , { walsCode := "ngi", iso := "wyb", value := .inclusiveExclusive }
  , { walsCode := "niv", iso := "niv", value := .inclusiveExclusive }
  , { walsCode := "nko", iso := "cgg", value := .noInclusiveExclusive }
  , { walsCode := "nbd", iso := "dgl", value := .noInclusiveExclusive }
  , { walsCode := "nug", iso := "nuy", value := .inclusiveExclusive }
  , { walsCode := "ond", iso := "one", value := .weTheSameAsI }
  , { walsCode := "orh", iso := "hae", value := .noInclusiveExclusive }
  , { walsCode := "oix", iso := "otz", value := .inclusiveExclusive }
  , { walsCode := "pms", iso := "pma", value := .inclusiveExclusive }
  , { walsCode := "pai", iso := "pwn", value := .inclusiveExclusive }
  , { walsCode := "psm", iso := "pqm", value := .inclusiveExclusive }
  , { walsCode := "pau", iso := "pad", value := .noInclusiveExclusive }
  , { walsCode := "prs", iso := "pes", value := .noInclusiveExclusive }
  , { walsCode := "prh", iso := "myp", value := .noWe }
  , { walsCode := "pit", iso := "pjt", value := .noInclusiveExclusive }
  , { walsCode := "pso", iso := "pom", value := .noInclusiveExclusive }
  , { walsCode := "qaw", iso := "alc", value := .weTheSameAsI }
  , { walsCode := "qim", iso := "qvi", value := .noInclusiveExclusive }
  , { walsCode := "ram", iso := "rma", value := .noInclusiveExclusive }
  , { walsCode := "rap", iso := "rap", value := .inclusiveExclusive }
  , { walsCode := "rus", iso := "rus", value := .noInclusiveExclusive }
  , { walsCode := "san", iso := "sag", value := .noInclusiveExclusive }
  , { walsCode := "snm", iso := "xsu", value := .inclusiveExclusive }
  , { walsCode := "sel", iso := "ona", value := .noInclusiveExclusive }
  , { walsCode := "sml", iso := "sza", value := .onlyInclusive }
  , { walsCode := "snt", iso := "set", value := .noInclusiveExclusive }
  , { walsCode := "shk", iso := "shp", value := .noInclusiveExclusive }
  , { walsCode := "sla", iso := "den", value := .noInclusiveExclusive }
  , { walsCode := "spa", iso := "spa", value := .noInclusiveExclusive }
  , { walsCode := "squ", iso := "squ", value := .noInclusiveExclusive }
  , { walsCode := "sue", iso := "sue", value := .inclusiveExclusive }
  , { walsCode := "sup", iso := "spp", value := .noInclusiveExclusive }
  , { walsCode := "swa", iso := "swh", value := .noInclusiveExclusive }
  , { walsCode := "tab", iso := "mky", value := .inclusiveExclusive }
  , { walsCode := "tag", iso := "tgl", value := .inclusiveExclusive }
  , { walsCode := "tha", iso := "tha", value := .weTheSameAsI }
  , { walsCode := "tiw", iso := "tiw", value := .inclusiveExclusive }
  , { walsCode := "tli", iso := "tli", value := .noInclusiveExclusive }
  , { walsCode := "tru", iso := "tpy", value := .weTheSameAsI }
  , { walsCode := "tsi", iso := "tsi", value := .noInclusiveExclusive }
  , { walsCode := "tuk", iso := "", value := .noInclusiveExclusive }
  , { walsCode := "tun", iso := "tun", value := .noInclusiveExclusive }
  , { walsCode := "tur", iso := "tur", value := .noInclusiveExclusive }
  , { walsCode := "una", iso := "mtg", value := .noInclusiveExclusive }
  , { walsCode := "ung", iso := "ung", value := .inclusiveExclusive }
  , { walsCode := "urk", iso := "urb", value := .noInclusiveExclusive }
  , { walsCode := "usa", iso := "wnu", value := .noInclusiveExclusive }
  , { walsCode := "vie", iso := "vie", value := .weTheSameAsI }
  , { walsCode := "wam", iso := "wmb", value := .inclusiveExclusive }
  , { walsCode := "wra", iso := "wba", value := .noInclusiveExclusive }
  , { walsCode := "wrd", iso := "wrr", value := .inclusiveExclusive }
  , { walsCode := "war", iso := "pav", value := .inclusiveExclusive }
  , { walsCode := "wic", iso := "wic", value := .inclusiveExclusive }
  , { walsCode := "wch", iso := "mzh", value := .noInclusiveExclusive }
  , { walsCode := "yag", iso := "yad", value := .inclusiveExclusive }
  , { walsCode := "yaq", iso := "yaq", value := .noInclusiveExclusive }
  , { walsCode := "yid", iso := "yii", value := .noInclusiveExclusive }
  , { walsCode := "yim", iso := "yee", value := .noInclusiveExclusive }
  , { walsCode := "yor", iso := "yor", value := .noInclusiveExclusive }
  , { walsCode := "yuc", iso := "yuc", value := .inclusiveExclusive }
  , { walsCode := "yko", iso := "yux", value := .noInclusiveExclusive }
  , { walsCode := "ypk", iso := "esu", value := .noInclusiveExclusive }
  , { walsCode := "yur", iso := "yur", value := .noInclusiveExclusive }
  , { walsCode := "zqc", iso := "zoc", value := .inclusiveExclusive }
  , { walsCode := "zul", iso := "zul", value := .noInclusiveExclusive }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F39A
