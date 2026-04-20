import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 40A: Inclusive/Exclusive Distinction in Verbal Inflection
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 40A`.

Chapter 40, 200 languages.
-/

namespace Core.WALS.F40A

/-- WALS 40A values. -/
inductive InclusiveExclusiveDistinctionInVerbalInflection where
  /-- No person marking (70 languages). -/
  | noPersonMarking
  /-- 'We' the same as 'I' (12 languages). -/
  | weTheSameAsI
  /-- No inclusive/exclusive (79 languages). -/
  | noInclusiveExclusive
  /-- Only inclusive (9 languages). -/
  | onlyInclusive
  /-- Inclusive/exclusive (30 languages). -/
  | inclusiveExclusive
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 40A dataset (200 languages). -/
def allData : List (Datapoint InclusiveExclusiveDistinctionInVerbalInflection) :=
  [ { walsCode := "abi", iso := "axb", value := .weTheSameAsI }
  , { walsCode := "abk", iso := "abk", value := .noInclusiveExclusive }
  , { walsCode := "aco", iso := "kjq", value := .weTheSameAsI }
  , { walsCode := "ain", iso := "ain", value := .inclusiveExclusive }
  , { walsCode := "ala", iso := "amp", value := .noInclusiveExclusive }
  , { walsCode := "ame", iso := "aey", value := .noInclusiveExclusive }
  , { walsCode := "apu", iso := "apu", value := .noInclusiveExclusive }
  , { walsCode := "aeg", iso := "arz", value := .noInclusiveExclusive }
  , { walsCode := "ana", iso := "aro", value := .noPersonMarking }
  , { walsCode := "arp", iso := "ape", value := .noInclusiveExclusive }
  , { walsCode := "arm", iso := "hye", value := .noInclusiveExclusive }
  , { walsCode := "asm", iso := "cns", value := .noInclusiveExclusive }
  , { walsCode := "awp", iso := "kwi", value := .weTheSameAsI }
  , { walsCode := "aym", iso := "ayr", value := .onlyInclusive }
  , { walsCode := "bag", iso := "bmi", value := .noPersonMarking }
  , { walsCode := "bam", iso := "bam", value := .noPersonMarking }
  , { walsCode := "brs", iso := "bsn", value := .noPersonMarking }
  , { walsCode := "bsq", iso := "eus", value := .noInclusiveExclusive }
  , { walsCode := "bkr", iso := "btx", value := .noPersonMarking }
  , { walsCode := "baw", iso := "bgr", value := .noPersonMarking }
  , { walsCode := "bej", iso := "bej", value := .noInclusiveExclusive }
  , { walsCode := "bma", iso := "tzm", value := .noInclusiveExclusive }
  , { walsCode := "brh", iso := "brh", value := .noInclusiveExclusive }
  , { walsCode := "bri", iso := "bzd", value := .noPersonMarking }
  , { walsCode := "brm", iso := "mya", value := .noPersonMarking }
  , { walsCode := "bur", iso := "bsk", value := .noInclusiveExclusive }
  , { walsCode := "cah", iso := "chl", value := .noInclusiveExclusive }
  , { walsCode := "cnl", iso := "ram", value := .onlyInclusive }
  , { walsCode := "car", iso := "car", value := .onlyInclusive }
  , { walsCode := "cyv", iso := "cyb", value := .inclusiveExclusive }
  , { walsCode := "cha", iso := "cha", value := .noPersonMarking }
  , { walsCode := "cle", iso := "cle", value := .noInclusiveExclusive }
  , { walsCode := "chk", iso := "ckt", value := .noInclusiveExclusive }
  , { walsCode := "cmn", iso := "com", value := .noPersonMarking }
  , { walsCode := "coo", iso := "csz", value := .inclusiveExclusive }
  , { walsCode := "cre", iso := "crk", value := .onlyInclusive }
  , { walsCode := "dag", iso := "dgz", value := .weTheSameAsI }
  , { walsCode := "dni", iso := "dni", value := .noInclusiveExclusive }
  , { walsCode := "dio", iso := "dyo", value := .inclusiveExclusive }
  , { walsCode := "dre", iso := "dhv", value := .noPersonMarking }
  , { walsCode := "eka", iso := "ekg", value := .noInclusiveExclusive }
  , { walsCode := "eng", iso := "eng", value := .weTheSameAsI }
  , { walsCode := "epe", iso := "sja", value := .noPersonMarking }
  , { walsCode := "eve", iso := "evn", value := .inclusiveExclusive }
  , { walsCode := "ewe", iso := "ewe", value := .noPersonMarking }
  , { walsCode := "fij", iso := "fij", value := .noPersonMarking }
  , { walsCode := "fin", iso := "fin", value := .noInclusiveExclusive }
  , { walsCode := "fre", iso := "fra", value := .noInclusiveExclusive }
  , { walsCode := "fur", iso := "fvr", value := .noInclusiveExclusive }
  , { walsCode := "gar", iso := "grt", value := .noPersonMarking }
  , { walsCode := "geo", iso := "kat", value := .weTheSameAsI }
  , { walsCode := "ger", iso := "deu", value := .noInclusiveExclusive }
  , { walsCode := "goo", iso := "gni", value := .inclusiveExclusive }
  , { walsCode := "grb", iso := "grj", value := .noPersonMarking }
  , { walsCode := "grk", iso := "ell", value := .noInclusiveExclusive }
  , { walsCode := "grw", iso := "kal", value := .noInclusiveExclusive }
  , { walsCode := "gua", iso := "gug", value := .inclusiveExclusive }
  , { walsCode := "hai", iso := "hai", value := .noPersonMarking }
  , { walsCode := "ham", iso := "hmt", value := .noInclusiveExclusive }
  , { walsCode := "hau", iso := "hau", value := .noPersonMarking }
  , { walsCode := "heb", iso := "heb", value := .noInclusiveExclusive }
  , { walsCode := "hin", iso := "hin", value := .noPersonMarking }
  , { walsCode := "hix", iso := "hix", value := .inclusiveExclusive }
  , { walsCode := "hmo", iso := "hnj", value := .noPersonMarking }
  , { walsCode := "hum", iso := "huu", value := .noInclusiveExclusive }
  , { walsCode := "hun", iso := "hun", value := .noInclusiveExclusive }
  , { walsCode := "hzb", iso := "huz", value := .noPersonMarking }
  , { walsCode := "igb", iso := "ibo", value := .noPersonMarking }
  , { walsCode := "ika", iso := "arh", value := .noInclusiveExclusive }
  , { walsCode := "imo", iso := "imn", value := .noPersonMarking }
  , { walsCode := "ind", iso := "ind", value := .noPersonMarking }
  , { walsCode := "ing", iso := "inh", value := .noPersonMarking }
  , { walsCode := "irq", iso := "irk", value := .noInclusiveExclusive }
  , { walsCode := "iri", iso := "gle", value := .noInclusiveExclusive }
  , { walsCode := "jak", iso := "jac", value := .noInclusiveExclusive }
  , { walsCode := "jpn", iso := "jpn", value := .noPersonMarking }
  , { walsCode := "juh", iso := "ktz", value := .noPersonMarking }
  , { walsCode := "knd", iso := "kan", value := .noInclusiveExclusive }
  , { walsCode := "knr", iso := "knc", value := .noInclusiveExclusive }
  , { walsCode := "krk", iso := "kyh", value := .noInclusiveExclusive }
  , { walsCode := "kyl", iso := "eky", value := .noPersonMarking }
  , { walsCode := "kay", iso := "gyd", value := .noPersonMarking }
  , { walsCode := "ker", iso := "ker", value := .noPersonMarking }
  , { walsCode := "ket", iso := "ket", value := .noInclusiveExclusive }
  , { walsCode := "kew", iso := "kew", value := .noInclusiveExclusive }
  , { walsCode := "kha", iso := "khk", value := .noPersonMarking }
  , { walsCode := "khs", iso := "kha", value := .noPersonMarking }
  , { walsCode := "khm", iso := "khm", value := .noPersonMarking }
  , { walsCode := "kmu", iso := "kjg", value := .noPersonMarking }
  , { walsCode := "klv", iso := "kij", value := .inclusiveExclusive }
  , { walsCode := "kio", iso := "kio", value := .inclusiveExclusive }
  , { walsCode := "krb", iso := "gil", value := .noPersonMarking }
  , { walsCode := "koa", iso := "cku", value := .noInclusiveExclusive }
  , { walsCode := "kob", iso := "kpw", value := .noInclusiveExclusive }
  , { walsCode := "kon", iso := "kng", value := .noInclusiveExclusive }
  , { walsCode := "kor", iso := "kor", value := .noPersonMarking }
  , { walsCode := "kfe", iso := "kfz", value := .noPersonMarking }
  , { walsCode := "kse", iso := "ses", value := .noPersonMarking }
  , { walsCode := "kro", iso := "kgo", value := .inclusiveExclusive }
  , { walsCode := "knm", iso := "kun", value := .inclusiveExclusive }
  , { walsCode := "kut", iso := "kut", value := .weTheSameAsI }
  , { walsCode := "lad", iso := "lbj", value := .noPersonMarking }
  , { walsCode := "lak", iso := "lbe", value := .noInclusiveExclusive }
  , { walsCode := "lkt", iso := "lkt", value := .noInclusiveExclusive }
  , { walsCode := "lan", iso := "laj", value := .noInclusiveExclusive }
  , { walsCode := "lat", iso := "lav", value := .noInclusiveExclusive }
  , { walsCode := "lav", iso := "lvk", value := .inclusiveExclusive }
  , { walsCode := "lep", iso := "lep", value := .noPersonMarking }
  , { walsCode := "lez", iso := "lez", value := .noPersonMarking }
  , { walsCode := "luv", iso := "lue", value := .noInclusiveExclusive }
  , { walsCode := "mab", iso := "mde", value := .noInclusiveExclusive }
  , { walsCode := "mak", iso := "myh", value := .noInclusiveExclusive }
  , { walsCode := "mal", iso := "plt", value := .noPersonMarking }
  , { walsCode := "mnd", iso := "cmn", value := .noPersonMarking }
  , { walsCode := "myi", iso := "mpc", value := .inclusiveExclusive }
  , { walsCode := "mao", iso := "mri", value := .noPersonMarking }
  , { walsCode := "map", iso := "arn", value := .noInclusiveExclusive }
  , { walsCode := "mku", iso := "zmr", value := .inclusiveExclusive }
  , { walsCode := "mar", iso := "mrc", value := .weTheSameAsI }
  , { walsCode := "mrd", iso := "mrz", value := .noInclusiveExclusive }
  , { walsCode := "mrt", iso := "vma", value := .noPersonMarking }
  , { walsCode := "mau", iso := "mph", value := .inclusiveExclusive }
  , { walsCode := "may", iso := "ayz", value := .noInclusiveExclusive }
  , { walsCode := "mei", iso := "mni", value := .noPersonMarking }
  , { walsCode := "mss", iso := "skd", value := .inclusiveExclusive }
  , { walsCode := "mxc", iso := "mig", value := .onlyInclusive }
  , { walsCode := "mun", iso := "unr", value := .inclusiveExclusive }
  , { walsCode := "mrl", iso := "mur", value := .weTheSameAsI }
  , { walsCode := "nht", iso := "nhg", value := .noInclusiveExclusive }
  , { walsCode := "kho", iso := "naq", value := .noPersonMarking }
  , { walsCode := "nav", iso := "nav", value := .noInclusiveExclusive }
  , { walsCode := "ndy", iso := "djk", value := .noPersonMarking }
  , { walsCode := "ntu", iso := "yrk", value := .noInclusiveExclusive }
  , { walsCode := "nez", iso := "nez", value := .weTheSameAsI }
  , { walsCode := "nti", iso := "niy", value := .onlyInclusive }
  , { walsCode := "ngi", iso := "wyb", value := .noPersonMarking }
  , { walsCode := "niv", iso := "niv", value := .noPersonMarking }
  , { walsCode := "nko", iso := "cgg", value := .noInclusiveExclusive }
  , { walsCode := "nbd", iso := "dgl", value := .noInclusiveExclusive }
  , { walsCode := "nug", iso := "nuy", value := .inclusiveExclusive }
  , { walsCode := "ond", iso := "one", value := .inclusiveExclusive }
  , { walsCode := "orh", iso := "hae", value := .noInclusiveExclusive }
  , { walsCode := "oix", iso := "otz", value := .weTheSameAsI }
  , { walsCode := "pms", iso := "pma", value := .inclusiveExclusive }
  , { walsCode := "pai", iso := "pwn", value := .noPersonMarking }
  , { walsCode := "psm", iso := "pqm", value := .onlyInclusive }
  , { walsCode := "pau", iso := "pad", value := .noInclusiveExclusive }
  , { walsCode := "prs", iso := "pes", value := .noInclusiveExclusive }
  , { walsCode := "prh", iso := "myp", value := .noPersonMarking }
  , { walsCode := "pit", iso := "pjt", value := .noPersonMarking }
  , { walsCode := "pso", iso := "pom", value := .noPersonMarking }
  , { walsCode := "qaw", iso := "alc", value := .noPersonMarking }
  , { walsCode := "qim", iso := "qvi", value := .noInclusiveExclusive }
  , { walsCode := "ram", iso := "rma", value := .noInclusiveExclusive }
  , { walsCode := "rap", iso := "rap", value := .noPersonMarking }
  , { walsCode := "rus", iso := "rus", value := .noInclusiveExclusive }
  , { walsCode := "san", iso := "sag", value := .noPersonMarking }
  , { walsCode := "snm", iso := "xsu", value := .noPersonMarking }
  , { walsCode := "sel", iso := "ona", value := .noPersonMarking }
  , { walsCode := "sml", iso := "sza", value := .onlyInclusive }
  , { walsCode := "snt", iso := "set", value := .noInclusiveExclusive }
  , { walsCode := "shk", iso := "shp", value := .noPersonMarking }
  , { walsCode := "sla", iso := "den", value := .noInclusiveExclusive }
  , { walsCode := "spa", iso := "spa", value := .noInclusiveExclusive }
  , { walsCode := "squ", iso := "squ", value := .noInclusiveExclusive }
  , { walsCode := "sue", iso := "sue", value := .inclusiveExclusive }
  , { walsCode := "sup", iso := "spp", value := .noPersonMarking }
  , { walsCode := "swa", iso := "swh", value := .noInclusiveExclusive }
  , { walsCode := "tab", iso := "mky", value := .inclusiveExclusive }
  , { walsCode := "tag", iso := "tgl", value := .noPersonMarking }
  , { walsCode := "tha", iso := "tha", value := .noPersonMarking }
  , { walsCode := "tiw", iso := "tiw", value := .inclusiveExclusive }
  , { walsCode := "tli", iso := "tli", value := .noInclusiveExclusive }
  , { walsCode := "tru", iso := "tpy", value := .noPersonMarking }
  , { walsCode := "tsi", iso := "tsi", value := .noInclusiveExclusive }
  , { walsCode := "tuk", iso := "", value := .noInclusiveExclusive }
  , { walsCode := "tun", iso := "tun", value := .noInclusiveExclusive }
  , { walsCode := "tur", iso := "tur", value := .noInclusiveExclusive }
  , { walsCode := "una", iso := "mtg", value := .noInclusiveExclusive }
  , { walsCode := "ung", iso := "ung", value := .inclusiveExclusive }
  , { walsCode := "urk", iso := "urb", value := .noInclusiveExclusive }
  , { walsCode := "usa", iso := "wnu", value := .noInclusiveExclusive }
  , { walsCode := "vie", iso := "vie", value := .noPersonMarking }
  , { walsCode := "wam", iso := "wmb", value := .noPersonMarking }
  , { walsCode := "wra", iso := "wba", value := .noPersonMarking }
  , { walsCode := "wrd", iso := "wrr", value := .inclusiveExclusive }
  , { walsCode := "war", iso := "pav", value := .inclusiveExclusive }
  , { walsCode := "wic", iso := "wic", value := .onlyInclusive }
  , { walsCode := "wch", iso := "mzh", value := .weTheSameAsI }
  , { walsCode := "yag", iso := "yad", value := .inclusiveExclusive }
  , { walsCode := "yaq", iso := "yaq", value := .noPersonMarking }
  , { walsCode := "yid", iso := "yii", value := .noPersonMarking }
  , { walsCode := "yim", iso := "yee", value := .noInclusiveExclusive }
  , { walsCode := "yor", iso := "yor", value := .noPersonMarking }
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

end Core.WALS.F40A
