import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 98A: Alignment of Case Marking of Full Noun Phrases
@cite{comrie-2013b}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 98A`.

Chapter 98, 190 languages.
-/

namespace Core.WALS.F98A

/-- WALS 98A values. -/
inductive NPCaseAlignment where
  /-- Neutral (98 languages). -/
  | neutral
  /-- Nominative - accusative (standard) (46 languages). -/
  | nominativeAccusative
  /-- Nominative - accusative (marked nominative) (6 languages). -/
  | nominativeAccusative_3
  /-- Ergative - absolutive (32 languages). -/
  | ergativeAbsolutive
  /-- Tripartite (4 languages). -/
  | tripartite
  /-- Active-inactive (4 languages). -/
  | activeInactive
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 98A dataset (190 languages). -/
def allData : List (Datapoint NPCaseAlignment) :=
  [ { walsCode := "abi", iso := "axb", value := .neutral }
  , { walsCode := "abk", iso := "abk", value := .neutral }
  , { walsCode := "aco", iso := "kjq", value := .neutral }
  , { walsCode := "ain", iso := "ain", value := .neutral }
  , { walsCode := "ala", iso := "amp", value := .neutral }
  , { walsCode := "ame", iso := "aey", value := .neutral }
  , { walsCode := "apu", iso := "apu", value := .neutral }
  , { walsCode := "aeg", iso := "arz", value := .neutral }
  , { walsCode := "ana", iso := "aro", value := .ergativeAbsolutive }
  , { walsCode := "arp", iso := "ape", value := .neutral }
  , { walsCode := "arm", iso := "hye", value := .nominativeAccusative }
  , { walsCode := "asm", iso := "cns", value := .neutral }
  , { walsCode := "awp", iso := "kwi", value := .nominativeAccusative }
  , { walsCode := "aym", iso := "ayr", value := .nominativeAccusative_3 }
  , { walsCode := "bag", iso := "bmi", value := .neutral }
  , { walsCode := "bam", iso := "bam", value := .neutral }
  , { walsCode := "brs", iso := "bsn", value := .nominativeAccusative }
  , { walsCode := "bsq", iso := "eus", value := .activeInactive }
  , { walsCode := "bkr", iso := "btx", value := .neutral }
  , { walsCode := "baw", iso := "bgr", value := .ergativeAbsolutive }
  , { walsCode := "bma", iso := "tzm", value := .nominativeAccusative_3 }
  , { walsCode := "brh", iso := "brh", value := .nominativeAccusative }
  , { walsCode := "bri", iso := "bzd", value := .ergativeAbsolutive }
  , { walsCode := "brm", iso := "mya", value := .nominativeAccusative }
  , { walsCode := "bur", iso := "bsk", value := .ergativeAbsolutive }
  , { walsCode := "cah", iso := "chl", value := .nominativeAccusative }
  , { walsCode := "cnl", iso := "ram", value := .neutral }
  , { walsCode := "car", iso := "car", value := .neutral }
  , { walsCode := "cyv", iso := "cyb", value := .neutral }
  , { walsCode := "cha", iso := "cha", value := .neutral }
  , { walsCode := "cle", iso := "cle", value := .neutral }
  , { walsCode := "chk", iso := "ckt", value := .ergativeAbsolutive }
  , { walsCode := "cmn", iso := "com", value := .nominativeAccusative }
  , { walsCode := "coo", iso := "csz", value := .ergativeAbsolutive }
  , { walsCode := "cea", iso := "csw", value := .neutral }
  , { walsCode := "dag", iso := "dgz", value := .neutral }
  , { walsCode := "dni", iso := "dni", value := .ergativeAbsolutive }
  , { walsCode := "dio", iso := "dyo", value := .neutral }
  , { walsCode := "dre", iso := "dhv", value := .activeInactive }
  , { walsCode := "eka", iso := "ekg", value := .neutral }
  , { walsCode := "eng", iso := "eng", value := .neutral }
  , { walsCode := "epe", iso := "sja", value := .ergativeAbsolutive }
  , { walsCode := "eve", iso := "evn", value := .nominativeAccusative }
  , { walsCode := "ewe", iso := "ewe", value := .neutral }
  , { walsCode := "fij", iso := "fij", value := .neutral }
  , { walsCode := "fin", iso := "fin", value := .nominativeAccusative }
  , { walsCode := "fre", iso := "fra", value := .neutral }
  , { walsCode := "fur", iso := "fvr", value := .nominativeAccusative }
  , { walsCode := "gar", iso := "grt", value := .nominativeAccusative }
  , { walsCode := "geo", iso := "kat", value := .activeInactive }
  , { walsCode := "ger", iso := "deu", value := .nominativeAccusative }
  , { walsCode := "goo", iso := "gni", value := .ergativeAbsolutive }
  , { walsCode := "grb", iso := "grj", value := .neutral }
  , { walsCode := "grk", iso := "ell", value := .nominativeAccusative }
  , { walsCode := "grw", iso := "kal", value := .ergativeAbsolutive }
  , { walsCode := "gua", iso := "gug", value := .nominativeAccusative }
  , { walsCode := "hai", iso := "hai", value := .neutral }
  , { walsCode := "ham", iso := "hmt", value := .neutral }
  , { walsCode := "hau", iso := "hau", value := .neutral }
  , { walsCode := "heb", iso := "heb", value := .nominativeAccusative }
  , { walsCode := "hin", iso := "hin", value := .tripartite }
  , { walsCode := "hix", iso := "hix", value := .neutral }
  , { walsCode := "hmo", iso := "hnj", value := .neutral }
  , { walsCode := "hun", iso := "hun", value := .nominativeAccusative }
  , { walsCode := "hzb", iso := "huz", value := .ergativeAbsolutive }
  , { walsCode := "igb", iso := "ibo", value := .nominativeAccusative_3 }
  , { walsCode := "ika", iso := "arh", value := .ergativeAbsolutive }
  , { walsCode := "imo", iso := "imn", value := .activeInactive }
  , { walsCode := "ind", iso := "ind", value := .neutral }
  , { walsCode := "ing", iso := "inh", value := .ergativeAbsolutive }
  , { walsCode := "irq", iso := "irk", value := .nominativeAccusative }
  , { walsCode := "iri", iso := "gle", value := .neutral }
  , { walsCode := "jak", iso := "jac", value := .neutral }
  , { walsCode := "jpn", iso := "jpn", value := .nominativeAccusative }
  , { walsCode := "juh", iso := "ktz", value := .neutral }
  , { walsCode := "knd", iso := "kan", value := .nominativeAccusative }
  , { walsCode := "knr", iso := "knc", value := .nominativeAccusative }
  , { walsCode := "krk", iso := "kyh", value := .neutral }
  , { walsCode := "kyl", iso := "eky", value := .neutral }
  , { walsCode := "kay", iso := "gyd", value := .nominativeAccusative }
  , { walsCode := "ker", iso := "ker", value := .neutral }
  , { walsCode := "ket", iso := "ket", value := .neutral }
  , { walsCode := "kew", iso := "kew", value := .ergativeAbsolutive }
  , { walsCode := "kha", iso := "khk", value := .nominativeAccusative }
  , { walsCode := "khs", iso := "kha", value := .nominativeAccusative }
  , { walsCode := "khm", iso := "khm", value := .neutral }
  , { walsCode := "kmu", iso := "kjg", value := .neutral }
  , { walsCode := "klv", iso := "kij", value := .neutral }
  , { walsCode := "kio", iso := "kio", value := .neutral }
  , { walsCode := "krb", iso := "gil", value := .neutral }
  , { walsCode := "koa", iso := "cku", value := .nominativeAccusative }
  , { walsCode := "kob", iso := "kpw", value := .neutral }
  , { walsCode := "kon", iso := "kng", value := .neutral }
  , { walsCode := "kor", iso := "kor", value := .nominativeAccusative }
  , { walsCode := "kfe", iso := "kfz", value := .neutral }
  , { walsCode := "kse", iso := "ses", value := .neutral }
  , { walsCode := "kro", iso := "kgo", value := .neutral }
  , { walsCode := "knm", iso := "kun", value := .nominativeAccusative }
  , { walsCode := "kut", iso := "kut", value := .neutral }
  , { walsCode := "lad", iso := "lbj", value := .ergativeAbsolutive }
  , { walsCode := "lak", iso := "lbe", value := .ergativeAbsolutive }
  , { walsCode := "lkt", iso := "lkt", value := .neutral }
  , { walsCode := "lan", iso := "laj", value := .neutral }
  , { walsCode := "lat", iso := "lav", value := .nominativeAccusative }
  , { walsCode := "lav", iso := "lvk", value := .neutral }
  , { walsCode := "lep", iso := "lep", value := .nominativeAccusative }
  , { walsCode := "lez", iso := "lez", value := .ergativeAbsolutive }
  , { walsCode := "luv", iso := "lue", value := .neutral }
  , { walsCode := "mal", iso := "plt", value := .nominativeAccusative }
  , { walsCode := "mnd", iso := "cmn", value := .neutral }
  , { walsCode := "myi", iso := "mpc", value := .nominativeAccusative }
  , { walsCode := "mao", iso := "mri", value := .nominativeAccusative }
  , { walsCode := "map", iso := "arn", value := .neutral }
  , { walsCode := "mku", iso := "zmr", value := .neutral }
  , { walsCode := "mhi", iso := "mar", value := .tripartite }
  , { walsCode := "mar", iso := "mrc", value := .nominativeAccusative_3 }
  , { walsCode := "mrd", iso := "mrz", value := .neutral }
  , { walsCode := "mrt", iso := "vma", value := .nominativeAccusative }
  , { walsCode := "mau", iso := "mph", value := .neutral }
  , { walsCode := "may", iso := "ayz", value := .neutral }
  , { walsCode := "mei", iso := "mni", value := .nominativeAccusative }
  , { walsCode := "mss", iso := "skd", value := .nominativeAccusative }
  , { walsCode := "mxc", iso := "mig", value := .neutral }
  , { walsCode := "mun", iso := "unr", value := .neutral }
  , { walsCode := "mrl", iso := "mur", value := .nominativeAccusative_3 }
  , { walsCode := "nht", iso := "nhg", value := .neutral }
  , { walsCode := "kho", iso := "naq", value := .nominativeAccusative }
  , { walsCode := "nav", iso := "nav", value := .neutral }
  , { walsCode := "ndy", iso := "djk", value := .neutral }
  , { walsCode := "ntu", iso := "yrk", value := .nominativeAccusative }
  , { walsCode := "nez", iso := "nez", value := .tripartite }
  , { walsCode := "nti", iso := "niy", value := .neutral }
  , { walsCode := "ngi", iso := "wyb", value := .ergativeAbsolutive }
  , { walsCode := "niv", iso := "niv", value := .neutral }
  , { walsCode := "nko", iso := "cgg", value := .neutral }
  , { walsCode := "nbd", iso := "dgl", value := .nominativeAccusative }
  , { walsCode := "nug", iso := "nuy", value := .neutral }
  , { walsCode := "orh", iso := "hae", value := .nominativeAccusative_3 }
  , { walsCode := "otm", iso := "ote", value := .neutral }
  , { walsCode := "pms", iso := "pma", value := .neutral }
  , { walsCode := "psm", iso := "pqm", value := .neutral }
  , { walsCode := "pau", iso := "pad", value := .ergativeAbsolutive }
  , { walsCode := "prs", iso := "pes", value := .nominativeAccusative }
  , { walsCode := "prh", iso := "myp", value := .neutral }
  , { walsCode := "pit", iso := "pjt", value := .ergativeAbsolutive }
  , { walsCode := "pso", iso := "pom", value := .nominativeAccusative }
  , { walsCode := "qim", iso := "qvi", value := .nominativeAccusative }
  , { walsCode := "ram", iso := "rma", value := .neutral }
  , { walsCode := "rap", iso := "rap", value := .neutral }
  , { walsCode := "rus", iso := "rus", value := .nominativeAccusative }
  , { walsCode := "san", iso := "sag", value := .neutral }
  , { walsCode := "snm", iso := "xsu", value := .ergativeAbsolutive }
  , { walsCode := "sml", iso := "sza", value := .tripartite }
  , { walsCode := "shk", iso := "shp", value := .ergativeAbsolutive }
  , { walsCode := "sla", iso := "den", value := .neutral }
  , { walsCode := "spa", iso := "spa", value := .nominativeAccusative }
  , { walsCode := "squ", iso := "squ", value := .neutral }
  , { walsCode := "sue", iso := "sue", value := .ergativeAbsolutive }
  , { walsCode := "sup", iso := "spp", value := .neutral }
  , { walsCode := "swa", iso := "swh", value := .neutral }
  , { walsCode := "tab", iso := "mky", value := .neutral }
  , { walsCode := "tag", iso := "tgl", value := .neutral }
  , { walsCode := "tha", iso := "tha", value := .neutral }
  , { walsCode := "tiw", iso := "tiw", value := .neutral }
  , { walsCode := "tru", iso := "tpy", value := .ergativeAbsolutive }
  , { walsCode := "tsi", iso := "tsi", value := .ergativeAbsolutive }
  , { walsCode := "tuk", iso := "", value := .ergativeAbsolutive }
  , { walsCode := "tun", iso := "tun", value := .neutral }
  , { walsCode := "tur", iso := "tur", value := .nominativeAccusative }
  , { walsCode := "una", iso := "mtg", value := .ergativeAbsolutive }
  , { walsCode := "ung", iso := "ung", value := .neutral }
  , { walsCode := "urk", iso := "urb", value := .nominativeAccusative }
  , { walsCode := "usa", iso := "wnu", value := .neutral }
  , { walsCode := "vie", iso := "vie", value := .neutral }
  , { walsCode := "wam", iso := "wmb", value := .ergativeAbsolutive }
  , { walsCode := "wra", iso := "wba", value := .neutral }
  , { walsCode := "wrd", iso := "wrr", value := .ergativeAbsolutive }
  , { walsCode := "war", iso := "pav", value := .neutral }
  , { walsCode := "wic", iso := "wic", value := .neutral }
  , { walsCode := "wch", iso := "mzh", value := .neutral }
  , { walsCode := "yag", iso := "yad", value := .neutral }
  , { walsCode := "yaq", iso := "yaq", value := .nominativeAccusative }
  , { walsCode := "yid", iso := "yii", value := .ergativeAbsolutive }
  , { walsCode := "yim", iso := "yee", value := .neutral }
  , { walsCode := "yor", iso := "yor", value := .neutral }
  , { walsCode := "yko", iso := "yux", value := .nominativeAccusative }
  , { walsCode := "ypk", iso := "esu", value := .ergativeAbsolutive }
  , { walsCode := "yur", iso := "yur", value := .neutral }
  , { walsCode := "zqc", iso := "zoc", value := .ergativeAbsolutive }
  , { walsCode := "zul", iso := "zul", value := .neutral }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F98A
