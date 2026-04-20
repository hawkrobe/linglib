import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 28A: Case Syncretism
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 28A`.

Chapter 28, 198 languages.
-/

namespace Core.WALS.F28A

/-- WALS 28A values. -/
inductive CaseSyncretism where
  /-- No case marking (123 languages). -/
  | noCaseMarking
  /-- Core cases only (18 languages). -/
  | coreCasesOnly
  /-- Core and non-core (22 languages). -/
  | coreAndNonCore
  /-- No syncretism (35 languages). -/
  | noSyncretism
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 28A dataset (198 languages). -/
def allData : List (Datapoint CaseSyncretism) :=
  [ { walsCode := "abi", iso := "axb", value := .noCaseMarking }
  , { walsCode := "abk", iso := "abk", value := .noCaseMarking }
  , { walsCode := "aco", iso := "kjq", value := .noCaseMarking }
  , { walsCode := "ain", iso := "ain", value := .noCaseMarking }
  , { walsCode := "ala", iso := "amp", value := .noCaseMarking }
  , { walsCode := "ame", iso := "aey", value := .noCaseMarking }
  , { walsCode := "apu", iso := "apu", value := .noCaseMarking }
  , { walsCode := "aeg", iso := "arz", value := .noCaseMarking }
  , { walsCode := "ana", iso := "aro", value := .coreAndNonCore }
  , { walsCode := "arp", iso := "ape", value := .noCaseMarking }
  , { walsCode := "arm", iso := "hye", value := .coreAndNonCore }
  , { walsCode := "asm", iso := "cns", value := .noCaseMarking }
  , { walsCode := "awp", iso := "kwi", value := .noCaseMarking }
  , { walsCode := "aym", iso := "ayr", value := .noCaseMarking }
  , { walsCode := "bag", iso := "bmi", value := .noCaseMarking }
  , { walsCode := "bam", iso := "bam", value := .noCaseMarking }
  , { walsCode := "brs", iso := "bsn", value := .noCaseMarking }
  , { walsCode := "bsq", iso := "eus", value := .coreCasesOnly }
  , { walsCode := "bkr", iso := "btx", value := .noCaseMarking }
  , { walsCode := "baw", iso := "bgr", value := .noSyncretism }
  , { walsCode := "bej", iso := "bej", value := .noCaseMarking }
  , { walsCode := "bma", iso := "tzm", value := .noCaseMarking }
  , { walsCode := "brh", iso := "brh", value := .noSyncretism }
  , { walsCode := "bri", iso := "bzd", value := .noCaseMarking }
  , { walsCode := "brm", iso := "mya", value := .noCaseMarking }
  , { walsCode := "bur", iso := "bsk", value := .coreAndNonCore }
  , { walsCode := "cah", iso := "chl", value := .noSyncretism }
  , { walsCode := "cnl", iso := "ram", value := .noCaseMarking }
  , { walsCode := "car", iso := "car", value := .noCaseMarking }
  , { walsCode := "cyv", iso := "cyb", value := .noCaseMarking }
  , { walsCode := "cha", iso := "cha", value := .noCaseMarking }
  , { walsCode := "cle", iso := "cle", value := .noCaseMarking }
  , { walsCode := "chk", iso := "ckt", value := .coreAndNonCore }
  , { walsCode := "ccp", iso := "coc", value := .noSyncretism }
  , { walsCode := "cmn", iso := "com", value := .coreAndNonCore }
  , { walsCode := "coo", iso := "csz", value := .noCaseMarking }
  , { walsCode := "cre", iso := "crk", value := .noCaseMarking }
  , { walsCode := "dag", iso := "dgz", value := .noCaseMarking }
  , { walsCode := "dni", iso := "dni", value := .noCaseMarking }
  , { walsCode := "dio", iso := "dyo", value := .noCaseMarking }
  , { walsCode := "dre", iso := "dhv", value := .noCaseMarking }
  , { walsCode := "eka", iso := "ekg", value := .noCaseMarking }
  , { walsCode := "eng", iso := "eng", value := .coreCasesOnly }
  , { walsCode := "epe", iso := "sja", value := .noSyncretism }
  , { walsCode := "eve", iso := "evn", value := .noSyncretism }
  , { walsCode := "ewe", iso := "ewe", value := .noCaseMarking }
  , { walsCode := "fij", iso := "fij", value := .coreCasesOnly }
  , { walsCode := "fin", iso := "fin", value := .coreAndNonCore }
  , { walsCode := "fre", iso := "fra", value := .coreAndNonCore }
  , { walsCode := "fur", iso := "fvr", value := .noCaseMarking }
  , { walsCode := "gar", iso := "grt", value := .noSyncretism }
  , { walsCode := "geo", iso := "kat", value := .coreAndNonCore }
  , { walsCode := "ger", iso := "deu", value := .coreAndNonCore }
  , { walsCode := "goo", iso := "gni", value := .noCaseMarking }
  , { walsCode := "grb", iso := "grj", value := .noCaseMarking }
  , { walsCode := "grk", iso := "ell", value := .coreAndNonCore }
  , { walsCode := "grw", iso := "kal", value := .coreCasesOnly }
  , { walsCode := "gua", iso := "gug", value := .noCaseMarking }
  , { walsCode := "hai", iso := "hai", value := .noCaseMarking }
  , { walsCode := "ham", iso := "hmt", value := .noCaseMarking }
  , { walsCode := "hau", iso := "hau", value := .noSyncretism }
  , { walsCode := "heb", iso := "heb", value := .noCaseMarking }
  , { walsCode := "hin", iso := "hin", value := .coreAndNonCore }
  , { walsCode := "hix", iso := "hix", value := .noCaseMarking }
  , { walsCode := "hmo", iso := "hnj", value := .noCaseMarking }
  , { walsCode := "hmi", iso := "hto", value := .noSyncretism }
  , { walsCode := "hun", iso := "hun", value := .noSyncretism }
  , { walsCode := "hzb", iso := "huz", value := .noSyncretism }
  , { walsCode := "igb", iso := "ibo", value := .noCaseMarking }
  , { walsCode := "ika", iso := "arh", value := .noSyncretism }
  , { walsCode := "imo", iso := "imn", value := .noSyncretism }
  , { walsCode := "ind", iso := "ind", value := .noCaseMarking }
  , { walsCode := "ing", iso := "inh", value := .coreAndNonCore }
  , { walsCode := "irq", iso := "irk", value := .noCaseMarking }
  , { walsCode := "iri", iso := "gle", value := .coreAndNonCore }
  , { walsCode := "jak", iso := "jac", value := .noCaseMarking }
  , { walsCode := "jpn", iso := "jpn", value := .noCaseMarking }
  , { walsCode := "juh", iso := "ktz", value := .noCaseMarking }
  , { walsCode := "knd", iso := "kan", value := .noSyncretism }
  , { walsCode := "knr", iso := "knc", value := .noCaseMarking }
  , { walsCode := "krk", iso := "kyh", value := .noCaseMarking }
  , { walsCode := "kyl", iso := "eky", value := .noCaseMarking }
  , { walsCode := "kay", iso := "gyd", value := .coreAndNonCore }
  , { walsCode := "ker", iso := "ker", value := .noCaseMarking }
  , { walsCode := "ket", iso := "ket", value := .noSyncretism }
  , { walsCode := "kew", iso := "kew", value := .noCaseMarking }
  , { walsCode := "kha", iso := "khk", value := .noSyncretism }
  , { walsCode := "khs", iso := "kha", value := .noCaseMarking }
  , { walsCode := "khm", iso := "khm", value := .noCaseMarking }
  , { walsCode := "kmu", iso := "kjg", value := .noCaseMarking }
  , { walsCode := "klv", iso := "kij", value := .noCaseMarking }
  , { walsCode := "kio", iso := "kio", value := .noCaseMarking }
  , { walsCode := "krb", iso := "gil", value := .noCaseMarking }
  , { walsCode := "koa", iso := "cku", value := .noSyncretism }
  , { walsCode := "kob", iso := "kpw", value := .noCaseMarking }
  , { walsCode := "kon", iso := "kng", value := .noCaseMarking }
  , { walsCode := "kor", iso := "kor", value := .noCaseMarking }
  , { walsCode := "kfe", iso := "kfz", value := .noCaseMarking }
  , { walsCode := "kse", iso := "ses", value := .noCaseMarking }
  , { walsCode := "kro", iso := "kgo", value := .coreAndNonCore }
  , { walsCode := "knm", iso := "kun", value := .noCaseMarking }
  , { walsCode := "kut", iso := "kut", value := .noCaseMarking }
  , { walsCode := "lad", iso := "lbj", value := .noSyncretism }
  , { walsCode := "lak", iso := "lbe", value := .coreCasesOnly }
  , { walsCode := "lkt", iso := "lkt", value := .noCaseMarking }
  , { walsCode := "lan", iso := "laj", value := .noCaseMarking }
  , { walsCode := "lat", iso := "lav", value := .coreAndNonCore }
  , { walsCode := "lav", iso := "lvk", value := .noCaseMarking }
  , { walsCode := "lep", iso := "lep", value := .noSyncretism }
  , { walsCode := "lez", iso := "lez", value := .coreAndNonCore }
  , { walsCode := "luv", iso := "lue", value := .noCaseMarking }
  , { walsCode := "mab", iso := "mde", value := .noCaseMarking }
  , { walsCode := "mal", iso := "plt", value := .noCaseMarking }
  , { walsCode := "mnd", iso := "cmn", value := .noCaseMarking }
  , { walsCode := "myi", iso := "mpc", value := .coreCasesOnly }
  , { walsCode := "mao", iso := "mri", value := .noCaseMarking }
  , { walsCode := "map", iso := "arn", value := .noCaseMarking }
  , { walsCode := "mku", iso := "zmr", value := .noCaseMarking }
  , { walsCode := "mar", iso := "mrc", value := .noSyncretism }
  , { walsCode := "mrd", iso := "mrz", value := .noCaseMarking }
  , { walsCode := "mrt", iso := "vma", value := .coreAndNonCore }
  , { walsCode := "mau", iso := "mph", value := .noCaseMarking }
  , { walsCode := "may", iso := "ayz", value := .noCaseMarking }
  , { walsCode := "mei", iso := "mni", value := .noSyncretism }
  , { walsCode := "mss", iso := "skd", value := .noSyncretism }
  , { walsCode := "mxc", iso := "mig", value := .noCaseMarking }
  , { walsCode := "mun", iso := "unr", value := .noCaseMarking }
  , { walsCode := "mrl", iso := "mur", value := .coreCasesOnly }
  , { walsCode := "nht", iso := "nhg", value := .noCaseMarking }
  , { walsCode := "kho", iso := "naq", value := .noCaseMarking }
  , { walsCode := "nav", iso := "nav", value := .noCaseMarking }
  , { walsCode := "ndy", iso := "djk", value := .noCaseMarking }
  , { walsCode := "ntu", iso := "yrk", value := .coreAndNonCore }
  , { walsCode := "nez", iso := "nez", value := .noSyncretism }
  , { walsCode := "nti", iso := "niy", value := .noCaseMarking }
  , { walsCode := "ngi", iso := "wyb", value := .coreAndNonCore }
  , { walsCode := "niv", iso := "niv", value := .noSyncretism }
  , { walsCode := "nko", iso := "cgg", value := .noCaseMarking }
  , { walsCode := "nbd", iso := "dgl", value := .noSyncretism }
  , { walsCode := "nug", iso := "nuy", value := .noSyncretism }
  , { walsCode := "orh", iso := "hae", value := .coreCasesOnly }
  , { walsCode := "otm", iso := "ote", value := .noCaseMarking }
  , { walsCode := "pms", iso := "pma", value := .noCaseMarking }
  , { walsCode := "pai", iso := "pwn", value := .noSyncretism }
  , { walsCode := "psm", iso := "pqm", value := .noCaseMarking }
  , { walsCode := "pau", iso := "pad", value := .coreCasesOnly }
  , { walsCode := "prs", iso := "pes", value := .noCaseMarking }
  , { walsCode := "prh", iso := "myp", value := .noCaseMarking }
  , { walsCode := "pit", iso := "pjt", value := .coreCasesOnly }
  , { walsCode := "pso", iso := "pom", value := .noSyncretism }
  , { walsCode := "qaw", iso := "alc", value := .noCaseMarking }
  , { walsCode := "qim", iso := "qvi", value := .noSyncretism }
  , { walsCode := "ram", iso := "rma", value := .noCaseMarking }
  , { walsCode := "rap", iso := "rap", value := .noCaseMarking }
  , { walsCode := "rus", iso := "rus", value := .coreAndNonCore }
  , { walsCode := "san", iso := "sag", value := .noCaseMarking }
  , { walsCode := "snm", iso := "xsu", value := .noCaseMarking }
  , { walsCode := "sel", iso := "ona", value := .noCaseMarking }
  , { walsCode := "snt", iso := "set", value := .noCaseMarking }
  , { walsCode := "shk", iso := "shp", value := .noCaseMarking }
  , { walsCode := "sla", iso := "den", value := .noCaseMarking }
  , { walsCode := "spa", iso := "spa", value := .coreAndNonCore }
  , { walsCode := "squ", iso := "squ", value := .noCaseMarking }
  , { walsCode := "sue", iso := "sue", value := .coreCasesOnly }
  , { walsCode := "sup", iso := "spp", value := .noCaseMarking }
  , { walsCode := "swa", iso := "swh", value := .noCaseMarking }
  , { walsCode := "tab", iso := "mky", value := .noCaseMarking }
  , { walsCode := "tag", iso := "tgl", value := .noCaseMarking }
  , { walsCode := "tha", iso := "tha", value := .noCaseMarking }
  , { walsCode := "tiw", iso := "tiw", value := .noCaseMarking }
  , { walsCode := "tli", iso := "tli", value := .noCaseMarking }
  , { walsCode := "tru", iso := "tpy", value := .noSyncretism }
  , { walsCode := "tsi", iso := "tsi", value := .noCaseMarking }
  , { walsCode := "tuk", iso := "", value := .noCaseMarking }
  , { walsCode := "tun", iso := "tun", value := .noCaseMarking }
  , { walsCode := "tur", iso := "tur", value := .noSyncretism }
  , { walsCode := "una", iso := "mtg", value := .noSyncretism }
  , { walsCode := "ung", iso := "ung", value := .noCaseMarking }
  , { walsCode := "urk", iso := "urb", value := .noCaseMarking }
  , { walsCode := "usa", iso := "wnu", value := .noCaseMarking }
  , { walsCode := "vie", iso := "vie", value := .noCaseMarking }
  , { walsCode := "wam", iso := "wmb", value := .coreCasesOnly }
  , { walsCode := "wra", iso := "wba", value := .coreCasesOnly }
  , { walsCode := "wrd", iso := "wrr", value := .noSyncretism }
  , { walsCode := "war", iso := "pav", value := .noCaseMarking }
  , { walsCode := "wic", iso := "wic", value := .noCaseMarking }
  , { walsCode := "wch", iso := "mzh", value := .noCaseMarking }
  , { walsCode := "yag", iso := "yad", value := .noCaseMarking }
  , { walsCode := "yaq", iso := "yaq", value := .coreCasesOnly }
  , { walsCode := "yid", iso := "yii", value := .coreCasesOnly }
  , { walsCode := "yim", iso := "yee", value := .noCaseMarking }
  , { walsCode := "yor", iso := "yor", value := .noSyncretism }
  , { walsCode := "yuc", iso := "yuc", value := .noCaseMarking }
  , { walsCode := "yko", iso := "yux", value := .coreCasesOnly }
  , { walsCode := "ypk", iso := "esu", value := .coreCasesOnly }
  , { walsCode := "yur", iso := "yur", value := .coreCasesOnly }
  , { walsCode := "zqc", iso := "zoc", value := .noSyncretism }
  , { walsCode := "zul", iso := "zul", value := .noCaseMarking }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F28A
