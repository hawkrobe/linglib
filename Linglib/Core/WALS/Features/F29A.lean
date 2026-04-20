import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 29A: Syncretism in Verbal Person/Number Marking
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 29A`.

Chapter 29, 198 languages.
-/

namespace Core.WALS.F29A

/-- WALS 29A values. -/
inductive SyncretismInVerbalPersonNumberMarking where
  /-- No subject person/number marking (57 languages). -/
  | noSubjectPersonNumberMarking
  /-- Syncretic (60 languages). -/
  | syncretic
  /-- Not syncretic (81 languages). -/
  | notSyncretic
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 29A dataset (198 languages). -/
def allData : List (Datapoint SyncretismInVerbalPersonNumberMarking) :=
  [ { walsCode := "abi", iso := "axb", value := .syncretic }
  , { walsCode := "abk", iso := "abk", value := .notSyncretic }
  , { walsCode := "aco", iso := "kjq", value := .notSyncretic }
  , { walsCode := "ain", iso := "ain", value := .notSyncretic }
  , { walsCode := "ala", iso := "amp", value := .notSyncretic }
  , { walsCode := "ame", iso := "aey", value := .syncretic }
  , { walsCode := "apu", iso := "apu", value := .notSyncretic }
  , { walsCode := "aeg", iso := "arz", value := .syncretic }
  , { walsCode := "ana", iso := "aro", value := .noSubjectPersonNumberMarking }
  , { walsCode := "arp", iso := "ape", value := .notSyncretic }
  , { walsCode := "arm", iso := "hye", value := .notSyncretic }
  , { walsCode := "asm", iso := "cns", value := .notSyncretic }
  , { walsCode := "awp", iso := "kwi", value := .syncretic }
  , { walsCode := "aym", iso := "ayr", value := .syncretic }
  , { walsCode := "bag", iso := "bmi", value := .syncretic }
  , { walsCode := "bam", iso := "bam", value := .noSubjectPersonNumberMarking }
  , { walsCode := "brs", iso := "bsn", value := .notSyncretic }
  , { walsCode := "bsq", iso := "eus", value := .notSyncretic }
  , { walsCode := "bkr", iso := "btx", value := .notSyncretic }
  , { walsCode := "baw", iso := "bgr", value := .notSyncretic }
  , { walsCode := "bej", iso := "bej", value := .syncretic }
  , { walsCode := "bma", iso := "tzm", value := .notSyncretic }
  , { walsCode := "brh", iso := "brh", value := .notSyncretic }
  , { walsCode := "bri", iso := "bzd", value := .noSubjectPersonNumberMarking }
  , { walsCode := "brm", iso := "mya", value := .noSubjectPersonNumberMarking }
  , { walsCode := "bur", iso := "bsk", value := .syncretic }
  , { walsCode := "cah", iso := "chl", value := .notSyncretic }
  , { walsCode := "cnl", iso := "ram", value := .syncretic }
  , { walsCode := "car", iso := "car", value := .syncretic }
  , { walsCode := "cyv", iso := "cyb", value := .syncretic }
  , { walsCode := "cha", iso := "cha", value := .notSyncretic }
  , { walsCode := "cle", iso := "cle", value := .syncretic }
  , { walsCode := "chk", iso := "ckt", value := .syncretic }
  , { walsCode := "ccp", iso := "coc", value := .notSyncretic }
  , { walsCode := "cmn", iso := "com", value := .noSubjectPersonNumberMarking }
  , { walsCode := "coo", iso := "csz", value := .notSyncretic }
  , { walsCode := "cre", iso := "crk", value := .notSyncretic }
  , { walsCode := "dag", iso := "dgz", value := .syncretic }
  , { walsCode := "dni", iso := "dni", value := .syncretic }
  , { walsCode := "dio", iso := "dyo", value := .syncretic }
  , { walsCode := "dre", iso := "dhv", value := .noSubjectPersonNumberMarking }
  , { walsCode := "eka", iso := "ekg", value := .syncretic }
  , { walsCode := "eng", iso := "eng", value := .syncretic }
  , { walsCode := "epe", iso := "sja", value := .noSubjectPersonNumberMarking }
  , { walsCode := "eve", iso := "evn", value := .notSyncretic }
  , { walsCode := "ewe", iso := "ewe", value := .syncretic }
  , { walsCode := "fij", iso := "fij", value := .noSubjectPersonNumberMarking }
  , { walsCode := "fin", iso := "fin", value := .notSyncretic }
  , { walsCode := "fre", iso := "fra", value := .syncretic }
  , { walsCode := "fur", iso := "fvr", value := .notSyncretic }
  , { walsCode := "gar", iso := "grt", value := .noSubjectPersonNumberMarking }
  , { walsCode := "geo", iso := "kat", value := .notSyncretic }
  , { walsCode := "ger", iso := "deu", value := .syncretic }
  , { walsCode := "goo", iso := "gni", value := .notSyncretic }
  , { walsCode := "grb", iso := "grj", value := .notSyncretic }
  , { walsCode := "grk", iso := "ell", value := .notSyncretic }
  , { walsCode := "grw", iso := "kal", value := .notSyncretic }
  , { walsCode := "gua", iso := "gug", value := .notSyncretic }
  , { walsCode := "hai", iso := "hai", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ham", iso := "hmt", value := .syncretic }
  , { walsCode := "hau", iso := "hau", value := .noSubjectPersonNumberMarking }
  , { walsCode := "heb", iso := "heb", value := .syncretic }
  , { walsCode := "hin", iso := "hin", value := .syncretic }
  , { walsCode := "hix", iso := "hix", value := .syncretic }
  , { walsCode := "hmo", iso := "hnj", value := .noSubjectPersonNumberMarking }
  , { walsCode := "hmi", iso := "hto", value := .notSyncretic }
  , { walsCode := "hun", iso := "hun", value := .notSyncretic }
  , { walsCode := "hzb", iso := "huz", value := .notSyncretic }
  , { walsCode := "igb", iso := "ibo", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ika", iso := "arh", value := .syncretic }
  , { walsCode := "imo", iso := "imn", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ind", iso := "ind", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ing", iso := "inh", value := .notSyncretic }
  , { walsCode := "irq", iso := "irk", value := .syncretic }
  , { walsCode := "iri", iso := "gle", value := .syncretic }
  , { walsCode := "jak", iso := "jac", value := .notSyncretic }
  , { walsCode := "jpn", iso := "jpn", value := .noSubjectPersonNumberMarking }
  , { walsCode := "juh", iso := "ktz", value := .noSubjectPersonNumberMarking }
  , { walsCode := "knd", iso := "kan", value := .syncretic }
  , { walsCode := "knr", iso := "knc", value := .notSyncretic }
  , { walsCode := "krk", iso := "kyh", value := .syncretic }
  , { walsCode := "kyl", iso := "eky", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kay", iso := "gyd", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ker", iso := "ker", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ket", iso := "ket", value := .syncretic }
  , { walsCode := "kew", iso := "kew", value := .syncretic }
  , { walsCode := "kha", iso := "khk", value := .noSubjectPersonNumberMarking }
  , { walsCode := "khs", iso := "kha", value := .noSubjectPersonNumberMarking }
  , { walsCode := "khm", iso := "khm", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kmu", iso := "kjg", value := .noSubjectPersonNumberMarking }
  , { walsCode := "klv", iso := "kij", value := .notSyncretic }
  , { walsCode := "kio", iso := "kio", value := .syncretic }
  , { walsCode := "krb", iso := "gil", value := .noSubjectPersonNumberMarking }
  , { walsCode := "koa", iso := "cku", value := .notSyncretic }
  , { walsCode := "kob", iso := "kpw", value := .syncretic }
  , { walsCode := "kon", iso := "kng", value := .syncretic }
  , { walsCode := "kor", iso := "kor", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kfe", iso := "kfz", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kse", iso := "ses", value := .noSubjectPersonNumberMarking }
  , { walsCode := "kro", iso := "kgo", value := .notSyncretic }
  , { walsCode := "knm", iso := "kun", value := .syncretic }
  , { walsCode := "kut", iso := "kut", value := .notSyncretic }
  , { walsCode := "lad", iso := "lbj", value := .noSubjectPersonNumberMarking }
  , { walsCode := "lak", iso := "lbe", value := .syncretic }
  , { walsCode := "lkt", iso := "lkt", value := .notSyncretic }
  , { walsCode := "lan", iso := "laj", value := .syncretic }
  , { walsCode := "lat", iso := "lav", value := .syncretic }
  , { walsCode := "lav", iso := "lvk", value := .syncretic }
  , { walsCode := "lep", iso := "lep", value := .noSubjectPersonNumberMarking }
  , { walsCode := "lez", iso := "lez", value := .noSubjectPersonNumberMarking }
  , { walsCode := "luv", iso := "lue", value := .syncretic }
  , { walsCode := "mab", iso := "mde", value := .notSyncretic }
  , { walsCode := "mal", iso := "plt", value := .notSyncretic }
  , { walsCode := "mnd", iso := "cmn", value := .noSubjectPersonNumberMarking }
  , { walsCode := "myi", iso := "mpc", value := .notSyncretic }
  , { walsCode := "mao", iso := "mri", value := .noSubjectPersonNumberMarking }
  , { walsCode := "map", iso := "arn", value := .notSyncretic }
  , { walsCode := "mku", iso := "zmr", value := .notSyncretic }
  , { walsCode := "mar", iso := "mrc", value := .notSyncretic }
  , { walsCode := "mrd", iso := "mrz", value := .syncretic }
  , { walsCode := "mrt", iso := "vma", value := .noSubjectPersonNumberMarking }
  , { walsCode := "mau", iso := "mph", value := .notSyncretic }
  , { walsCode := "may", iso := "ayz", value := .notSyncretic }
  , { walsCode := "mei", iso := "mni", value := .noSubjectPersonNumberMarking }
  , { walsCode := "mss", iso := "skd", value := .notSyncretic }
  , { walsCode := "mxc", iso := "mig", value := .notSyncretic }
  , { walsCode := "mun", iso := "unr", value := .notSyncretic }
  , { walsCode := "mrl", iso := "mur", value := .syncretic }
  , { walsCode := "nht", iso := "nhg", value := .notSyncretic }
  , { walsCode := "kho", iso := "naq", value := .syncretic }
  , { walsCode := "nav", iso := "nav", value := .notSyncretic }
  , { walsCode := "ndy", iso := "djk", value := .noSubjectPersonNumberMarking }
  , { walsCode := "ntu", iso := "yrk", value := .syncretic }
  , { walsCode := "nez", iso := "nez", value := .notSyncretic }
  , { walsCode := "nti", iso := "niy", value := .syncretic }
  , { walsCode := "ngi", iso := "wyb", value := .noSubjectPersonNumberMarking }
  , { walsCode := "niv", iso := "niv", value := .syncretic }
  , { walsCode := "nko", iso := "cgg", value := .syncretic }
  , { walsCode := "nbd", iso := "dgl", value := .syncretic }
  , { walsCode := "nug", iso := "nuy", value := .syncretic }
  , { walsCode := "ond", iso := "one", value := .notSyncretic }
  , { walsCode := "orh", iso := "hae", value := .syncretic }
  , { walsCode := "pms", iso := "pma", value := .notSyncretic }
  , { walsCode := "pai", iso := "pwn", value := .notSyncretic }
  , { walsCode := "psm", iso := "pqm", value := .notSyncretic }
  , { walsCode := "pau", iso := "pad", value := .notSyncretic }
  , { walsCode := "prs", iso := "pes", value := .notSyncretic }
  , { walsCode := "prh", iso := "myp", value := .noSubjectPersonNumberMarking }
  , { walsCode := "pit", iso := "pjt", value := .noSubjectPersonNumberMarking }
  , { walsCode := "pso", iso := "pom", value := .noSubjectPersonNumberMarking }
  , { walsCode := "qaw", iso := "alc", value := .noSubjectPersonNumberMarking }
  , { walsCode := "qim", iso := "qvi", value := .notSyncretic }
  , { walsCode := "ram", iso := "rma", value := .noSubjectPersonNumberMarking }
  , { walsCode := "rap", iso := "rap", value := .noSubjectPersonNumberMarking }
  , { walsCode := "rus", iso := "rus", value := .notSyncretic }
  , { walsCode := "san", iso := "sag", value := .notSyncretic }
  , { walsCode := "snm", iso := "xsu", value := .noSubjectPersonNumberMarking }
  , { walsCode := "sel", iso := "ona", value := .noSubjectPersonNumberMarking }
  , { walsCode := "snt", iso := "set", value := .syncretic }
  , { walsCode := "shk", iso := "shp", value := .noSubjectPersonNumberMarking }
  , { walsCode := "sla", iso := "den", value := .notSyncretic }
  , { walsCode := "spa", iso := "spa", value := .syncretic }
  , { walsCode := "squ", iso := "squ", value := .notSyncretic }
  , { walsCode := "sue", iso := "sue", value := .syncretic }
  , { walsCode := "sup", iso := "spp", value := .noSubjectPersonNumberMarking }
  , { walsCode := "swa", iso := "swh", value := .syncretic }
  , { walsCode := "tab", iso := "mky", value := .notSyncretic }
  , { walsCode := "tag", iso := "tgl", value := .noSubjectPersonNumberMarking }
  , { walsCode := "tha", iso := "tha", value := .noSubjectPersonNumberMarking }
  , { walsCode := "tiw", iso := "tiw", value := .syncretic }
  , { walsCode := "tli", iso := "tli", value := .notSyncretic }
  , { walsCode := "tru", iso := "tpy", value := .noSubjectPersonNumberMarking }
  , { walsCode := "tsi", iso := "tsi", value := .notSyncretic }
  , { walsCode := "tuk", iso := "", value := .notSyncretic }
  , { walsCode := "tun", iso := "tun", value := .notSyncretic }
  , { walsCode := "tur", iso := "tur", value := .notSyncretic }
  , { walsCode := "una", iso := "mtg", value := .notSyncretic }
  , { walsCode := "ung", iso := "ung", value := .notSyncretic }
  , { walsCode := "urk", iso := "urb", value := .notSyncretic }
  , { walsCode := "usa", iso := "wnu", value := .syncretic }
  , { walsCode := "vie", iso := "vie", value := .noSubjectPersonNumberMarking }
  , { walsCode := "wam", iso := "wmb", value := .notSyncretic }
  , { walsCode := "wra", iso := "wba", value := .noSubjectPersonNumberMarking }
  , { walsCode := "wrd", iso := "wrr", value := .notSyncretic }
  , { walsCode := "war", iso := "pav", value := .noSubjectPersonNumberMarking }
  , { walsCode := "wic", iso := "wic", value := .notSyncretic }
  , { walsCode := "wch", iso := "mzh", value := .notSyncretic }
  , { walsCode := "yag", iso := "yad", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yaq", iso := "yaq", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yid", iso := "yii", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yim", iso := "yee", value := .syncretic }
  , { walsCode := "yor", iso := "yor", value := .noSubjectPersonNumberMarking }
  , { walsCode := "yuc", iso := "yuc", value := .notSyncretic }
  , { walsCode := "yko", iso := "yux", value := .syncretic }
  , { walsCode := "ypk", iso := "esu", value := .notSyncretic }
  , { walsCode := "yur", iso := "yur", value := .notSyncretic }
  , { walsCode := "zqc", iso := "zoc", value := .notSyncretic }
  , { walsCode := "zul", iso := "zul", value := .syncretic }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F29A
