import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 131A: Numeral Bases
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 131A`.

Chapter 131, 196 languages.
-/

namespace Core.WALS.F131A

/-- WALS 131A values. -/
inductive NumeralBases where
  /-- Decimal (125 languages). -/
  | decimal
  /-- Hybrid vigesimal-decimal (22 languages). -/
  | hybridVigesimalDecimal
  /-- Pure vigesimal (20 languages). -/
  | pureVigesimal
  /-- Other base (5 languages). -/
  | otherBase
  /-- Extended body-part system (4 languages). -/
  | extendedBodyPartSystem
  /-- Restricted (20 languages). -/
  | restricted
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 131A dataset (196 languages). -/
def allData : List (Datapoint NumeralBases) :=
  [ { walsCode := "xoo", iso := "nmn", value := .restricted }
  , { walsCode := "abk", iso := "abk", value := .hybridVigesimalDecimal }
  , { walsCode := "abu", iso := "kgr", value := .decimal }
  , { walsCode := "acg", iso := "aca", value := .restricted }
  , { walsCode := "aco", iso := "kjq", value := .decimal }
  , { walsCode := "ain", iso := "ain", value := .pureVigesimal }
  , { walsCode := "abm", iso := "akz", value := .decimal }
  , { walsCode := "ala", iso := "amp", value := .pureVigesimal }
  , { walsCode := "alb", iso := "sqi", value := .decimal }
  , { walsCode := "amh", iso := "amh", value := .decimal }
  , { walsCode := "adk", iso := "ano", value := .pureVigesimal }
  , { walsCode := "aeg", iso := "arz", value := .decimal }
  , { walsCode := "ana", iso := "aro", value := .restricted }
  , { walsCode := "arc", iso := "aqc", value := .decimal }
  , { walsCode := "arm", iso := "hye", value := .decimal }
  , { walsCode := "awp", iso := "kwi", value := .restricted }
  , { walsCode := "aym", iso := "ayr", value := .decimal }
  , { walsCode := "bag", iso := "bmi", value := .decimal }
  , { walsCode := "bam", iso := "bam", value := .decimal }
  , { walsCode := "brs", iso := "bsn", value := .restricted }
  , { walsCode := "bae", iso := "bae", value := .restricted }
  , { walsCode := "bas", iso := "bas", value := .decimal }
  , { walsCode := "bsq", iso := "eus", value := .hybridVigesimalDecimal }
  , { walsCode := "bkr", iso := "btx", value := .decimal }
  , { walsCode := "baw", iso := "bgr", value := .decimal }
  , { walsCode := "bma", iso := "tzm", value := .decimal }
  , { walsCode := "brh", iso := "brh", value := .decimal }
  , { walsCode := "bri", iso := "bzd", value := .decimal }
  , { walsCode := "brm", iso := "mya", value := .decimal }
  , { walsCode := "bur", iso := "bsk", value := .hybridVigesimalDecimal }
  , { walsCode := "cah", iso := "chl", value := .decimal }
  , { walsCode := "car", iso := "car", value := .pureVigesimal }
  , { walsCode := "cyv", iso := "cyb", value := .decimal }
  , { walsCode := "cha", iso := "cha", value := .decimal }
  , { walsCode := "cle", iso := "cle", value := .hybridVigesimalDecimal }
  , { walsCode := "chk", iso := "ckt", value := .pureVigesimal }
  , { walsCode := "cuu", iso := "chk", value := .decimal }
  , { walsCode := "chv", iso := "chv", value := .decimal }
  , { walsCode := "cmn", iso := "com", value := .decimal }
  , { walsCode := "cre", iso := "crk", value := .decimal }
  , { walsCode := "dag", iso := "dgz", value := .pureVigesimal }
  , { walsCode := "dam", iso := "mbp", value := .decimal }
  , { walsCode := "dsh", iso := "dan", value := .hybridVigesimalDecimal }
  , { walsCode := "dio", iso := "dyo", value := .hybridVigesimalDecimal }
  , { walsCode := "dre", iso := "dhv", value := .pureVigesimal }
  , { walsCode := "eip", iso := "eip", value := .extendedBodyPartSystem }
  , { walsCode := "eka", iso := "ekg", value := .otherBase }
  , { walsCode := "emc", iso := "cmi", value := .otherBase }
  , { walsCode := "eng", iso := "eng", value := .decimal }
  , { walsCode := "eve", iso := "evn", value := .decimal }
  , { walsCode := "ewe", iso := "ewe", value := .decimal }
  , { walsCode := "fij", iso := "fij", value := .decimal }
  , { walsCode := "fin", iso := "fin", value := .decimal }
  , { walsCode := "fre", iso := "fra", value := .decimal }
  , { walsCode := "fum", iso := "ffm", value := .hybridVigesimalDecimal }
  , { walsCode := "fur", iso := "fvr", value := .decimal }
  , { walsCode := "gar", iso := "grt", value := .decimal }
  , { walsCode := "geo", iso := "kat", value := .hybridVigesimalDecimal }
  , { walsCode := "ger", iso := "deu", value := .decimal }
  , { walsCode := "goa", iso := "guc", value := .decimal }
  , { walsCode := "gol", iso := "gol", value := .hybridVigesimalDecimal }
  , { walsCode := "goo", iso := "gni", value := .restricted }
  , { walsCode := "grk", iso := "ell", value := .decimal }
  , { walsCode := "grw", iso := "kal", value := .hybridVigesimalDecimal }
  , { walsCode := "gua", iso := "gug", value := .decimal }
  , { walsCode := "gur", iso := "", value := .decimal }
  , { walsCode := "hai", iso := "hai", value := .decimal }
  , { walsCode := "har", iso := "tmd", value := .extendedBodyPartSystem }
  , { walsCode := "hau", iso := "hau", value := .decimal }
  , { walsCode := "heb", iso := "heb", value := .decimal }
  , { walsCode := "hin", iso := "hin", value := .decimal }
  , { walsCode := "hix", iso := "hix", value := .restricted }
  , { walsCode := "hmo", iso := "hnj", value := .decimal }
  , { walsCode := "hlp", iso := "yuf", value := .decimal }
  , { walsCode := "hve", iso := "huv", value := .hybridVigesimalDecimal }
  , { walsCode := "hun", iso := "hun", value := .decimal }
  , { walsCode := "hzb", iso := "huz", value := .decimal }
  , { walsCode := "hpd", iso := "jup", value := .restricted }
  , { walsCode := "hup", iso := "hup", value := .decimal }
  , { walsCode := "igb", iso := "ibo", value := .pureVigesimal }
  , { walsCode := "ika", iso := "arh", value := .decimal }
  , { walsCode := "imo", iso := "imn", value := .restricted }
  , { walsCode := "ind", iso := "ind", value := .decimal }
  , { walsCode := "ing", iso := "inh", value := .hybridVigesimalDecimal }
  , { walsCode := "irq", iso := "irk", value := .decimal }
  , { walsCode := "iri", iso := "gle", value := .hybridVigesimalDecimal }
  , { walsCode := "jak", iso := "jac", value := .hybridVigesimalDecimal }
  , { walsCode := "jpn", iso := "jpn", value := .decimal }
  , { walsCode := "jaq", iso := "jqr", value := .decimal }
  , { walsCode := "kab", iso := "kbd", value := .decimal }
  , { walsCode := "kan", iso := "ogo", value := .pureVigesimal }
  , { walsCode := "knd", iso := "kan", value := .decimal }
  , { walsCode := "knr", iso := "knc", value := .decimal }
  , { walsCode := "krk", iso := "kyh", value := .decimal }
  , { walsCode := "kyl", iso := "eky", value := .decimal }
  , { walsCode := "kay", iso := "gyd", value := .restricted }
  , { walsCode := "ket", iso := "ket", value := .decimal }
  , { walsCode := "khl", iso := "klj", value := .decimal }
  , { walsCode := "kha", iso := "khk", value := .decimal }
  , { walsCode := "kty", iso := "kca", value := .decimal }
  , { walsCode := "khm", iso := "khm", value := .decimal }
  , { walsCode := "klv", iso := "kij", value := .decimal }
  , { walsCode := "krb", iso := "gil", value := .decimal }
  , { walsCode := "koa", iso := "cku", value := .decimal }
  , { walsCode := "kob", iso := "kpw", value := .extendedBodyPartSystem }
  , { walsCode := "kor", iso := "kor", value := .decimal }
  , { walsCode := "kfe", iso := "kfz", value := .decimal }
  , { walsCode := "kse", iso := "ses", value := .decimal }
  , { walsCode := "kro", iso := "kgo", value := .pureVigesimal }
  , { walsCode := "knm", iso := "kun", value := .decimal }
  , { walsCode := "kut", iso := "kut", value := .decimal }
  , { walsCode := "lak", iso := "lbe", value := .decimal }
  , { walsCode := "lkt", iso := "lkt", value := .decimal }
  , { walsCode := "lan", iso := "laj", value := .decimal }
  , { walsCode := "lat", iso := "lav", value := .decimal }
  , { walsCode := "lav", iso := "lvk", value := .decimal }
  , { walsCode := "leg", iso := "lea", value := .decimal }
  , { walsCode := "lez", iso := "lez", value := .hybridVigesimalDecimal }
  , { walsCode := "ara", iso := "arw", value := .pureVigesimal }
  , { walsCode := "luv", iso := "lue", value := .decimal }
  , { walsCode := "mal", iso := "plt", value := .decimal }
  , { walsCode := "mnd", iso := "cmn", value := .decimal }
  , { walsCode := "mmb", iso := "mna", value := .pureVigesimal }
  , { walsCode := "myi", iso := "mpc", value := .restricted }
  , { walsCode := "mao", iso := "mri", value := .decimal }
  , { walsCode := "map", iso := "arn", value := .decimal }
  , { walsCode := "mrt", iso := "vma", value := .restricted }
  , { walsCode := "msl", iso := "mls", value := .decimal }
  , { walsCode := "mei", iso := "mni", value := .hybridVigesimalDecimal }
  , { walsCode := "mxa", iso := "mib", value := .hybridVigesimalDecimal }
  , { walsCode := "mxc", iso := "mig", value := .hybridVigesimalDecimal }
  , { walsCode := "nsz", iso := "azz", value := .hybridVigesimalDecimal }
  , { walsCode := "nht", iso := "nhg", value := .decimal }
  , { walsCode := "kho", iso := "naq", value := .decimal }
  , { walsCode := "nav", iso := "nav", value := .decimal }
  , { walsCode := "ndy", iso := "djk", value := .decimal }
  , { walsCode := "ntu", iso := "yrk", value := .decimal }
  , { walsCode := "nez", iso := "nez", value := .decimal }
  , { walsCode := "nti", iso := "niy", value := .otherBase }
  , { walsCode := "niv", iso := "niv", value := .decimal }
  , { walsCode := "nko", iso := "cgg", value := .decimal }
  , { walsCode := "noo", iso := "snf", value := .decimal }
  , { walsCode := "nbd", iso := "dgl", value := .decimal }
  , { walsCode := "ond", iso := "one", value := .decimal }
  , { walsCode := "orh", iso := "hae", value := .decimal }
  , { walsCode := "otm", iso := "ote", value := .hybridVigesimalDecimal }
  , { walsCode := "pai", iso := "pwn", value := .decimal }
  , { walsCode := "prs", iso := "pes", value := .decimal }
  , { walsCode := "prh", iso := "myp", value := .restricted }
  , { walsCode := "pit", iso := "pjt", value := .restricted }
  , { walsCode := "poh", iso := "pon", value := .decimal }
  , { walsCode := "pme", iso := "peb", value := .decimal }
  , { walsCode := "qim", iso := "qvi", value := .decimal }
  , { walsCode := "qui", iso := "qui", value := .decimal }
  , { walsCode := "ram", iso := "rma", value := .restricted }
  , { walsCode := "rap", iso := "rap", value := .decimal }
  , { walsCode := "rus", iso := "rus", value := .decimal }
  , { walsCode := "sah", iso := "saj", value := .decimal }
  , { walsCode := "san", iso := "sag", value := .decimal }
  , { walsCode := "sap", iso := "spu", value := .decimal }
  , { walsCode := "sla", iso := "den", value := .decimal }
  , { walsCode := "so", iso := "teu", value := .decimal }
  , { walsCode := "sou", iso := "hsb", value := .decimal }
  , { walsCode := "spa", iso := "spa", value := .decimal }
  , { walsCode := "sup", iso := "spp", value := .otherBase }
  , { walsCode := "swa", iso := "swh", value := .decimal }
  , { walsCode := "tab", iso := "mky", value := .decimal }
  , { walsCode := "tag", iso := "tgl", value := .decimal }
  , { walsCode := "tam", iso := "taj", value := .pureVigesimal }
  , { walsCode := "twe", iso := "tac", value := .decimal }
  , { walsCode := "taw", iso := "tbo", value := .pureVigesimal }
  , { walsCode := "tel", iso := "tel", value := .decimal }
  , { walsCode := "tha", iso := "tha", value := .decimal }
  , { walsCode := "tli", iso := "tli", value := .decimal }
  , { walsCode := "tms", iso := "dto", value := .otherBase }
  , { walsCode := "tsz", iso := "ddo", value := .hybridVigesimalDecimal }
  , { walsCode := "tug", iso := "thv", value := .decimal }
  , { walsCode := "tuk", iso := "", value := .decimal }
  , { walsCode := "tur", iso := "tur", value := .decimal }
  , { walsCode := "una", iso := "mtg", value := .extendedBodyPartSystem }
  , { walsCode := "vie", iso := "vie", value := .decimal }
  , { walsCode := "wra", iso := "wba", value := .pureVigesimal }
  , { walsCode := "war", iso := "pav", value := .restricted }
  , { walsCode := "wsk", iso := "wsk", value := .restricted }
  , { walsCode := "wch", iso := "mzh", value := .restricted }
  , { walsCode := "yag", iso := "yad", value := .decimal }
  , { walsCode := "ykt", iso := "sah", value := .decimal }
  , { walsCode := "yaq", iso := "yaq", value := .hybridVigesimalDecimal }
  , { walsCode := "yid", iso := "yii", value := .restricted }
  , { walsCode := "yim", iso := "yee", value := .pureVigesimal }
  , { walsCode := "yor", iso := "yor", value := .pureVigesimal }
  , { walsCode := "yct", iso := "yua", value := .pureVigesimal }
  , { walsCode := "yko", iso := "yux", value := .decimal }
  , { walsCode := "ypk", iso := "esu", value := .pureVigesimal }
  , { walsCode := "zqc", iso := "zoc", value := .pureVigesimal }
  , { walsCode := "zul", iso := "zul", value := .decimal }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F131A
