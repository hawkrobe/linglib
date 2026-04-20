import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 115A: Negative Indefinite Pronouns and Predicate Negation
@cite{haspelmath-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 115A`.

Chapter 115, 206 languages.
-/

namespace Core.WALS.F115A

/-- WALS 115A values. -/
inductive NegativeIndefiniteType where
  /-- Predicate negation also present (170 languages). -/
  | predicateNegationAlsoPresent
  /-- No predicate negation (11 languages). -/
  | noPredicateNegation
  /-- Mixed behaviour (13 languages). -/
  | mixedBehaviour
  /-- Negative existential construction (12 languages). -/
  | negativeExistentialConstruction
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 115A dataset (206 languages). -/
def allData : List (Datapoint NegativeIndefiniteType) :=
  [ { walsCode := "abk", iso := "abk", value := .predicateNegationAlsoPresent }
  , { walsCode := "abu", iso := "kgr", value := .predicateNegationAlsoPresent }
  , { walsCode := "ace", iso := "ace", value := .predicateNegationAlsoPresent }
  , { walsCode := "ady", iso := "ady", value := .predicateNegationAlsoPresent }
  , { walsCode := "ain", iso := "ain", value := .predicateNegationAlsoPresent }
  , { walsCode := "ano", iso := "nun", value := .predicateNegationAlsoPresent }
  , { walsCode := "aeg", iso := "arz", value := .predicateNegationAlsoPresent }
  , { walsCode := "ana", iso := "aro", value := .predicateNegationAlsoPresent }
  , { walsCode := "ass", iso := "asm", value := .predicateNegationAlsoPresent }
  , { walsCode := "awp", iso := "kwi", value := .predicateNegationAlsoPresent }
  , { walsCode := "bab", iso := "bav", value := .predicateNegationAlsoPresent }
  , { walsCode := "bag", iso := "bmi", value := .predicateNegationAlsoPresent }
  , { walsCode := "brs", iso := "bsn", value := .negativeExistentialConstruction }
  , { walsCode := "bae", iso := "bae", value := .predicateNegationAlsoPresent }
  , { walsCode := "bsq", iso := "eus", value := .predicateNegationAlsoPresent }
  , { walsCode := "bkr", iso := "btx", value := .predicateNegationAlsoPresent }
  , { walsCode := "baw", iso := "bgr", value := .predicateNegationAlsoPresent }
  , { walsCode := "bma", iso := "tzm", value := .predicateNegationAlsoPresent }
  , { walsCode := "bbw", iso := "gup", value := .predicateNegationAlsoPresent }
  , { walsCode := "biu", iso := "", value := .predicateNegationAlsoPresent }
  , { walsCode := "boz", iso := "boz", value := .predicateNegationAlsoPresent }
  , { walsCode := "brh", iso := "brh", value := .predicateNegationAlsoPresent }
  , { walsCode := "bud", iso := "bdm", value := .predicateNegationAlsoPresent }
  , { walsCode := "bul", iso := "bul", value := .predicateNegationAlsoPresent }
  , { walsCode := "brm", iso := "mya", value := .predicateNegationAlsoPresent }
  , { walsCode := "cnl", iso := "ram", value := .predicateNegationAlsoPresent }
  , { walsCode := "cnt", iso := "yue", value := .predicateNegationAlsoPresent }
  , { walsCode := "ctl", iso := "cat", value := .predicateNegationAlsoPresent }
  , { walsCode := "cha", iso := "cha", value := .noPredicateNegation }
  , { walsCode := "chn", iso := "chx", value := .predicateNegationAlsoPresent }
  , { walsCode := "cch", iso := "coz", value := .noPredicateNegation }
  , { walsCode := "chk", iso := "ckt", value := .predicateNegationAlsoPresent }
  , { walsCode := "coo", iso := "csz", value := .predicateNegationAlsoPresent }
  , { walsCode := "cop", iso := "cop", value := .predicateNegationAlsoPresent }
  , { walsCode := "dgr", iso := "dta", value := .predicateNegationAlsoPresent }
  , { walsCode := "dji", iso := "jig", value := .predicateNegationAlsoPresent }
  , { walsCode := "dut", iso := "nld", value := .noPredicateNegation }
  , { walsCode := "eng", iso := "eng", value := .mixedBehaviour }
  , { walsCode := "epe", iso := "sja", value := .predicateNegationAlsoPresent }
  , { walsCode := "eve", iso := "evn", value := .predicateNegationAlsoPresent }
  , { walsCode := "fin", iso := "fin", value := .predicateNegationAlsoPresent }
  , { walsCode := "fon", iso := "fon", value := .predicateNegationAlsoPresent }
  , { walsCode := "fre", iso := "fra", value := .mixedBehaviour }
  , { walsCode := "fue", iso := "fud", value := .negativeExistentialConstruction }
  , { walsCode := "geo", iso := "kat", value := .mixedBehaviour }
  , { walsCode := "ger", iso := "deu", value := .noPredicateNegation }
  , { walsCode := "goo", iso := "gni", value := .predicateNegationAlsoPresent }
  , { walsCode := "grk", iso := "ell", value := .predicateNegationAlsoPresent }
  , { walsCode := "grw", iso := "kal", value := .predicateNegationAlsoPresent }
  , { walsCode := "gua", iso := "gug", value := .predicateNegationAlsoPresent }
  , { walsCode := "guj", iso := "guj", value := .predicateNegationAlsoPresent }
  , { walsCode := "grg", iso := "gge", value := .predicateNegationAlsoPresent }
  , { walsCode := "hai", iso := "hai", value := .predicateNegationAlsoPresent }
  , { walsCode := "hau", iso := "hau", value := .predicateNegationAlsoPresent }
  , { walsCode := "heb", iso := "heb", value := .predicateNegationAlsoPresent }
  , { walsCode := "hin", iso := "hin", value := .predicateNegationAlsoPresent }
  , { walsCode := "hmo", iso := "hnj", value := .predicateNegationAlsoPresent }
  , { walsCode := "hun", iso := "hun", value := .predicateNegationAlsoPresent }
  , { walsCode := "hzb", iso := "huz", value := .predicateNegationAlsoPresent }
  , { walsCode := "ice", iso := "isl", value := .mixedBehaviour }
  , { walsCode := "ind", iso := "ind", value := .predicateNegationAlsoPresent }
  , { walsCode := "irq", iso := "irk", value := .negativeExistentialConstruction }
  , { walsCode := "iri", iso := "gle", value := .predicateNegationAlsoPresent }
  , { walsCode := "ita", iso := "ita", value := .mixedBehaviour }
  , { walsCode := "itz", iso := "itz", value := .mixedBehaviour }
  , { walsCode := "jam", iso := "djd", value := .predicateNegationAlsoPresent }
  , { walsCode := "jpn", iso := "jpn", value := .predicateNegationAlsoPresent }
  , { walsCode := "jel", iso := "jek", value := .predicateNegationAlsoPresent }
  , { walsCode := "kma", iso := "kay", value := .predicateNegationAlsoPresent }
  , { walsCode := "kan", iso := "ogo", value := .predicateNegationAlsoPresent }
  , { walsCode := "knd", iso := "kan", value := .predicateNegationAlsoPresent }
  , { walsCode := "knr", iso := "knc", value := .predicateNegationAlsoPresent }
  , { walsCode := "kkp", iso := "kaa", value := .predicateNegationAlsoPresent }
  , { walsCode := "kas", iso := "kas", value := .predicateNegationAlsoPresent }
  , { walsCode := "kaz", iso := "kaz", value := .predicateNegationAlsoPresent }
  , { walsCode := "ker", iso := "ker", value := .predicateNegationAlsoPresent }
  , { walsCode := "ket", iso := "ket", value := .predicateNegationAlsoPresent }
  , { walsCode := "kmh", iso := "kjl", value := .predicateNegationAlsoPresent }
  , { walsCode := "kty", iso := "kca", value := .predicateNegationAlsoPresent }
  , { walsCode := "khs", iso := "kha", value := .predicateNegationAlsoPresent }
  , { walsCode := "khm", iso := "khm", value := .predicateNegationAlsoPresent }
  , { walsCode := "kmu", iso := "kjg", value := .predicateNegationAlsoPresent }
  , { walsCode := "klv", iso := "kij", value := .predicateNegationAlsoPresent }
  , { walsCode := "kio", iso := "kio", value := .predicateNegationAlsoPresent }
  , { walsCode := "koa", iso := "cku", value := .predicateNegationAlsoPresent }
  , { walsCode := "kob", iso := "kpw", value := .predicateNegationAlsoPresent }
  , { walsCode := "kod", iso := "kfa", value := .predicateNegationAlsoPresent }
  , { walsCode := "kzy", iso := "kpv", value := .predicateNegationAlsoPresent }
  , { walsCode := "kor", iso := "kor", value := .predicateNegationAlsoPresent }
  , { walsCode := "kku", iso := "kfq", value := .predicateNegationAlsoPresent }
  , { walsCode := "kfe", iso := "kfz", value := .predicateNegationAlsoPresent }
  , { walsCode := "kse", iso := "ses", value := .predicateNegationAlsoPresent }
  , { walsCode := "kug", iso := "cmn", value := .predicateNegationAlsoPresent }
  , { walsCode := "lak", iso := "lbe", value := .predicateNegationAlsoPresent }
  , { walsCode := "lkt", iso := "lkt", value := .predicateNegationAlsoPresent }
  , { walsCode := "lan", iso := "laj", value := .negativeExistentialConstruction }
  , { walsCode := "lat", iso := "lav", value := .predicateNegationAlsoPresent }
  , { walsCode := "lav", iso := "lvk", value := .predicateNegationAlsoPresent }
  , { walsCode := "lel", iso := "lln", value := .predicateNegationAlsoPresent }
  , { walsCode := "lez", iso := "lez", value := .predicateNegationAlsoPresent }
  , { walsCode := "lil", iso := "lil", value := .predicateNegationAlsoPresent }
  , { walsCode := "lin", iso := "lin", value := .predicateNegationAlsoPresent }
  , { walsCode := "lit", iso := "lit", value := .predicateNegationAlsoPresent }
  , { walsCode := "mad", iso := "mhi", value := .predicateNegationAlsoPresent }
  , { walsCode := "mle", iso := "mdy", value := .predicateNegationAlsoPresent }
  , { walsCode := "mac", iso := "mbc", value := .predicateNegationAlsoPresent }
  , { walsCode := "mym", iso := "mal", value := .predicateNegationAlsoPresent }
  , { walsCode := "mlg", iso := "", value := .mixedBehaviour }
  , { walsCode := "mlt", iso := "mlt", value := .mixedBehaviour }
  , { walsCode := "mto", iso := "kmj", value := .predicateNegationAlsoPresent }
  , { walsCode := "mnd", iso := "cmn", value := .predicateNegationAlsoPresent }
  , { walsCode := "myi", iso := "mpc", value := .noPredicateNegation }
  , { walsCode := "mao", iso := "mri", value := .predicateNegationAlsoPresent }
  , { walsCode := "map", iso := "arn", value := .predicateNegationAlsoPresent }
  , { walsCode := "mhi", iso := "mar", value := .predicateNegationAlsoPresent }
  , { walsCode := "mme", iso := "mhr", value := .predicateNegationAlsoPresent }
  , { walsCode := "may", iso := "ayz", value := .predicateNegationAlsoPresent }
  , { walsCode := "mby", iso := "myb", value := .predicateNegationAlsoPresent }
  , { walsCode := "mbi", iso := "baw", value := .predicateNegationAlsoPresent }
  , { walsCode := "mxc", iso := "mig", value := .noPredicateNegation }
  , { walsCode := "miy", iso := "mkf", value := .predicateNegationAlsoPresent }
  , { walsCode := "mcv", iso := "moc", value := .negativeExistentialConstruction }
  , { walsCode := "moe", iso := "myv", value := .predicateNegationAlsoPresent }
  , { walsCode := "mos", iso := "cas", value := .predicateNegationAlsoPresent }
  , { walsCode := "mdg", iso := "mua", value := .predicateNegationAlsoPresent }
  , { walsCode := "mun", iso := "unr", value := .predicateNegationAlsoPresent }
  , { walsCode := "mgu", iso := "mug", value := .predicateNegationAlsoPresent }
  , { walsCode := "nht", iso := "nhg", value := .noPredicateNegation }
  , { walsCode := "nai", iso := "gld", value := .predicateNegationAlsoPresent }
  , { walsCode := "nav", iso := "nav", value := .predicateNegationAlsoPresent }
  , { walsCode := "ndj", iso := "djj", value := .predicateNegationAlsoPresent }
  , { walsCode := "nel", iso := "nee", value := .negativeExistentialConstruction }
  , { walsCode := "nep", iso := "npi", value := .predicateNegationAlsoPresent }
  , { walsCode := "nwd", iso := "new", value := .predicateNegationAlsoPresent }
  , { walsCode := "nti", iso := "niy", value := .predicateNegationAlsoPresent }
  , { walsCode := "ngi", iso := "wyb", value := .predicateNegationAlsoPresent }
  , { walsCode := "niu", iso := "niu", value := .predicateNegationAlsoPresent }
  , { walsCode := "niv", iso := "niv", value := .predicateNegationAlsoPresent }
  , { walsCode := "nko", iso := "cgg", value := .negativeExistentialConstruction }
  , { walsCode := "nua", iso := "nxl", value := .predicateNegationAlsoPresent }
  , { walsCode := "ood", iso := "ood", value := .predicateNegationAlsoPresent }
  , { walsCode := "oji", iso := "", value := .predicateNegationAlsoPresent }
  , { walsCode := "orh", iso := "hae", value := .predicateNegationAlsoPresent }
  , { walsCode := "oss", iso := "oss", value := .noPredicateNegation }
  , { walsCode := "pms", iso := "pma", value := .predicateNegationAlsoPresent }
  , { walsCode := "pno", iso := "pao", value := .predicateNegationAlsoPresent }
  , { walsCode := "pai", iso := "pwn", value := .predicateNegationAlsoPresent }
  , { walsCode := "prs", iso := "pes", value := .predicateNegationAlsoPresent }
  , { walsCode := "pol", iso := "pol", value := .predicateNegationAlsoPresent }
  , { walsCode := "pop", iso := "pbe", value := .predicateNegationAlsoPresent }
  , { walsCode := "por", iso := "por", value := .mixedBehaviour }
  , { walsCode := "pur", iso := "tsz", value := .noPredicateNegation }
  , { walsCode := "pae", iso := "pbb", value := .predicateNegationAlsoPresent }
  , { walsCode := "qia", iso := "", value := .predicateNegationAlsoPresent }
  , { walsCode := "qhu", iso := "qub", value := .predicateNegationAlsoPresent }
  , { walsCode := "qim", iso := "qvi", value := .predicateNegationAlsoPresent }
  , { walsCode := "raw", iso := "raw", value := .predicateNegationAlsoPresent }
  , { walsCode := "ret", iso := "tnc", value := .predicateNegationAlsoPresent }
  , { walsCode := "rom", iso := "ron", value := .predicateNegationAlsoPresent }
  , { walsCode := "rus", iso := "rus", value := .predicateNegationAlsoPresent }
  , { walsCode := "sno", iso := "sme", value := .predicateNegationAlsoPresent }
  , { walsCode := "skp", iso := "sel", value := .predicateNegationAlsoPresent }
  , { walsCode := "scr", iso := "hbs", value := .predicateNegationAlsoPresent }
  , { walsCode := "shk", iso := "shp", value := .predicateNegationAlsoPresent }
  , { walsCode := "sla", iso := "den", value := .predicateNegationAlsoPresent }
  , { walsCode := "som", iso := "som", value := .predicateNegationAlsoPresent }
  , { walsCode := "spa", iso := "spa", value := .mixedBehaviour }
  , { walsCode := "squ", iso := "squ", value := .predicateNegationAlsoPresent }
  , { walsCode := "sup", iso := "spp", value := .predicateNegationAlsoPresent }
  , { walsCode := "swa", iso := "swh", value := .predicateNegationAlsoPresent }
  , { walsCode := "swe", iso := "swe", value := .mixedBehaviour }
  , { walsCode := "tab", iso := "mky", value := .mixedBehaviour }
  , { walsCode := "tag", iso := "tgl", value := .predicateNegationAlsoPresent }
  , { walsCode := "tah", iso := "tah", value := .negativeExistentialConstruction }
  , { walsCode := "tam", iso := "taj", value := .predicateNegationAlsoPresent }
  , { walsCode := "tml", iso := "tam", value := .predicateNegationAlsoPresent }
  , { walsCode := "teo", iso := "tio", value := .negativeExistentialConstruction }
  , { walsCode := "tpn", iso := "ntp", value := .predicateNegationAlsoPresent }
  , { walsCode := "trb", iso := "tfr", value := .predicateNegationAlsoPresent }
  , { walsCode := "ttn", iso := "tet", value := .predicateNegationAlsoPresent }
  , { walsCode := "tha", iso := "tha", value := .predicateNegationAlsoPresent }
  , { walsCode := "tid", iso := "tvo", value := .predicateNegationAlsoPresent }
  , { walsCode := "tja", iso := "dih", value := .predicateNegationAlsoPresent }
  , { walsCode := "tiw", iso := "tiw", value := .noPredicateNegation }
  , { walsCode := "tke", iso := "tkl", value := .negativeExistentialConstruction }
  , { walsCode := "tms", iso := "dto", value := .predicateNegationAlsoPresent }
  , { walsCode := "tru", iso := "tpy", value := .predicateNegationAlsoPresent }
  , { walsCode := "tur", iso := "tur", value := .predicateNegationAlsoPresent }
  , { walsCode := "tvl", iso := "tvl", value := .negativeExistentialConstruction }
  , { walsCode := "tuv", iso := "tyv", value := .predicateNegationAlsoPresent }
  , { walsCode := "tzu", iso := "tzj", value := .noPredicateNegation }
  , { walsCode := "udh", iso := "ude", value := .predicateNegationAlsoPresent }
  , { walsCode := "udm", iso := "udm", value := .predicateNegationAlsoPresent }
  , { walsCode := "uku", iso := "kuu", value := .negativeExistentialConstruction }
  , { walsCode := "urk", iso := "urb", value := .predicateNegationAlsoPresent }
  , { walsCode := "vie", iso := "vie", value := .predicateNegationAlsoPresent }
  , { walsCode := "wch", iso := "mzh", value := .predicateNegationAlsoPresent }
  , { walsCode := "wlf", iso := "wol", value := .predicateNegationAlsoPresent }
  , { walsCode := "ykt", iso := "sah", value := .predicateNegationAlsoPresent }
  , { walsCode := "yaq", iso := "yaq", value := .mixedBehaviour }
  , { walsCode := "yko", iso := "yux", value := .predicateNegationAlsoPresent }
  , { walsCode := "ytu", iso := "ykg", value := .predicateNegationAlsoPresent }
  , { walsCode := "zaq", iso := "zpi", value := .predicateNegationAlsoPresent }
  , { walsCode := "zaz", iso := "diq", value := .predicateNegationAlsoPresent }
  , { walsCode := "zul", iso := "zul", value := .predicateNegationAlsoPresent }
  , { walsCode := "zun", iso := "zun", value := .predicateNegationAlsoPresent }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F115A
