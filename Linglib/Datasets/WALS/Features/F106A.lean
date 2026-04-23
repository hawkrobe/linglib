import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 106A: Reciprocal Constructions
@cite{maslova-nedjalkov-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 106A`.

Chapter 106, 175 languages.
-/

namespace Datasets.WALS.F106A

/-- WALS 106A values. -/
inductive ReciprocalType where
  /-- No reciprocal construction (16 languages). -/
  | noReciprocalConstruction
  /-- Distinct from reflexive (99 languages). -/
  | distinctFromReflexive
  /-- Mixed (16 languages). -/
  | mixed
  /-- Identical to reflexive (44 languages). -/
  | identicalToReflexive
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 106A dataset (175 languages). -/
def allData : List (Datapoint ReciprocalType) :=
  [ { walsCode := "abk", iso := "abk", value := .distinctFromReflexive }
  , { walsCode := "acg", iso := "aca", value := .distinctFromReflexive }
  , { walsCode := "ain", iso := "ain", value := .distinctFromReflexive }
  , { walsCode := "ame", iso := "aey", value := .noReciprocalConstruction }
  , { walsCode := "amu", iso := "ame", value := .distinctFromReflexive }
  , { walsCode := "anc", iso := "anc", value := .distinctFromReflexive }
  , { walsCode := "apu", iso := "apu", value := .distinctFromReflexive }
  , { walsCode := "aeg", iso := "arz", value := .distinctFromReflexive }
  , { walsCode := "arp", iso := "ape", value := .noReciprocalConstruction }
  , { walsCode := "asm", iso := "cns", value := .distinctFromReflexive }
  , { walsCode := "bag", iso := "bmi", value := .distinctFromReflexive }
  , { walsCode := "bam", iso := "bam", value := .distinctFromReflexive }
  , { walsCode := "bnw", iso := "bwi", value := .identicalToReflexive }
  , { walsCode := "bae", iso := "bae", value := .identicalToReflexive }
  , { walsCode := "bsq", iso := "eus", value := .distinctFromReflexive }
  , { walsCode := "bma", iso := "tzm", value := .distinctFromReflexive }
  , { walsCode := "bul", iso := "bul", value := .mixed }
  , { walsCode := "but", iso := "bxm", value := .distinctFromReflexive }
  , { walsCode := "brm", iso := "mya", value := .noReciprocalConstruction }
  , { walsCode := "bur", iso := "bsk", value := .distinctFromReflexive }
  , { walsCode := "cah", iso := "chl", value := .identicalToReflexive }
  , { walsCode := "cnt", iso := "yue", value := .distinctFromReflexive }
  , { walsCode := "csh", iso := "cbs", value := .distinctFromReflexive }
  , { walsCode := "cha", iso := "cha", value := .distinctFromReflexive }
  , { walsCode := "chc", iso := "che", value := .noReciprocalConstruction }
  , { walsCode := "chk", iso := "ckt", value := .distinctFromReflexive }
  , { walsCode := "cor", iso := "crn", value := .identicalToReflexive }
  , { walsCode := "cea", iso := "csw", value := .distinctFromReflexive }
  , { walsCode := "cup", iso := "cup", value := .identicalToReflexive }
  , { walsCode := "dni", iso := "dni", value := .noReciprocalConstruction }
  , { walsCode := "ygd", iso := "dur", value := .distinctFromReflexive }
  , { walsCode := "djr", iso := "ddj", value := .identicalToReflexive }
  , { walsCode := "eng", iso := "eng", value := .distinctFromReflexive }
  , { walsCode := "evn", iso := "eve", value := .distinctFromReflexive }
  , { walsCode := "eve", iso := "evn", value := .distinctFromReflexive }
  , { walsCode := "fij", iso := "fij", value := .distinctFromReflexive }
  , { walsCode := "fin", iso := "fin", value := .distinctFromReflexive }
  , { walsCode := "fre", iso := "fra", value := .mixed }
  , { walsCode := "fue", iso := "fud", value := .distinctFromReflexive }
  , { walsCode := "gbb", iso := "gbp", value := .distinctFromReflexive }
  , { walsCode := "geo", iso := "kat", value := .distinctFromReflexive }
  , { walsCode := "ger", iso := "deu", value := .mixed }
  , { walsCode := "gim", iso := "bcq", value := .identicalToReflexive }
  , { walsCode := "goa", iso := "guc", value := .distinctFromReflexive }
  , { walsCode := "gdi", iso := "god", value := .noReciprocalConstruction }
  , { walsCode := "goo", iso := "gni", value := .identicalToReflexive }
  , { walsCode := "grb", iso := "grj", value := .distinctFromReflexive }
  , { walsCode := "grk", iso := "ell", value := .mixed }
  , { walsCode := "grw", iso := "kal", value := .identicalToReflexive }
  , { walsCode := "gua", iso := "gug", value := .distinctFromReflexive }
  , { walsCode := "hau", iso := "hau", value := .distinctFromReflexive }
  , { walsCode := "heb", iso := "heb", value := .mixed }
  , { walsCode := "hin", iso := "hin", value := .distinctFromReflexive }
  , { walsCode := "hix", iso := "hix", value := .mixed }
  , { walsCode := "hmo", iso := "hnj", value := .distinctFromReflexive }
  , { walsCode := "hop", iso := "hop", value := .mixed }
  , { walsCode := "hui", iso := "hch", value := .identicalToReflexive }
  , { walsCode := "ign", iso := "ign", value := .distinctFromReflexive }
  , { walsCode := "ika", iso := "arh", value := .identicalToReflexive }
  , { walsCode := "imo", iso := "imn", value := .identicalToReflexive }
  , { walsCode := "ind", iso := "ind", value := .distinctFromReflexive }
  , { walsCode := "ite", iso := "itl", value := .distinctFromReflexive }
  , { walsCode := "jak", iso := "jac", value := .identicalToReflexive }
  , { walsCode := "jpn", iso := "jpn", value := .distinctFromReflexive }
  , { walsCode := "kab", iso := "kbd", value := .distinctFromReflexive }
  , { walsCode := "kng", iso := "kgp", value := .identicalToReflexive }
  , { walsCode := "knd", iso := "kan", value := .distinctFromReflexive }
  , { walsCode := "krc", iso := "krc", value := .distinctFromReflexive }
  , { walsCode := "jva", iso := "kpj", value := .distinctFromReflexive }
  , { walsCode := "krk", iso := "kyh", value := .distinctFromReflexive }
  , { walsCode := "kws", iso := "xaw", value := .identicalToReflexive }
  , { walsCode := "kyp", iso := "txu", value := .distinctFromReflexive }
  , { walsCode := "kay", iso := "gyd", value := .distinctFromReflexive }
  , { walsCode := "kew", iso := "kew", value := .noReciprocalConstruction }
  , { walsCode := "kha", iso := "khk", value := .distinctFromReflexive }
  , { walsCode := "kio", iso := "kio", value := .identicalToReflexive }
  , { walsCode := "kgz", iso := "kir", value := .distinctFromReflexive }
  , { walsCode := "koa", iso := "cku", value := .distinctFromReflexive }
  , { walsCode := "kor", iso := "kor", value := .distinctFromReflexive }
  , { walsCode := "kse", iso := "ses", value := .distinctFromReflexive }
  , { walsCode := "kro", iso := "kgo", value := .identicalToReflexive }
  , { walsCode := "kut", iso := "kut", value := .distinctFromReflexive }
  , { walsCode := "lkt", iso := "lkt", value := .distinctFromReflexive }
  , { walsCode := "lan", iso := "laj", value := .identicalToReflexive }
  , { walsCode := "lrd", iso := "lbz", value := .distinctFromReflexive }
  , { walsCode := "lit", iso := "lit", value := .mixed }
  , { walsCode := "lui", iso := "lui", value := .identicalToReflexive }
  , { walsCode := "luv", iso := "lue", value := .identicalToReflexive }
  , { walsCode := "lye", iso := "lee", value := .distinctFromReflexive }
  , { walsCode := "mne", iso := "nmu", value := .distinctFromReflexive }
  , { walsCode := "mal", iso := "plt", value := .distinctFromReflexive }
  , { walsCode := "mam", iso := "mam", value := .noReciprocalConstruction }
  , { walsCode := "mnd", iso := "cmn", value := .distinctFromReflexive }
  , { walsCode := "myi", iso := "mpc", value := .identicalToReflexive }
  , { walsCode := "map", iso := "arn", value := .identicalToReflexive }
  , { walsCode := "mku", iso := "zmr", value := .distinctFromReflexive }
  , { walsCode := "mar", iso := "mrc", value := .identicalToReflexive }
  , { walsCode := "mrt", iso := "vma", value := .distinctFromReflexive }
  , { walsCode := "mau", iso := "mph", value := .identicalToReflexive }
  , { walsCode := "max", iso := "mbl", value := .identicalToReflexive }
  , { walsCode := "may", iso := "ayz", value := .noReciprocalConstruction }
  , { walsCode := "mei", iso := "mni", value := .distinctFromReflexive }
  , { walsCode := "mno", iso := "mnr", value := .distinctFromReflexive }
  , { walsCode := "mud", iso := "mnf", value := .identicalToReflexive }
  , { walsCode := "mun", iso := "unr", value := .distinctFromReflexive }
  , { walsCode := "kho", iso := "naq", value := .distinctFromReflexive }
  , { walsCode := "nel", iso := "nee", value := .distinctFromReflexive }
  , { walsCode := "ngi", iso := "wyb", value := .distinctFromReflexive }
  , { walsCode := "niv", iso := "niv", value := .distinctFromReflexive }
  , { walsCode := "nko", iso := "cgg", value := .distinctFromReflexive }
  , { walsCode := "nom", iso := "not", value := .distinctFromReflexive }
  , { walsCode := "nug", iso := "nuy", value := .distinctFromReflexive }
  , { walsCode := "ood", iso := "ood", value := .mixed }
  , { walsCode := "ojm", iso := "ciw", value := .distinctFromReflexive }
  , { walsCode := "ond", iso := "one", value := .identicalToReflexive }
  , { walsCode := "orh", iso := "hae", value := .distinctFromReflexive }
  , { walsCode := "otm", iso := "ote", value := .noReciprocalConstruction }
  , { walsCode := "pno", iso := "pao", value := .mixed }
  , { walsCode := "put", iso := "ute", value := .identicalToReflexive }
  , { walsCode := "prs", iso := "pes", value := .distinctFromReflexive }
  , { walsCode := "prh", iso := "myp", value := .noReciprocalConstruction }
  , { walsCode := "pir", iso := "pib", value := .distinctFromReflexive }
  , { walsCode := "pol", iso := "pol", value := .mixed }
  , { walsCode := "pso", iso := "pom", value := .distinctFromReflexive }
  , { walsCode := "qbo", iso := "", value := .distinctFromReflexive }
  , { walsCode := "qcu", iso := "quz", value := .distinctFromReflexive }
  , { walsCode := "qhu", iso := "qub", value := .identicalToReflexive }
  , { walsCode := "qim", iso := "qvi", value := .mixed }
  , { walsCode := "ram", iso := "rma", value := .noReciprocalConstruction }
  , { walsCode := "rap", iso := "rap", value := .identicalToReflexive }
  , { walsCode := "rus", iso := "rus", value := .mixed }
  , { walsCode := "san", iso := "sag", value := .noReciprocalConstruction }
  , { walsCode := "snm", iso := "xsu", value := .distinctFromReflexive }
  , { walsCode := "srr", iso := "ser", value := .identicalToReflexive }
  , { walsCode := "sho", iso := "shh", value := .identicalToReflexive }
  , { walsCode := "sla", iso := "den", value := .distinctFromReflexive }
  , { walsCode := "spa", iso := "spa", value := .mixed }
  , { walsCode := "sup", iso := "spp", value := .identicalToReflexive }
  , { walsCode := "sur", iso := "sgz", value := .mixed }
  , { walsCode := "swa", iso := "swh", value := .distinctFromReflexive }
  , { walsCode := "tag", iso := "tgl", value := .distinctFromReflexive }
  , { walsCode := "tml", iso := "tam", value := .distinctFromReflexive }
  , { walsCode := "tce", iso := "tar", value := .distinctFromReflexive }
  , { walsCode := "tar", iso := "tae", value := .mixed }
  , { walsCode := "tpc", iso := "tep", value := .noReciprocalConstruction }
  , { walsCode := "tha", iso := "tha", value := .distinctFromReflexive }
  , { walsCode := "tiw", iso := "tiw", value := .distinctFromReflexive }
  , { walsCode := "toq", iso := "mlu", value := .identicalToReflexive }
  , { walsCode := "tuc", iso := "tuo", value := .distinctFromReflexive }
  , { walsCode := "tuk", iso := "", value := .distinctFromReflexive }
  , { walsCode := "tur", iso := "tur", value := .distinctFromReflexive }
  , { walsCode := "tuv", iso := "tyv", value := .distinctFromReflexive }
  , { walsCode := "tbb", iso := "tub", value := .distinctFromReflexive }
  , { walsCode := "vie", iso := "vie", value := .distinctFromReflexive }
  , { walsCode := "wam", iso := "wmb", value := .identicalToReflexive }
  , { walsCode := "wra", iso := "wba", value := .identicalToReflexive }
  , { walsCode := "wrk", iso := "gae", value := .identicalToReflexive }
  , { walsCode := "war", iso := "pav", value := .identicalToReflexive }
  , { walsCode := "wgu", iso := "wrg", value := .distinctFromReflexive }
  , { walsCode := "wur", iso := "wau", value := .distinctFromReflexive }
  , { walsCode := "wic", iso := "wic", value := .noReciprocalConstruction }
  , { walsCode := "wch", iso := "mzh", value := .identicalToReflexive }
  , { walsCode := "win", iso := "wnw", value := .distinctFromReflexive }
  , { walsCode := "xer", iso := "xer", value := .identicalToReflexive }
  , { walsCode := "xok", iso := "xok", value := .distinctFromReflexive }
  , { walsCode := "yag", iso := "yad", value := .identicalToReflexive }
  , { walsCode := "ykt", iso := "sah", value := .distinctFromReflexive }
  , { walsCode := "ynk", iso := "kdd", value := .identicalToReflexive }
  , { walsCode := "yaq", iso := "yaq", value := .identicalToReflexive }
  , { walsCode := "yid", iso := "yii", value := .noReciprocalConstruction }
  , { walsCode := "yor", iso := "yor", value := .identicalToReflexive }
  , { walsCode := "yko", iso := "yux", value := .distinctFromReflexive }
  , { walsCode := "ytu", iso := "ykg", value := .distinctFromReflexive }
  , { walsCode := "yuk", iso := "gcd", value := .distinctFromReflexive }
  , { walsCode := "zul", iso := "zul", value := .distinctFromReflexive }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F106A
