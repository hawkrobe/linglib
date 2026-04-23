import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 109B: Other Roles of Applied Objects
@cite{polinsky-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 109B`.

Chapter 109, 183 languages.
-/

namespace Datasets.WALS.F109B

/-- WALS 109B values. -/
inductive AppliedObjectRole where
  /-- Instrument (17 languages). -/
  | instrument
  /-- Locative (18 languages). -/
  | locative
  /-- Instrument and locative (12 languages). -/
  | instrumentAndLocative
  /-- No other roles (= Only benefactive) (36 languages). -/
  | onlyBenefactive
  /-- No applicative construction (100 languages). -/
  | noApplicative
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 109B dataset (183 languages). -/
def allData : List (Datapoint AppliedObjectRole) :=
  [ { walsCode := "abz", iso := "abq", value := .instrumentAndLocative }
  , { walsCode := "abk", iso := "abk", value := .instrument }
  , { walsCode := "aco", iso := "kjq", value := .onlyBenefactive }
  , { walsCode := "ain", iso := "ain", value := .instrumentAndLocative }
  , { walsCode := "ala", iso := "amp", value := .onlyBenefactive }
  , { walsCode := "ame", iso := "aey", value := .onlyBenefactive }
  , { walsCode := "apu", iso := "apu", value := .noApplicative }
  , { walsCode := "aeg", iso := "arz", value := .noApplicative }
  , { walsCode := "arp", iso := "ape", value := .locative }
  , { walsCode := "arc", iso := "aqc", value := .noApplicative }
  , { walsCode := "arm", iso := "hye", value := .noApplicative }
  , { walsCode := "asm", iso := "cns", value := .onlyBenefactive }
  , { walsCode := "awp", iso := "kwi", value := .noApplicative }
  , { walsCode := "bag", iso := "bmi", value := .noApplicative }
  , { walsCode := "brs", iso := "bsn", value := .noApplicative }
  , { walsCode := "bsq", iso := "eus", value := .noApplicative }
  , { walsCode := "bma", iso := "tzm", value := .noApplicative }
  , { walsCode := "brh", iso := "brh", value := .noApplicative }
  , { walsCode := "brm", iso := "mya", value := .noApplicative }
  , { walsCode := "bur", iso := "bsk", value := .onlyBenefactive }
  , { walsCode := "cah", iso := "chl", value := .locative }
  , { walsCode := "cnl", iso := "ram", value := .noApplicative }
  , { walsCode := "chh", iso := "sgw", value := .onlyBenefactive }
  , { walsCode := "cha", iso := "cha", value := .onlyBenefactive }
  , { walsCode := "cic", iso := "nya", value := .instrumentAndLocative }
  , { walsCode := "chk", iso := "ckt", value := .noApplicative }
  , { walsCode := "cmn", iso := "com", value := .instrument }
  , { walsCode := "cre", iso := "crk", value := .onlyBenefactive }
  , { walsCode := "dag", iso := "dgz", value := .noApplicative }
  , { walsCode := "dni", iso := "dni", value := .locative }
  , { walsCode := "diy", iso := "dif", value := .locative }
  , { walsCode := "dji", iso := "jig", value := .noApplicative }
  , { walsCode := "dyi", iso := "dbl", value := .instrument }
  , { walsCode := "eng", iso := "eng", value := .noApplicative }
  , { walsCode := "epe", iso := "sja", value := .onlyBenefactive }
  , { walsCode := "eve", iso := "evn", value := .noApplicative }
  , { walsCode := "ewe", iso := "ewe", value := .noApplicative }
  , { walsCode := "fij", iso := "fij", value := .locative }
  , { walsCode := "fin", iso := "fin", value := .noApplicative }
  , { walsCode := "fre", iso := "fra", value := .noApplicative }
  , { walsCode := "gae", iso := "gla", value := .noApplicative }
  , { walsCode := "geo", iso := "kat", value := .locative }
  , { walsCode := "ger", iso := "deu", value := .noApplicative }
  , { walsCode := "god", iso := "gdo", value := .noApplicative }
  , { walsCode := "goo", iso := "gni", value := .noApplicative }
  , { walsCode := "grb", iso := "grj", value := .instrument }
  , { walsCode := "grk", iso := "ell", value := .noApplicative }
  , { walsCode := "grw", iso := "kal", value := .instrument }
  , { walsCode := "gua", iso := "gug", value := .noApplicative }
  , { walsCode := "hlu", iso := "hur", value := .onlyBenefactive }
  , { walsCode := "hau", iso := "hau", value := .locative }
  , { walsCode := "heb", iso := "heb", value := .noApplicative }
  , { walsCode := "hin", iso := "hin", value := .noApplicative }
  , { walsCode := "hix", iso := "hix", value := .noApplicative }
  , { walsCode := "hmo", iso := "hnj", value := .noApplicative }
  , { walsCode := "hun", iso := "hun", value := .noApplicative }
  , { walsCode := "hzb", iso := "huz", value := .noApplicative }
  , { walsCode := "ice", iso := "isl", value := .noApplicative }
  , { walsCode := "igb", iso := "ibo", value := .onlyBenefactive }
  , { walsCode := "ika", iso := "arh", value := .onlyBenefactive }
  , { walsCode := "imo", iso := "imn", value := .onlyBenefactive }
  , { walsCode := "ind", iso := "ind", value := .onlyBenefactive }
  , { walsCode := "ing", iso := "inh", value := .noApplicative }
  , { walsCode := "irq", iso := "irk", value := .noApplicative }
  , { walsCode := "jak", iso := "jac", value := .instrument }
  , { walsCode := "jpn", iso := "jpn", value := .noApplicative }
  , { walsCode := "juh", iso := "ktz", value := .locative }
  , { walsCode := "kam", iso := "xbr", value := .locative }
  , { walsCode := "knd", iso := "kan", value := .onlyBenefactive }
  , { walsCode := "knr", iso := "knc", value := .locative }
  , { walsCode := "krk", iso := "kyh", value := .instrument }
  , { walsCode := "kas", iso := "kas", value := .noApplicative }
  , { walsCode := "kay", iso := "gyd", value := .noApplicative }
  , { walsCode := "ket", iso := "ket", value := .noApplicative }
  , { walsCode := "kew", iso := "kew", value := .onlyBenefactive }
  , { walsCode := "khk", iso := "kjh", value := .noApplicative }
  , { walsCode := "kha", iso := "khk", value := .noApplicative }
  , { walsCode := "khs", iso := "kha", value := .noApplicative }
  , { walsCode := "klv", iso := "kij", value := .noApplicative }
  , { walsCode := "kio", iso := "kio", value := .noApplicative }
  , { walsCode := "kgz", iso := "kir", value := .noApplicative }
  , { walsCode := "koa", iso := "cku", value := .noApplicative }
  , { walsCode := "kob", iso := "kpw", value := .noApplicative }
  , { walsCode := "kol", iso := "kfb", value := .noApplicative }
  , { walsCode := "kor", iso := "kor", value := .noApplicative }
  , { walsCode := "kfe", iso := "kfz", value := .noApplicative }
  , { walsCode := "kse", iso := "ses", value := .instrument }
  , { walsCode := "kro", iso := "kgo", value := .locative }
  , { walsCode := "kut", iso := "kut", value := .instrument }
  , { walsCode := "lai", iso := "cnh", value := .instrument }
  , { walsCode := "lak", iso := "lbe", value := .noApplicative }
  , { walsCode := "lkt", iso := "lkt", value := .onlyBenefactive }
  , { walsCode := "lan", iso := "laj", value := .locative }
  , { walsCode := "lat", iso := "lav", value := .noApplicative }
  , { walsCode := "lav", iso := "lvk", value := .noApplicative }
  , { walsCode := "lez", iso := "lez", value := .noApplicative }
  , { walsCode := "lin", iso := "lin", value := .locative }
  , { walsCode := "luv", iso := "lue", value := .instrumentAndLocative }
  , { walsCode := "mac", iso := "mbc", value := .noApplicative }
  , { walsCode := "mak", iso := "myh", value := .noApplicative }
  , { walsCode := "mal", iso := "plt", value := .instrumentAndLocative }
  , { walsCode := "mnd", iso := "cmn", value := .noApplicative }
  , { walsCode := "myi", iso := "mpc", value := .noApplicative }
  , { walsCode := "mao", iso := "mri", value := .noApplicative }
  , { walsCode := "map", iso := "arn", value := .noApplicative }
  , { walsCode := "mar", iso := "mrc", value := .locative }
  , { walsCode := "mrt", iso := "vma", value := .noApplicative }
  , { walsCode := "mau", iso := "mph", value := .noApplicative }
  , { walsCode := "may", iso := "ayz", value := .instrument }
  , { walsCode := "mei", iso := "mni", value := .onlyBenefactive }
  , { walsCode := "mxc", iso := "mig", value := .noApplicative }
  , { walsCode := "mrl", iso := "mur", value := .noApplicative }
  , { walsCode := "kho", iso := "naq", value := .onlyBenefactive }
  , { walsCode := "ndy", iso := "djk", value := .noApplicative }
  , { walsCode := "nez", iso := "nez", value := .locative }
  , { walsCode := "ngn", iso := "nid", value := .onlyBenefactive }
  , { walsCode := "ngi", iso := "wyb", value := .noApplicative }
  , { walsCode := "niv", iso := "niv", value := .noApplicative }
  , { walsCode := "nko", iso := "cgg", value := .instrument }
  , { walsCode := "nug", iso := "nuy", value := .onlyBenefactive }
  , { walsCode := "nuu", iso := "nuk", value := .onlyBenefactive }
  , { walsCode := "oji", iso := "", value := .onlyBenefactive }
  , { walsCode := "ond", iso := "one", value := .instrumentAndLocative }
  , { walsCode := "orh", iso := "hae", value := .noApplicative }
  , { walsCode := "otm", iso := "ote", value := .noApplicative }
  , { walsCode := "pms", iso := "pma", value := .noApplicative }
  , { walsCode := "pai", iso := "pwn", value := .instrumentAndLocative }
  , { walsCode := "pan", iso := "pan", value := .noApplicative }
  , { walsCode := "psm", iso := "pqm", value := .onlyBenefactive }
  , { walsCode := "pau", iso := "pad", value := .onlyBenefactive }
  , { walsCode := "prs", iso := "pes", value := .noApplicative }
  , { walsCode := "prh", iso := "myp", value := .noApplicative }
  , { walsCode := "pmc", iso := "poo", value := .noApplicative }
  , { walsCode := "par", iso := "lkr", value := .onlyBenefactive }
  , { walsCode := "qaf", iso := "aar", value := .onlyBenefactive }
  , { walsCode := "qim", iso := "qvi", value := .noApplicative }
  , { walsCode := "ram", iso := "rma", value := .noApplicative }
  , { walsCode := "rap", iso := "rap", value := .noApplicative }
  , { walsCode := "rus", iso := "rus", value := .noApplicative }
  , { walsCode := "san", iso := "sag", value := .noApplicative }
  , { walsCode := "snm", iso := "xsu", value := .noApplicative }
  , { walsCode := "snc", iso := "see", value := .instrumentAndLocative }
  , { walsCode := "shk", iso := "shp", value := .onlyBenefactive }
  , { walsCode := "sla", iso := "den", value := .noApplicative }
  , { walsCode := "spa", iso := "spa", value := .noApplicative }
  , { walsCode := "sue", iso := "sue", value := .noApplicative }
  , { walsCode := "sup", iso := "spp", value := .noApplicative }
  , { walsCode := "swa", iso := "swh", value := .locative }
  , { walsCode := "tab", iso := "mky", value := .onlyBenefactive }
  , { walsCode := "tag", iso := "tgl", value := .instrumentAndLocative }
  , { walsCode := "tap", iso := "gpn", value := .onlyBenefactive }
  , { walsCode := "tml", iso := "tam", value := .noApplicative }
  , { walsCode := "tep", iso := "tpt", value := .instrument }
  , { walsCode := "tha", iso := "tha", value := .noApplicative }
  , { walsCode := "tho", iso := "thp", value := .locative }
  , { walsCode := "tiw", iso := "tiw", value := .instrument }
  , { walsCode := "tsz", iso := "ddo", value := .noApplicative }
  , { walsCode := "tuk", iso := "", value := .instrumentAndLocative }
  , { walsCode := "tur", iso := "tur", value := .noApplicative }
  , { walsCode := "tvl", iso := "tvl", value := .noApplicative }
  , { walsCode := "ukr", iso := "ukr", value := .noApplicative }
  , { walsCode := "una", iso := "mtg", value := .onlyBenefactive }
  , { walsCode := "urk", iso := "urb", value := .instrument }
  , { walsCode := "usa", iso := "wnu", value := .onlyBenefactive }
  , { walsCode := "uzb", iso := "", value := .noApplicative }
  , { walsCode := "vie", iso := "vie", value := .noApplicative }
  , { walsCode := "wam", iso := "wmb", value := .locative }
  , { walsCode := "wra", iso := "wba", value := .noApplicative }
  , { walsCode := "wrd", iso := "wrr", value := .noApplicative }
  , { walsCode := "war", iso := "pav", value := .noApplicative }
  , { walsCode := "wic", iso := "wic", value := .instrument }
  , { walsCode := "wch", iso := "mzh", value := .noApplicative }
  , { walsCode := "wlf", iso := "wol", value := .instrumentAndLocative }
  , { walsCode := "yag", iso := "yad", value := .instrumentAndLocative }
  , { walsCode := "yaq", iso := "yaq", value := .onlyBenefactive }
  , { walsCode := "yaz", iso := "yah", value := .noApplicative }
  , { walsCode := "yid", iso := "yii", value := .onlyBenefactive }
  , { walsCode := "yim", iso := "yee", value := .onlyBenefactive }
  , { walsCode := "yor", iso := "yor", value := .noApplicative }
  , { walsCode := "ypk", iso := "esu", value := .noApplicative }
  , { walsCode := "yur", iso := "yur", value := .noApplicative }
  , { walsCode := "zqc", iso := "zoc", value := .onlyBenefactive }
  , { walsCode := "zul", iso := "zul", value := .instrument }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F109B
