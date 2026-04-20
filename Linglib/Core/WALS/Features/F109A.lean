import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 109A: Applicative Constructions
@cite{polinsky-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 109A`.

Chapter 109, 183 languages.
-/

namespace Core.WALS.F109A

/-- WALS 109A values. -/
inductive ApplicativeType where
  /-- Benefactive object; both bases (16 languages). -/
  | benefactiveBothBases
  /-- Benefactive object; only transitive (4 languages). -/
  | benefactiveTransOnly
  /-- Benefactive and other; both bases (49 languages). -/
  | benefactiveAndOtherBothBases
  /-- Benefactive and other; only transitive (2 languages). -/
  | benefactiveAndOtherTransOnly
  /-- Non-benefactive object; both bases (9 languages). -/
  | nonBenefactiveBothBases
  /-- Non-benefactive object; only transitive (1 languages). -/
  | nonBenefactiveTransOnly
  /-- Non-benefactive object; only intransitive (2 languages). -/
  | nonBenefactiveIntransOnly
  /-- No applicative construction (100 languages). -/
  | noApplicative
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 109A dataset (183 languages). -/
def allData : List (Datapoint ApplicativeType) :=
  [ { walsCode := "abz", iso := "abq", value := .benefactiveAndOtherBothBases }
  , { walsCode := "abk", iso := "abk", value := .benefactiveAndOtherTransOnly }
  , { walsCode := "aco", iso := "kjq", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ain", iso := "ain", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ala", iso := "amp", value := .benefactiveBothBases }
  , { walsCode := "ame", iso := "aey", value := .benefactiveBothBases }
  , { walsCode := "apu", iso := "apu", value := .noApplicative }
  , { walsCode := "aeg", iso := "arz", value := .noApplicative }
  , { walsCode := "arp", iso := "ape", value := .benefactiveAndOtherBothBases }
  , { walsCode := "arc", iso := "aqc", value := .noApplicative }
  , { walsCode := "arm", iso := "hye", value := .noApplicative }
  , { walsCode := "asm", iso := "cns", value := .benefactiveTransOnly }
  , { walsCode := "awp", iso := "kwi", value := .noApplicative }
  , { walsCode := "bag", iso := "bmi", value := .noApplicative }
  , { walsCode := "brs", iso := "bsn", value := .noApplicative }
  , { walsCode := "bsq", iso := "eus", value := .noApplicative }
  , { walsCode := "bma", iso := "tzm", value := .noApplicative }
  , { walsCode := "brh", iso := "brh", value := .noApplicative }
  , { walsCode := "brm", iso := "mya", value := .noApplicative }
  , { walsCode := "bur", iso := "bsk", value := .benefactiveAndOtherBothBases }
  , { walsCode := "cah", iso := "chl", value := .benefactiveAndOtherBothBases }
  , { walsCode := "cnl", iso := "ram", value := .noApplicative }
  , { walsCode := "chh", iso := "sgw", value := .benefactiveTransOnly }
  , { walsCode := "cha", iso := "cha", value := .benefactiveBothBases }
  , { walsCode := "cic", iso := "nya", value := .benefactiveAndOtherBothBases }
  , { walsCode := "chk", iso := "ckt", value := .noApplicative }
  , { walsCode := "cmn", iso := "com", value := .benefactiveAndOtherBothBases }
  , { walsCode := "cre", iso := "crk", value := .benefactiveBothBases }
  , { walsCode := "dag", iso := "dgz", value := .noApplicative }
  , { walsCode := "dni", iso := "dni", value := .benefactiveAndOtherBothBases }
  , { walsCode := "diy", iso := "dif", value := .benefactiveAndOtherBothBases }
  , { walsCode := "dji", iso := "jig", value := .noApplicative }
  , { walsCode := "dyi", iso := "dbl", value := .nonBenefactiveBothBases }
  , { walsCode := "eng", iso := "eng", value := .noApplicative }
  , { walsCode := "epe", iso := "sja", value := .nonBenefactiveBothBases }
  , { walsCode := "eve", iso := "evn", value := .noApplicative }
  , { walsCode := "ewe", iso := "ewe", value := .noApplicative }
  , { walsCode := "fij", iso := "fij", value := .nonBenefactiveIntransOnly }
  , { walsCode := "fin", iso := "fin", value := .noApplicative }
  , { walsCode := "fre", iso := "fra", value := .noApplicative }
  , { walsCode := "gae", iso := "gla", value := .noApplicative }
  , { walsCode := "geo", iso := "kat", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ger", iso := "deu", value := .noApplicative }
  , { walsCode := "god", iso := "gdo", value := .noApplicative }
  , { walsCode := "goo", iso := "gni", value := .noApplicative }
  , { walsCode := "grb", iso := "grj", value := .benefactiveAndOtherBothBases }
  , { walsCode := "grk", iso := "ell", value := .noApplicative }
  , { walsCode := "grw", iso := "kal", value := .benefactiveAndOtherBothBases }
  , { walsCode := "gua", iso := "gug", value := .noApplicative }
  , { walsCode := "hli", iso := "hur", value := .benefactiveAndOtherBothBases }
  , { walsCode := "hau", iso := "hau", value := .benefactiveAndOtherBothBases }
  , { walsCode := "heb", iso := "heb", value := .noApplicative }
  , { walsCode := "hin", iso := "hin", value := .noApplicative }
  , { walsCode := "hix", iso := "hix", value := .noApplicative }
  , { walsCode := "hmo", iso := "hnj", value := .noApplicative }
  , { walsCode := "hun", iso := "hun", value := .noApplicative }
  , { walsCode := "hzb", iso := "huz", value := .noApplicative }
  , { walsCode := "ice", iso := "isl", value := .noApplicative }
  , { walsCode := "igb", iso := "ibo", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ika", iso := "arh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "imo", iso := "imn", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ind", iso := "ind", value := .benefactiveTransOnly }
  , { walsCode := "ing", iso := "inh", value := .noApplicative }
  , { walsCode := "irq", iso := "irk", value := .noApplicative }
  , { walsCode := "jak", iso := "jac", value := .nonBenefactiveTransOnly }
  , { walsCode := "jpn", iso := "jpn", value := .noApplicative }
  , { walsCode := "juh", iso := "ktz", value := .nonBenefactiveBothBases }
  , { walsCode := "kam", iso := "xbr", value := .benefactiveAndOtherBothBases }
  , { walsCode := "knd", iso := "kan", value := .benefactiveBothBases }
  , { walsCode := "knr", iso := "knc", value := .benefactiveAndOtherBothBases }
  , { walsCode := "krk", iso := "kyh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "kas", iso := "kas", value := .noApplicative }
  , { walsCode := "kay", iso := "gyd", value := .noApplicative }
  , { walsCode := "ket", iso := "ket", value := .noApplicative }
  , { walsCode := "kew", iso := "kew", value := .benefactiveBothBases }
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
  , { walsCode := "kse", iso := "ses", value := .nonBenefactiveBothBases }
  , { walsCode := "kro", iso := "kgo", value := .benefactiveAndOtherBothBases }
  , { walsCode := "kut", iso := "kut", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lai", iso := "cnh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lak", iso := "lbe", value := .noApplicative }
  , { walsCode := "lkt", iso := "lkt", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lan", iso := "laj", value := .benefactiveAndOtherBothBases }
  , { walsCode := "lat", iso := "lav", value := .noApplicative }
  , { walsCode := "lav", iso := "lvk", value := .noApplicative }
  , { walsCode := "lez", iso := "lez", value := .noApplicative }
  , { walsCode := "lin", iso := "lin", value := .benefactiveAndOtherBothBases }
  , { walsCode := "luv", iso := "lue", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mac", iso := "mbc", value := .noApplicative }
  , { walsCode := "mak", iso := "myh", value := .noApplicative }
  , { walsCode := "mal", iso := "plt", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mnd", iso := "cmn", value := .noApplicative }
  , { walsCode := "myi", iso := "mpc", value := .noApplicative }
  , { walsCode := "mao", iso := "mri", value := .noApplicative }
  , { walsCode := "map", iso := "arn", value := .noApplicative }
  , { walsCode := "mar", iso := "mrc", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mrt", iso := "vma", value := .noApplicative }
  , { walsCode := "mau", iso := "mph", value := .noApplicative }
  , { walsCode := "may", iso := "ayz", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mei", iso := "mni", value := .benefactiveAndOtherBothBases }
  , { walsCode := "mxc", iso := "mig", value := .noApplicative }
  , { walsCode := "mrl", iso := "mur", value := .noApplicative }
  , { walsCode := "kho", iso := "naq", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ndy", iso := "djk", value := .noApplicative }
  , { walsCode := "nez", iso := "nez", value := .benefactiveAndOtherBothBases }
  , { walsCode := "ngn", iso := "nid", value := .benefactiveBothBases }
  , { walsCode := "ngi", iso := "wyb", value := .noApplicative }
  , { walsCode := "niv", iso := "niv", value := .noApplicative }
  , { walsCode := "nko", iso := "cgg", value := .nonBenefactiveBothBases }
  , { walsCode := "nug", iso := "nuy", value := .benefactiveAndOtherBothBases }
  , { walsCode := "nuu", iso := "nuk", value := .benefactiveBothBases }
  , { walsCode := "oji", iso := "", value := .benefactiveBothBases }
  , { walsCode := "ond", iso := "one", value := .benefactiveAndOtherBothBases }
  , { walsCode := "orh", iso := "hae", value := .noApplicative }
  , { walsCode := "otm", iso := "ote", value := .noApplicative }
  , { walsCode := "pms", iso := "pma", value := .noApplicative }
  , { walsCode := "pai", iso := "pwn", value := .benefactiveAndOtherBothBases }
  , { walsCode := "pan", iso := "pan", value := .noApplicative }
  , { walsCode := "psm", iso := "pqm", value := .benefactiveBothBases }
  , { walsCode := "pau", iso := "pad", value := .benefactiveBothBases }
  , { walsCode := "prs", iso := "pes", value := .noApplicative }
  , { walsCode := "prh", iso := "myp", value := .noApplicative }
  , { walsCode := "pmc", iso := "poo", value := .noApplicative }
  , { walsCode := "par", iso := "lkr", value := .benefactiveBothBases }
  , { walsCode := "qaf", iso := "aar", value := .benefactiveBothBases }
  , { walsCode := "qim", iso := "qvi", value := .noApplicative }
  , { walsCode := "ram", iso := "rma", value := .noApplicative }
  , { walsCode := "rap", iso := "rap", value := .noApplicative }
  , { walsCode := "rus", iso := "rus", value := .noApplicative }
  , { walsCode := "san", iso := "sag", value := .noApplicative }
  , { walsCode := "snm", iso := "xsu", value := .noApplicative }
  , { walsCode := "snc", iso := "see", value := .benefactiveAndOtherBothBases }
  , { walsCode := "shk", iso := "shp", value := .benefactiveAndOtherBothBases }
  , { walsCode := "sla", iso := "den", value := .noApplicative }
  , { walsCode := "spa", iso := "spa", value := .noApplicative }
  , { walsCode := "sue", iso := "sue", value := .noApplicative }
  , { walsCode := "sup", iso := "spp", value := .noApplicative }
  , { walsCode := "swa", iso := "swh", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tab", iso := "mky", value := .nonBenefactiveBothBases }
  , { walsCode := "tag", iso := "tgl", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tap", iso := "gpn", value := .benefactiveAndOtherTransOnly }
  , { walsCode := "tml", iso := "tam", value := .noApplicative }
  , { walsCode := "tep", iso := "tpt", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tha", iso := "tha", value := .noApplicative }
  , { walsCode := "tho", iso := "thp", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tiw", iso := "tiw", value := .nonBenefactiveBothBases }
  , { walsCode := "tsz", iso := "ddo", value := .noApplicative }
  , { walsCode := "tuk", iso := "", value := .benefactiveAndOtherBothBases }
  , { walsCode := "tur", iso := "tur", value := .noApplicative }
  , { walsCode := "tvl", iso := "tvl", value := .noApplicative }
  , { walsCode := "ukr", iso := "ukr", value := .noApplicative }
  , { walsCode := "una", iso := "mtg", value := .benefactiveTransOnly }
  , { walsCode := "urk", iso := "urb", value := .benefactiveAndOtherBothBases }
  , { walsCode := "usa", iso := "wnu", value := .benefactiveBothBases }
  , { walsCode := "uzb", iso := "", value := .noApplicative }
  , { walsCode := "vie", iso := "vie", value := .noApplicative }
  , { walsCode := "wam", iso := "wmb", value := .nonBenefactiveIntransOnly }
  , { walsCode := "wra", iso := "wba", value := .noApplicative }
  , { walsCode := "wrd", iso := "wrr", value := .noApplicative }
  , { walsCode := "war", iso := "pav", value := .noApplicative }
  , { walsCode := "wic", iso := "wic", value := .benefactiveAndOtherBothBases }
  , { walsCode := "wch", iso := "mzh", value := .noApplicative }
  , { walsCode := "wlf", iso := "wol", value := .benefactiveAndOtherBothBases }
  , { walsCode := "yag", iso := "yad", value := .nonBenefactiveBothBases }
  , { walsCode := "yaq", iso := "yaq", value := .benefactiveBothBases }
  , { walsCode := "yaz", iso := "yah", value := .noApplicative }
  , { walsCode := "yid", iso := "yii", value := .nonBenefactiveBothBases }
  , { walsCode := "yim", iso := "yee", value := .benefactiveAndOtherBothBases }
  , { walsCode := "yor", iso := "yor", value := .noApplicative }
  , { walsCode := "ypk", iso := "esu", value := .noApplicative }
  , { walsCode := "yur", iso := "yur", value := .noApplicative }
  , { walsCode := "zqc", iso := "zoc", value := .benefactiveBothBases }
  , { walsCode := "zul", iso := "zul", value := .benefactiveAndOtherBothBases }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F109A
