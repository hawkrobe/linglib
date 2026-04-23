import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 21B: Exponence of Tense-Aspect-Mood Inflection
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 21B`.

Chapter 21, 160 languages.
-/

namespace Datasets.WALS.F21B

/-- WALS 21B values. -/
inductive ExponenceOfTenseAspectMoodInflection where
  /-- monoexponential TAM (127 languages). -/
  | monoexponentialTam
  /-- TAM+agreement (19 languages). -/
  | tamAgreement
  /-- TAM+agreement+diathesis (4 languages). -/
  | tamAgreementDiathesis
  /-- TAM+agreement+construct (1 languages). -/
  | tamAgreementConstruct
  /-- TAM+polarity (5 languages). -/
  | tamPolarity
  /-- no TAM (4 languages). -/
  | noTam
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 21B dataset (160 languages). -/
def allData : List (Datapoint ExponenceOfTenseAspectMoodInflection) :=
  [ { walsCode := "abi", iso := "axb", value := .monoexponentialTam }
  , { walsCode := "abk", iso := "abk", value := .monoexponentialTam }
  , { walsCode := "aco", iso := "kjq", value := .tamAgreement }
  , { walsCode := "ala", iso := "amp", value := .monoexponentialTam }
  , { walsCode := "ame", iso := "aey", value := .monoexponentialTam }
  , { walsCode := "apu", iso := "apu", value := .monoexponentialTam }
  , { walsCode := "aeg", iso := "arz", value := .tamAgreementDiathesis }
  , { walsCode := "ana", iso := "aro", value := .monoexponentialTam }
  , { walsCode := "arp", iso := "ape", value := .monoexponentialTam }
  , { walsCode := "amp", iso := "aer", value := .monoexponentialTam }
  , { walsCode := "asm", iso := "cns", value := .monoexponentialTam }
  , { walsCode := "atk", iso := "aqp", value := .monoexponentialTam }
  , { walsCode := "awp", iso := "kwi", value := .monoexponentialTam }
  , { walsCode := "aym", iso := "ayr", value := .tamAgreement }
  , { walsCode := "bag", iso := "bmi", value := .tamAgreement }
  , { walsCode := "bnj", iso := "bdy", value := .monoexponentialTam }
  , { walsCode := "brs", iso := "bsn", value := .monoexponentialTam }
  , { walsCode := "bsq", iso := "eus", value := .monoexponentialTam }
  , { walsCode := "bej", iso := "bej", value := .monoexponentialTam }
  , { walsCode := "bel", iso := "byw", value := .monoexponentialTam }
  , { walsCode := "bma", iso := "tzm", value := .monoexponentialTam }
  , { walsCode := "bbw", iso := "gup", value := .monoexponentialTam }
  , { walsCode := "brr", iso := "bor", value := .noTam }
  , { walsCode := "brh", iso := "brh", value := .tamAgreement }
  , { walsCode := "brm", iso := "mya", value := .monoexponentialTam }
  , { walsCode := "bur", iso := "bsk", value := .monoexponentialTam }
  , { walsCode := "cnl", iso := "ram", value := .monoexponentialTam }
  , { walsCode := "cyv", iso := "cyb", value := .monoexponentialTam }
  , { walsCode := "cha", iso := "cha", value := .tamAgreement }
  , { walsCode := "cku", iso := "wac", value := .monoexponentialTam }
  , { walsCode := "cho", iso := "chd", value := .monoexponentialTam }
  , { walsCode := "chk", iso := "ckt", value := .monoexponentialTam }
  , { walsCode := "cre", iso := "crk", value := .monoexponentialTam }
  , { walsCode := "dag", iso := "dgz", value := .tamAgreement }
  , { walsCode := "dni", iso := "dni", value := .monoexponentialTam }
  , { walsCode := "dig", iso := "mhu", value := .monoexponentialTam }
  , { walsCode := "eka", iso := "ekg", value := .monoexponentialTam }
  , { walsCode := "eng", iso := "eng", value := .monoexponentialTam }
  , { walsCode := "epe", iso := "sja", value := .monoexponentialTam }
  , { walsCode := "eve", iso := "evn", value := .monoexponentialTam }
  , { walsCode := "fij", iso := "fij", value := .monoexponentialTam }
  , { walsCode := "fin", iso := "fin", value := .monoexponentialTam }
  , { walsCode := "fre", iso := "fra", value := .tamAgreement }
  , { walsCode := "gar", iso := "grt", value := .monoexponentialTam }
  , { walsCode := "geo", iso := "kat", value := .tamAgreement }
  , { walsCode := "ger", iso := "deu", value := .monoexponentialTam }
  , { walsCode := "goo", iso := "gni", value := .monoexponentialTam }
  , { walsCode := "grb", iso := "grj", value := .monoexponentialTam }
  , { walsCode := "grk", iso := "ell", value := .tamAgreementDiathesis }
  , { walsCode := "grw", iso := "kal", value := .monoexponentialTam }
  , { walsCode := "gua", iso := "gug", value := .monoexponentialTam }
  , { walsCode := "hai", iso := "hai", value := .monoexponentialTam }
  , { walsCode := "hat", iso := "had", value := .monoexponentialTam }
  , { walsCode := "hau", iso := "hau", value := .monoexponentialTam }
  , { walsCode := "heb", iso := "heb", value := .tamAgreementDiathesis }
  , { walsCode := "hin", iso := "hin", value := .tamAgreement }
  , { walsCode := "hix", iso := "hix", value := .monoexponentialTam }
  , { walsCode := "hmo", iso := "hnj", value := .monoexponentialTam }
  , { walsCode := "hve", iso := "huv", value := .tamAgreement }
  , { walsCode := "hun", iso := "hun", value := .monoexponentialTam }
  , { walsCode := "hzb", iso := "huz", value := .tamPolarity }
  , { walsCode := "iau", iso := "tmu", value := .monoexponentialTam }
  , { walsCode := "imo", iso := "imn", value := .monoexponentialTam }
  , { walsCode := "ind", iso := "ind", value := .monoexponentialTam }
  , { walsCode := "ing", iso := "inh", value := .monoexponentialTam }
  , { walsCode := "jak", iso := "jac", value := .monoexponentialTam }
  , { walsCode := "jpn", iso := "jpn", value := .monoexponentialTam }
  , { walsCode := "jel", iso := "jek", value := .monoexponentialTam }
  , { walsCode := "knd", iso := "kan", value := .monoexponentialTam }
  , { walsCode := "krk", iso := "kyh", value := .monoexponentialTam }
  , { walsCode := "kay", iso := "gyd", value := .tamPolarity }
  , { walsCode := "ket", iso := "ket", value := .tamAgreement }
  , { walsCode := "kew", iso := "kew", value := .tamAgreementDiathesis }
  , { walsCode := "kha", iso := "khk", value := .monoexponentialTam }
  , { walsCode := "khs", iso := "kha", value := .monoexponentialTam }
  , { walsCode := "kio", iso := "kio", value := .monoexponentialTam }
  , { walsCode := "kis", iso := "kss", value := .monoexponentialTam }
  , { walsCode := "kiw", iso := "kjd", value := .tamAgreement }
  , { walsCode := "koa", iso := "cku", value := .monoexponentialTam }
  , { walsCode := "koi", iso := "kbk", value := .tamAgreement }
  , { walsCode := "kor", iso := "kor", value := .monoexponentialTam }
  , { walsCode := "kch", iso := "khq", value := .tamPolarity }
  , { walsCode := "kro", iso := "kgo", value := .monoexponentialTam }
  , { walsCode := "knm", iso := "kun", value := .monoexponentialTam }
  , { walsCode := "kut", iso := "kut", value := .monoexponentialTam }
  , { walsCode := "lah", iso := "lhu", value := .monoexponentialTam }
  , { walsCode := "lai", iso := "cnh", value := .monoexponentialTam }
  , { walsCode := "lkt", iso := "lkt", value := .monoexponentialTam }
  , { walsCode := "lan", iso := "laj", value := .tamAgreementConstruct }
  , { walsCode := "lav", iso := "lvk", value := .monoexponentialTam }
  , { walsCode := "lez", iso := "lez", value := .monoexponentialTam }
  , { walsCode := "lug", iso := "lgg", value := .monoexponentialTam }
  , { walsCode := "luv", iso := "lue", value := .monoexponentialTam }
  , { walsCode := "maa", iso := "mas", value := .tamPolarity }
  , { walsCode := "mal", iso := "plt", value := .monoexponentialTam }
  , { walsCode := "mnd", iso := "cmn", value := .monoexponentialTam }
  , { walsCode := "myi", iso := "mpc", value := .tamPolarity }
  , { walsCode := "mao", iso := "mri", value := .monoexponentialTam }
  , { walsCode := "map", iso := "arn", value := .tamAgreement }
  , { walsCode := "mrg", iso := "mrt", value := .monoexponentialTam }
  , { walsCode := "mar", iso := "mrc", value := .monoexponentialTam }
  , { walsCode := "mrt", iso := "vma", value := .monoexponentialTam }
  , { walsCode := "mau", iso := "mph", value := .monoexponentialTam }
  , { walsCode := "may", iso := "ayz", value := .noTam }
  , { walsCode := "mei", iso := "mni", value := .monoexponentialTam }
  , { walsCode := "mss", iso := "skd", value := .monoexponentialTam }
  , { walsCode := "mxc", iso := "mig", value := .monoexponentialTam }
  , { walsCode := "mun", iso := "unr", value := .monoexponentialTam }
  , { walsCode := "nah", iso := "nll", value := .monoexponentialTam }
  , { walsCode := "kho", iso := "naq", value := .monoexponentialTam }
  , { walsCode := "nmb", iso := "nab", value := .monoexponentialTam }
  , { walsCode := "nan", iso := "niq", value := .monoexponentialTam }
  , { walsCode := "ntu", iso := "yrk", value := .monoexponentialTam }
  , { walsCode := "ngi", iso := "wyb", value := .monoexponentialTam }
  , { walsCode := "niv", iso := "niv", value := .monoexponentialTam }
  , { walsCode := "nbd", iso := "dgl", value := .monoexponentialTam }
  , { walsCode := "ond", iso := "one", value := .monoexponentialTam }
  , { walsCode := "orh", iso := "hae", value := .monoexponentialTam }
  , { walsCode := "otm", iso := "ote", value := .tamAgreement }
  , { walsCode := "pai", iso := "pwn", value := .monoexponentialTam }
  , { walsCode := "prs", iso := "pes", value := .monoexponentialTam }
  , { walsCode := "prh", iso := "myp", value := .monoexponentialTam }
  , { walsCode := "pur", iso := "tsz", value := .monoexponentialTam }
  , { walsCode := "qim", iso := "qvi", value := .monoexponentialTam }
  , { walsCode := "ram", iso := "rma", value := .monoexponentialTam }
  , { walsCode := "rap", iso := "rap", value := .monoexponentialTam }
  , { walsCode := "rus", iso := "rus", value := .monoexponentialTam }
  , { walsCode := "san", iso := "sag", value := .noTam }
  , { walsCode := "snm", iso := "xsu", value := .monoexponentialTam }
  , { walsCode := "sla", iso := "den", value := .monoexponentialTam }
  , { walsCode := "spa", iso := "spa", value := .tamAgreement }
  , { walsCode := "squ", iso := "squ", value := .monoexponentialTam }
  , { walsCode := "sup", iso := "spp", value := .monoexponentialTam }
  , { walsCode := "swa", iso := "swh", value := .monoexponentialTam }
  , { walsCode := "tag", iso := "tgl", value := .monoexponentialTam }
  , { walsCode := "ter", iso := "ttr", value := .monoexponentialTam }
  , { walsCode := "tha", iso := "tha", value := .monoexponentialTam }
  , { walsCode := "tib", iso := "bod", value := .tamAgreement }
  , { walsCode := "tiw", iso := "tiw", value := .noTam }
  , { walsCode := "tli", iso := "tli", value := .monoexponentialTam }
  , { walsCode := "tot", iso := "tlc", value := .monoexponentialTam }
  , { walsCode := "tru", iso := "tpy", value := .monoexponentialTam }
  , { walsCode := "tuk", iso := "", value := .tamAgreement }
  , { walsCode := "tur", iso := "tur", value := .monoexponentialTam }
  , { walsCode := "vie", iso := "vie", value := .monoexponentialTam }
  , { walsCode := "wra", iso := "wba", value := .monoexponentialTam }
  , { walsCode := "wrd", iso := "wrr", value := .monoexponentialTam }
  , { walsCode := "wrm", iso := "wsa", value := .monoexponentialTam }
  , { walsCode := "war", iso := "pav", value := .tamAgreement }
  , { walsCode := "wem", iso := "xww", value := .monoexponentialTam }
  , { walsCode := "wic", iso := "wic", value := .monoexponentialTam }
  , { walsCode := "wch", iso := "mzh", value := .monoexponentialTam }
  , { walsCode := "yag", iso := "yad", value := .monoexponentialTam }
  , { walsCode := "yaq", iso := "yaq", value := .monoexponentialTam }
  , { walsCode := "yid", iso := "yii", value := .monoexponentialTam }
  , { walsCode := "yor", iso := "yor", value := .monoexponentialTam }
  , { walsCode := "yuc", iso := "yuc", value := .monoexponentialTam }
  , { walsCode := "yur", iso := "yur", value := .monoexponentialTam }
  , { walsCode := "zqc", iso := "zoc", value := .monoexponentialTam }
  , { walsCode := "zul", iso := "zul", value := .monoexponentialTam }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F21B
