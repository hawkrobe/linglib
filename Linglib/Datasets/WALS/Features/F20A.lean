import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 20A: Fusion of Selected Inflectional Formatives
@cite{bickel-nichols-2013a}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 20A`.

Chapter 20, 165 languages.
-/

namespace Datasets.WALS.F20A

/-- WALS 20A values. -/
inductive FusionType where
  /-- Exclusively concatenative (125 languages). -/
  | exclusivelyConcatenative
  /-- Exclusively isolating (16 languages). -/
  | exclusivelyIsolating
  /-- Exclusively tonal (3 languages). -/
  | exclusivelyTonal
  /-- Tonal/isolating (1 languages). -/
  | tonalIsolating
  /-- Tonal/concatenative (2 languages). -/
  | tonalConcatenative
  /-- Ablaut/concatenative (5 languages). -/
  | ablautConcatenative
  /-- Isolating/concatenative (13 languages). -/
  | isolatingConcatenative
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 20A dataset (165 languages). -/
def allData : List (Datapoint FusionType) :=
  [ { walsCode := "abi", iso := "axb", value := .exclusivelyConcatenative }
  , { walsCode := "abk", iso := "abk", value := .exclusivelyConcatenative }
  , { walsCode := "aco", iso := "kjq", value := .exclusivelyConcatenative }
  , { walsCode := "ala", iso := "amp", value := .exclusivelyConcatenative }
  , { walsCode := "ame", iso := "aey", value := .exclusivelyConcatenative }
  , { walsCode := "apu", iso := "apu", value := .exclusivelyConcatenative }
  , { walsCode := "aeg", iso := "arz", value := .ablautConcatenative }
  , { walsCode := "ana", iso := "aro", value := .exclusivelyConcatenative }
  , { walsCode := "arp", iso := "ape", value := .exclusivelyConcatenative }
  , { walsCode := "amp", iso := "aer", value := .exclusivelyConcatenative }
  , { walsCode := "asm", iso := "cns", value := .exclusivelyConcatenative }
  , { walsCode := "atk", iso := "aqp", value := .exclusivelyConcatenative }
  , { walsCode := "awp", iso := "kwi", value := .exclusivelyConcatenative }
  , { walsCode := "aym", iso := "ayr", value := .exclusivelyConcatenative }
  , { walsCode := "bag", iso := "bmi", value := .exclusivelyConcatenative }
  , { walsCode := "bnj", iso := "bdy", value := .exclusivelyConcatenative }
  , { walsCode := "brs", iso := "bsn", value := .exclusivelyConcatenative }
  , { walsCode := "bsq", iso := "eus", value := .exclusivelyConcatenative }
  , { walsCode := "bej", iso := "bej", value := .ablautConcatenative }
  , { walsCode := "bel", iso := "byw", value := .exclusivelyConcatenative }
  , { walsCode := "bma", iso := "tzm", value := .ablautConcatenative }
  , { walsCode := "bbw", iso := "gup", value := .exclusivelyConcatenative }
  , { walsCode := "brh", iso := "brh", value := .exclusivelyConcatenative }
  , { walsCode := "brm", iso := "mya", value := .exclusivelyConcatenative }
  , { walsCode := "bur", iso := "bsk", value := .exclusivelyConcatenative }
  , { walsCode := "cah", iso := "chl", value := .exclusivelyConcatenative }
  , { walsCode := "cnl", iso := "ram", value := .exclusivelyConcatenative }
  , { walsCode := "cyv", iso := "cyb", value := .exclusivelyConcatenative }
  , { walsCode := "cha", iso := "cha", value := .isolatingConcatenative }
  , { walsCode := "cku", iso := "wac", value := .exclusivelyConcatenative }
  , { walsCode := "cho", iso := "chd", value := .exclusivelyConcatenative }
  , { walsCode := "chk", iso := "ckt", value := .exclusivelyConcatenative }
  , { walsCode := "ccp", iso := "coc", value := .exclusivelyConcatenative }
  , { walsCode := "coo", iso := "csz", value := .exclusivelyConcatenative }
  , { walsCode := "cre", iso := "crk", value := .isolatingConcatenative }
  , { walsCode := "dag", iso := "dgz", value := .exclusivelyConcatenative }
  , { walsCode := "dni", iso := "dni", value := .exclusivelyConcatenative }
  , { walsCode := "dig", iso := "mhu", value := .exclusivelyConcatenative }
  , { walsCode := "eka", iso := "ekg", value := .exclusivelyConcatenative }
  , { walsCode := "eng", iso := "eng", value := .exclusivelyConcatenative }
  , { walsCode := "epe", iso := "sja", value := .exclusivelyConcatenative }
  , { walsCode := "eve", iso := "evn", value := .exclusivelyConcatenative }
  , { walsCode := "fij", iso := "fij", value := .exclusivelyIsolating }
  , { walsCode := "fin", iso := "fin", value := .exclusivelyConcatenative }
  , { walsCode := "fre", iso := "fra", value := .exclusivelyConcatenative }
  , { walsCode := "gar", iso := "grt", value := .exclusivelyConcatenative }
  , { walsCode := "geo", iso := "kat", value := .exclusivelyConcatenative }
  , { walsCode := "ger", iso := "deu", value := .exclusivelyConcatenative }
  , { walsCode := "goo", iso := "gni", value := .isolatingConcatenative }
  , { walsCode := "grb", iso := "grj", value := .exclusivelyConcatenative }
  , { walsCode := "grk", iso := "ell", value := .exclusivelyConcatenative }
  , { walsCode := "grw", iso := "kal", value := .exclusivelyConcatenative }
  , { walsCode := "gua", iso := "gug", value := .exclusivelyConcatenative }
  , { walsCode := "hai", iso := "hai", value := .exclusivelyConcatenative }
  , { walsCode := "hat", iso := "had", value := .exclusivelyConcatenative }
  , { walsCode := "hau", iso := "hau", value := .exclusivelyIsolating }
  , { walsCode := "heb", iso := "heb", value := .ablautConcatenative }
  , { walsCode := "hin", iso := "hin", value := .exclusivelyConcatenative }
  , { walsCode := "hix", iso := "hix", value := .exclusivelyConcatenative }
  , { walsCode := "hmo", iso := "hnj", value := .exclusivelyIsolating }
  , { walsCode := "hve", iso := "huv", value := .exclusivelyConcatenative }
  , { walsCode := "hun", iso := "hun", value := .exclusivelyConcatenative }
  , { walsCode := "hzb", iso := "huz", value := .exclusivelyConcatenative }
  , { walsCode := "iau", iso := "tmu", value := .exclusivelyTonal }
  , { walsCode := "imo", iso := "imn", value := .exclusivelyConcatenative }
  , { walsCode := "ind", iso := "ind", value := .exclusivelyIsolating }
  , { walsCode := "ing", iso := "inh", value := .exclusivelyConcatenative }
  , { walsCode := "jak", iso := "jac", value := .exclusivelyConcatenative }
  , { walsCode := "jpn", iso := "jpn", value := .exclusivelyConcatenative }
  , { walsCode := "jel", iso := "jek", value := .exclusivelyIsolating }
  , { walsCode := "knd", iso := "kan", value := .exclusivelyConcatenative }
  , { walsCode := "krk", iso := "kyh", value := .exclusivelyConcatenative }
  , { walsCode := "kay", iso := "gyd", value := .exclusivelyConcatenative }
  , { walsCode := "ket", iso := "ket", value := .exclusivelyConcatenative }
  , { walsCode := "kew", iso := "kew", value := .exclusivelyConcatenative }
  , { walsCode := "kha", iso := "khk", value := .exclusivelyConcatenative }
  , { walsCode := "khs", iso := "kha", value := .exclusivelyIsolating }
  , { walsCode := "kio", iso := "kio", value := .exclusivelyConcatenative }
  , { walsCode := "kri", iso := "kzw", value := .exclusivelyIsolating }
  , { walsCode := "kis", iso := "kss", value := .exclusivelyTonal }
  , { walsCode := "kiw", iso := "kjd", value := .exclusivelyConcatenative }
  , { walsCode := "koa", iso := "cku", value := .exclusivelyConcatenative }
  , { walsCode := "koi", iso := "kbk", value := .exclusivelyConcatenative }
  , { walsCode := "kor", iso := "kor", value := .exclusivelyConcatenative }
  , { walsCode := "kch", iso := "khq", value := .exclusivelyIsolating }
  , { walsCode := "kro", iso := "kgo", value := .exclusivelyConcatenative }
  , { walsCode := "knm", iso := "kun", value := .isolatingConcatenative }
  , { walsCode := "kut", iso := "kut", value := .exclusivelyConcatenative }
  , { walsCode := "lah", iso := "lhu", value := .exclusivelyIsolating }
  , { walsCode := "lai", iso := "cnh", value := .exclusivelyIsolating }
  , { walsCode := "lkt", iso := "lkt", value := .isolatingConcatenative }
  , { walsCode := "lan", iso := "laj", value := .exclusivelyTonal }
  , { walsCode := "lav", iso := "lvk", value := .exclusivelyConcatenative }
  , { walsCode := "lez", iso := "lez", value := .exclusivelyConcatenative }
  , { walsCode := "lug", iso := "lgg", value := .ablautConcatenative }
  , { walsCode := "luv", iso := "lue", value := .exclusivelyConcatenative }
  , { walsCode := "maa", iso := "mas", value := .tonalConcatenative }
  , { walsCode := "mal", iso := "plt", value := .exclusivelyConcatenative }
  , { walsCode := "mnd", iso := "cmn", value := .isolatingConcatenative }
  , { walsCode := "myi", iso := "mpc", value := .exclusivelyConcatenative }
  , { walsCode := "mao", iso := "mri", value := .isolatingConcatenative }
  , { walsCode := "map", iso := "arn", value := .exclusivelyConcatenative }
  , { walsCode := "mar", iso := "mrc", value := .exclusivelyConcatenative }
  , { walsCode := "mrt", iso := "vma", value := .exclusivelyConcatenative }
  , { walsCode := "mau", iso := "mph", value := .exclusivelyConcatenative }
  , { walsCode := "may", iso := "ayz", value := .exclusivelyConcatenative }
  , { walsCode := "mei", iso := "mni", value := .exclusivelyConcatenative }
  , { walsCode := "mss", iso := "skd", value := .exclusivelyConcatenative }
  , { walsCode := "mxc", iso := "mig", value := .exclusivelyConcatenative }
  , { walsCode := "mot", iso := "siw", value := .exclusivelyConcatenative }
  , { walsCode := "mun", iso := "unr", value := .exclusivelyConcatenative }
  , { walsCode := "nah", iso := "nll", value := .exclusivelyConcatenative }
  , { walsCode := "kho", iso := "naq", value := .isolatingConcatenative }
  , { walsCode := "nmb", iso := "nab", value := .exclusivelyConcatenative }
  , { walsCode := "nan", iso := "niq", value := .tonalConcatenative }
  , { walsCode := "nav", iso := "nav", value := .exclusivelyConcatenative }
  , { walsCode := "ntu", iso := "yrk", value := .exclusivelyConcatenative }
  , { walsCode := "ngi", iso := "wyb", value := .exclusivelyConcatenative }
  , { walsCode := "niv", iso := "niv", value := .exclusivelyConcatenative }
  , { walsCode := "nbd", iso := "dgl", value := .exclusivelyConcatenative }
  , { walsCode := "ond", iso := "one", value := .exclusivelyConcatenative }
  , { walsCode := "orh", iso := "hae", value := .exclusivelyConcatenative }
  , { walsCode := "otm", iso := "ote", value := .exclusivelyConcatenative }
  , { walsCode := "pai", iso := "pwn", value := .isolatingConcatenative }
  , { walsCode := "prs", iso := "pes", value := .exclusivelyConcatenative }
  , { walsCode := "prh", iso := "myp", value := .exclusivelyConcatenative }
  , { walsCode := "pso", iso := "pom", value := .exclusivelyConcatenative }
  , { walsCode := "pur", iso := "tsz", value := .exclusivelyConcatenative }
  , { walsCode := "qim", iso := "qvi", value := .exclusivelyConcatenative }
  , { walsCode := "ram", iso := "rma", value := .exclusivelyConcatenative }
  , { walsCode := "rap", iso := "rap", value := .exclusivelyIsolating }
  , { walsCode := "rus", iso := "rus", value := .exclusivelyConcatenative }
  , { walsCode := "san", iso := "sag", value := .exclusivelyConcatenative }
  , { walsCode := "snm", iso := "xsu", value := .exclusivelyConcatenative }
  , { walsCode := "shk", iso := "shp", value := .exclusivelyConcatenative }
  , { walsCode := "sla", iso := "den", value := .exclusivelyConcatenative }
  , { walsCode := "spa", iso := "spa", value := .exclusivelyConcatenative }
  , { walsCode := "squ", iso := "squ", value := .exclusivelyConcatenative }
  , { walsCode := "sup", iso := "spp", value := .exclusivelyIsolating }
  , { walsCode := "swa", iso := "swh", value := .exclusivelyConcatenative }
  , { walsCode := "tag", iso := "tgl", value := .exclusivelyConcatenative }
  , { walsCode := "ter", iso := "ttr", value := .exclusivelyIsolating }
  , { walsCode := "tha", iso := "tha", value := .isolatingConcatenative }
  , { walsCode := "tib", iso := "bod", value := .exclusivelyConcatenative }
  , { walsCode := "tiw", iso := "tiw", value := .exclusivelyConcatenative }
  , { walsCode := "tli", iso := "tli", value := .exclusivelyConcatenative }
  , { walsCode := "tot", iso := "tlc", value := .exclusivelyConcatenative }
  , { walsCode := "tru", iso := "tpy", value := .isolatingConcatenative }
  , { walsCode := "tuk", iso := "", value := .isolatingConcatenative }
  , { walsCode := "tur", iso := "tur", value := .exclusivelyConcatenative }
  , { walsCode := "vie", iso := "vie", value := .exclusivelyIsolating }
  , { walsCode := "wra", iso := "wba", value := .isolatingConcatenative }
  , { walsCode := "wrd", iso := "wrr", value := .exclusivelyConcatenative }
  , { walsCode := "wrm", iso := "wsa", value := .exclusivelyConcatenative }
  , { walsCode := "war", iso := "pav", value := .exclusivelyIsolating }
  , { walsCode := "wem", iso := "xww", value := .exclusivelyConcatenative }
  , { walsCode := "wic", iso := "wic", value := .exclusivelyConcatenative }
  , { walsCode := "wch", iso := "mzh", value := .exclusivelyIsolating }
  , { walsCode := "yag", iso := "yad", value := .exclusivelyConcatenative }
  , { walsCode := "yaq", iso := "yaq", value := .exclusivelyConcatenative }
  , { walsCode := "yid", iso := "yii", value := .exclusivelyConcatenative }
  , { walsCode := "yor", iso := "yor", value := .tonalIsolating }
  , { walsCode := "yur", iso := "yur", value := .exclusivelyConcatenative }
  , { walsCode := "zqc", iso := "zoc", value := .exclusivelyConcatenative }
  , { walsCode := "zul", iso := "zul", value := .exclusivelyConcatenative }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F20A
