import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 122A: Relativization on Subjects
@cite{comrie-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 122A`.

Chapter 122, 166 languages.
-/

namespace Datasets.WALS.F122A

/-- WALS 122A values. -/
inductive SubjectRelativization where
  /-- Relative pronoun (12 languages). -/
  | relativePronoun
  /-- Non-reduction (24 languages). -/
  | nonReduction
  /-- Pronoun-retention (5 languages). -/
  | pronounRetention
  /-- Gap (125 languages). -/
  | gap
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 122A dataset (166 languages). -/
def allData : List (Datapoint SubjectRelativization) :=
  [ { walsCode := "abk", iso := "abk", value := .gap }
  , { walsCode := "ace", iso := "ace", value := .gap }
  , { walsCode := "aco", iso := "kjq", value := .relativePronoun }
  , { walsCode := "ala", iso := "amp", value := .gap }
  , { walsCode := "ame", iso := "aey", value := .nonReduction }
  , { walsCode := "any", iso := "anu", value := .gap }
  , { walsCode := "aeg", iso := "arz", value := .gap }
  , { walsCode := "arp", iso := "ape", value := .gap }
  , { walsCode := "bab", iso := "bav", value := .pronounRetention }
  , { walsCode := "bag", iso := "bmi", value := .gap }
  , { walsCode := "bak", iso := "bkc", value := .pronounRetention }
  , { walsCode := "bam", iso := "bam", value := .nonReduction }
  , { walsCode := "brs", iso := "bsn", value := .gap }
  , { walsCode := "bar", iso := "bfa", value := .gap }
  , { walsCode := "bsq", iso := "eus", value := .gap }
  , { walsCode := "bkr", iso := "btx", value := .gap }
  , { walsCode := "baw", iso := "bgr", value := .gap }
  , { walsCode := "bma", iso := "tzm", value := .gap }
  , { walsCode := "bob", iso := "bni", value := .gap }
  , { walsCode := "blq", iso := "bol", value := .gap }
  , { walsCode := "brh", iso := "brh", value := .gap }
  , { walsCode := "bul", iso := "bul", value := .relativePronoun }
  , { walsCode := "brm", iso := "mya", value := .gap }
  , { walsCode := "bur", iso := "bsk", value := .gap }
  , { walsCode := "cah", iso := "chl", value := .nonReduction }
  , { walsCode := "cnl", iso := "ram", value := .nonReduction }
  , { walsCode := "cha", iso := "cha", value := .gap }
  , { walsCode := "cle", iso := "cle", value := .gap }
  , { walsCode := "chk", iso := "ckt", value := .gap }
  , { walsCode := "dag", iso := "dgz", value := .gap }
  , { walsCode := "dgb", iso := "dag", value := .gap }
  , { walsCode := "dni", iso := "dni", value := .gap }
  , { walsCode := "deg", iso := "deg", value := .gap }
  , { walsCode := "die", iso := "dih", value := .nonReduction }
  , { walsCode := "diy", iso := "dif", value := .gap }
  , { walsCode := "eng", iso := "eng", value := .relativePronoun }
  , { walsCode := "epe", iso := "sja", value := .nonReduction }
  , { walsCode := "eve", iso := "evn", value := .gap }
  , { walsCode := "ewa", iso := "ewe", value := .gap }
  , { walsCode := "fij", iso := "fij", value := .gap }
  , { walsCode := "fin", iso := "fin", value := .relativePronoun }
  , { walsCode := "fre", iso := "fra", value := .relativePronoun }
  , { walsCode := "fur", iso := "fvr", value := .gap }
  , { walsCode := "fye", iso := "pym", value := .gap }
  , { walsCode := "gae", iso := "gla", value := .gap }
  , { walsCode := "geo", iso := "kat", value := .relativePronoun }
  , { walsCode := "ger", iso := "deu", value := .relativePronoun }
  , { walsCode := "gdr", iso := "gid", value := .gap }
  , { walsCode := "giz", iso := "gis", value := .gap }
  , { walsCode := "goo", iso := "gni", value := .nonReduction }
  , { walsCode := "grk", iso := "ell", value := .relativePronoun }
  , { walsCode := "grw", iso := "kal", value := .gap }
  , { walsCode := "gua", iso := "gug", value := .gap }
  , { walsCode := "hau", iso := "hau", value := .gap }
  , { walsCode := "heb", iso := "heb", value := .gap }
  , { walsCode := "hin", iso := "hin", value := .nonReduction }
  , { walsCode := "hix", iso := "hix", value := .gap }
  , { walsCode := "hmo", iso := "hnj", value := .gap }
  , { walsCode := "hun", iso := "hun", value := .relativePronoun }
  , { walsCode := "hzb", iso := "huz", value := .gap }
  , { walsCode := "ik", iso := "ikx", value := .gap }
  , { walsCode := "ika", iso := "arh", value := .nonReduction }
  , { walsCode := "imo", iso := "imn", value := .gap }
  , { walsCode := "ind", iso := "ind", value := .gap }
  , { walsCode := "ing", iso := "inh", value := .gap }
  , { walsCode := "iri", iso := "gle", value := .gap }
  , { walsCode := "ita", iso := "ita", value := .relativePronoun }
  , { walsCode := "jak", iso := "jac", value := .gap }
  , { walsCode := "jpn", iso := "jpn", value := .gap }
  , { walsCode := "kam", iso := "xbr", value := .gap }
  , { walsCode := "knd", iso := "kan", value := .gap }
  , { walsCode := "krc", iso := "krc", value := .gap }
  , { walsCode := "kyl", iso := "eky", value := .pronounRetention }
  , { walsCode := "kay", iso := "gyd", value := .gap }
  , { walsCode := "kha", iso := "khk", value := .gap }
  , { walsCode := "khm", iso := "khm", value := .gap }
  , { walsCode := "klv", iso := "kij", value := .gap }
  , { walsCode := "kin", iso := "kin", value := .gap }
  , { walsCode := "kio", iso := "kio", value := .nonReduction }
  , { walsCode := "kis", iso := "kss", value := .gap }
  , { walsCode := "koa", iso := "cku", value := .nonReduction }
  , { walsCode := "kob", iso := "kpw", value := .gap }
  , { walsCode := "kjr", iso := "kqy", value := .gap }
  , { walsCode := "kko", iso := "knk", value := .nonReduction }
  , { walsCode := "kor", iso := "kor", value := .gap }
  , { walsCode := "kfe", iso := "kfz", value := .gap }
  , { walsCode := "kch", iso := "khq", value := .gap }
  , { walsCode := "kse", iso := "ses", value := .gap }
  , { walsCode := "kro", iso := "kgo", value := .gap }
  , { walsCode := "kul", iso := "dwr", value := .gap }
  , { walsCode := "knm", iso := "kun", value := .gap }
  , { walsCode := "kxo", iso := "xuu", value := .gap }
  , { walsCode := "lkt", iso := "lkt", value := .nonReduction }
  , { walsCode := "lan", iso := "laj", value := .gap }
  , { walsCode := "lat", iso := "lav", value := .relativePronoun }
  , { walsCode := "lav", iso := "lvk", value := .nonReduction }
  , { walsCode := "lel", iso := "lln", value := .gap }
  , { walsCode := "lez", iso := "lez", value := .gap }
  , { walsCode := "lin", iso := "lin", value := .gap }
  , { walsCode := "luo", iso := "luo", value := .gap }
  , { walsCode := "luv", iso := "lue", value := .gap }
  , { walsCode := "mle", iso := "mdy", value := .gap }
  , { walsCode := "maa", iso := "mas", value := .gap }
  , { walsCode := "mal", iso := "plt", value := .gap }
  , { walsCode := "mnd", iso := "cmn", value := .gap }
  , { walsCode := "mao", iso := "mri", value := .gap }
  , { walsCode := "map", iso := "arn", value := .gap }
  , { walsCode := "mku", iso := "zmr", value := .nonReduction }
  , { walsCode := "mar", iso := "mrc", value := .nonReduction }
  , { walsCode := "mrt", iso := "vma", value := .gap }
  , { walsCode := "mau", iso := "mph", value := .gap }
  , { walsCode := "may", iso := "ayz", value := .gap }
  , { walsCode := "mei", iso := "mni", value := .gap }
  , { walsCode := "mxc", iso := "mig", value := .gap }
  , { walsCode := "miy", iso := "mkf", value := .gap }
  , { walsCode := "mna", iso := "mnb", value := .gap }
  , { walsCode := "kho", iso := "naq", value := .gap }
  , { walsCode := "nbb", iso := "nmb", value := .gap }
  , { walsCode := "nan", iso := "niq", value := .gap }
  , { walsCode := "ndy", iso := "djk", value := .gap }
  , { walsCode := "nge", iso := "nge", value := .pronounRetention }
  , { walsCode := "ngi", iso := "wyb", value := .gap }
  , { walsCode := "nbd", iso := "dgl", value := .gap }
  , { walsCode := "nug", iso := "nuy", value := .gap }
  , { walsCode := "orh", iso := "hae", value := .gap }
  , { walsCode := "pms", iso := "pma", value := .gap }
  , { walsCode := "pai", iso := "pwn", value := .gap }
  , { walsCode := "psm", iso := "pqm", value := .gap }
  , { walsCode := "per", iso := "pip", value := .gap }
  , { walsCode := "prs", iso := "pes", value := .gap }
  , { walsCode := "prh", iso := "myp", value := .nonReduction }
  , { walsCode := "pit", iso := "pjt", value := .gap }
  , { walsCode := "qim", iso := "qvi", value := .gap }
  , { walsCode := "ram", iso := "rma", value := .nonReduction }
  , { walsCode := "rap", iso := "rap", value := .gap }
  , { walsCode := "rus", iso := "rus", value := .relativePronoun }
  , { walsCode := "san", iso := "sag", value := .gap }
  , { walsCode := "snm", iso := "xsu", value := .nonReduction }
  , { walsCode := "see", iso := "trv", value := .gap }
  , { walsCode := "sla", iso := "den", value := .nonReduction }
  , { walsCode := "so", iso := "teu", value := .gap }
  , { walsCode := "stn", iso := "nso", value := .gap }
  , { walsCode := "spa", iso := "spa", value := .gap }
  , { walsCode := "sup", iso := "spp", value := .nonReduction }
  , { walsCode := "swa", iso := "swh", value := .gap }
  , { walsCode := "tag", iso := "tgl", value := .gap }
  , { walsCode := "tes", iso := "teo", value := .gap }
  , { walsCode := "tha", iso := "tha", value := .gap }
  , { walsCode := "tuk", iso := "", value := .gap }
  , { walsCode := "tur", iso := "tur", value := .gap }
  , { walsCode := "ung", iso := "ung", value := .gap }
  , { walsCode := "usa", iso := "wnu", value := .nonReduction }
  , { walsCode := "ven", iso := "ven", value := .gap }
  , { walsCode := "vie", iso := "vie", value := .gap }
  , { walsCode := "wra", iso := "wba", value := .nonReduction }
  , { walsCode := "wrd", iso := "wrr", value := .gap }
  , { walsCode := "war", iso := "pav", value := .gap }
  , { walsCode := "wrn", iso := "wnd", value := .gap }
  , { walsCode := "wic", iso := "wic", value := .gap }
  , { walsCode := "ygr", iso := "ygr", value := .gap }
  , { walsCode := "yaq", iso := "yaq", value := .gap }
  , { walsCode := "yid", iso := "yii", value := .nonReduction }
  , { walsCode := "yim", iso := "yee", value := .gap }
  , { walsCode := "yor", iso := "yor", value := .pronounRetention }
  , { walsCode := "yko", iso := "yux", value := .gap }
  , { walsCode := "zul", iso := "zul", value := .gap }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F122A
