import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 142A: Para-Linguistic Usages of Clicks
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 142A`.

Chapter 142, 143 languages.
-/

namespace Datasets.WALS.F142A

/-- WALS 142A values. -/
inductive ParaLinguisticUsagesOfClicks where
  /-- Logical meanings (47 languages). -/
  | logicalMeanings
  /-- Affective meanings (71 languages). -/
  | affectiveMeanings
  /-- Other or none (25 languages). -/
  | otherOrNone
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 142A dataset (143 languages). -/
def allData : List (Datapoint ParaLinguisticUsagesOfClicks) :=
  [ { walsCode := "alb", iso := "sqi", value := .logicalMeanings }
  , { walsCode := "ame", iso := "aey", value := .affectiveMeanings }
  , { walsCode := "ami", iso := "ami", value := .otherOrNone }
  , { walsCode := "abh", iso := "abv", value := .logicalMeanings }
  , { walsCode := "ako", iso := "acy", value := .logicalMeanings }
  , { walsCode := "arl", iso := "apc", value := .logicalMeanings }
  , { walsCode := "amr", iso := "ary", value := .logicalMeanings }
  , { walsCode := "ars", iso := "ayn", value := .logicalMeanings }
  , { walsCode := "atu", iso := "aeb", value := .logicalMeanings }
  , { walsCode := "akm", iso := "rmz", value := .affectiveMeanings }
  , { walsCode := "aul", iso := "aul", value := .affectiveMeanings }
  , { walsCode := "ava", iso := "ava", value := .logicalMeanings }
  , { walsCode := "bgv", iso := "kva", value := .logicalMeanings }
  , { walsCode := "bal", iso := "ban", value := .affectiveMeanings }
  , { walsCode := "bam", iso := "bam", value := .logicalMeanings }
  , { walsCode := "bmn", iso := "bax", value := .affectiveMeanings }
  , { walsCode := "bej", iso := "bej", value := .logicalMeanings }
  , { walsCode := "bel", iso := "byw", value := .otherOrNone }
  , { walsCode := "ben", iso := "ben", value := .logicalMeanings }
  , { walsCode := "btk", iso := "lbk", value := .otherOrNone }
  , { walsCode := "bos", iso := "bos", value := .logicalMeanings }
  , { walsCode := "bra", iso := "brb", value := .affectiveMeanings }
  , { walsCode := "bul", iso := "bul", value := .logicalMeanings }
  , { walsCode := "cnt", iso := "yue", value := .affectiveMeanings }
  , { walsCode := "chc", iso := "che", value := .logicalMeanings }
  , { walsCode := "cck", iso := "cic", value := .otherOrNone }
  , { walsCode := "chx", iso := "clo", value := .affectiveMeanings }
  , { walsCode := "cze", iso := "ces", value := .affectiveMeanings }
  , { walsCode := "dgr", iso := "dta", value := .otherOrNone }
  , { walsCode := "dsh", iso := "dan", value := .affectiveMeanings }
  , { walsCode := "dge", iso := "gsg", value := .affectiveMeanings }
  , { walsCode := "dut", iso := "nld", value := .affectiveMeanings }
  , { walsCode := "dyu", iso := "dyu", value := .logicalMeanings }
  , { walsCode := "eng", iso := "eng", value := .affectiveMeanings }
  , { walsCode := "fef", iso := "fmp", value := .affectiveMeanings }
  , { walsCode := "fiw", iso := "wyy", value := .affectiveMeanings }
  , { walsCode := "fin", iso := "fin", value := .affectiveMeanings }
  , { walsCode := "fbf", iso := "fuh", value := .logicalMeanings }
  , { walsCode := "fua", iso := "fub", value := .affectiveMeanings }
  , { walsCode := "geo", iso := "kat", value := .logicalMeanings }
  , { walsCode := "ger", iso := "deu", value := .affectiveMeanings }
  , { walsCode := "gvi", iso := "bar", value := .affectiveMeanings }
  , { walsCode := "gho", iso := "aaa", value := .logicalMeanings }
  , { walsCode := "gcy", iso := "ell", value := .logicalMeanings }
  , { walsCode := "grk", iso := "ell", value := .logicalMeanings }
  , { walsCode := "gue", iso := "", value := .logicalMeanings }
  , { walsCode := "gfr", iso := "gcr", value := .affectiveMeanings }
  , { walsCode := "gji", iso := "gue", value := .otherOrNone }
  , { walsCode := "gro", iso := "goa", value := .logicalMeanings }
  , { walsCode := "hlu", iso := "hur", value := .otherOrNone }
  , { walsCode := "hau", iso := "hau", value := .affectiveMeanings }
  , { walsCode := "heb", iso := "heb", value := .logicalMeanings }
  , { walsCode := "hin", iso := "hin", value := .logicalMeanings }
  , { walsCode := "hmd", iso := "mww", value := .affectiveMeanings }
  , { walsCode := "hmo", iso := "hnj", value := .affectiveMeanings }
  , { walsCode := "hun", iso := "hun", value := .affectiveMeanings }
  , { walsCode := "hzb", iso := "huz", value := .logicalMeanings }
  , { walsCode := "hpd", iso := "jup", value := .otherOrNone }
  , { walsCode := "igb", iso := "ibo", value := .affectiveMeanings }
  , { walsCode := "ilo", iso := "ilo", value := .affectiveMeanings }
  , { walsCode := "inj", iso := "ind", value := .affectiveMeanings }
  , { walsCode := "ing", iso := "inh", value := .logicalMeanings }
  , { walsCode := "iri", iso := "gle", value := .affectiveMeanings }
  , { walsCode := "ita", iso := "ita", value := .logicalMeanings }
  , { walsCode := "itb", iso := "egl", value := .logicalMeanings }
  , { walsCode := "ifi", iso := "ita", value := .logicalMeanings }
  , { walsCode := "itg", iso := "lij", value := .logicalMeanings }
  , { walsCode := "itn", iso := "nap", value := .logicalMeanings }
  , { walsCode := "jah", iso := "jhi", value := .affectiveMeanings }
  , { walsCode := "jpn", iso := "jpn", value := .affectiveMeanings }
  , { walsCode := "klq", iso := "kmh", value := .affectiveMeanings }
  , { walsCode := "knd", iso := "kan", value := .affectiveMeanings }
  , { walsCode := "ket", iso := "ket", value := .otherOrNone }
  , { walsCode := "kty", iso := "kca", value := .otherOrNone }
  , { walsCode := "khm", iso := "khm", value := .affectiveMeanings }
  , { walsCode := "kmu", iso := "kjg", value := .affectiveMeanings }
  , { walsCode := "khu", iso := "cnk", value := .affectiveMeanings }
  , { walsCode := "klv", iso := "kij", value := .affectiveMeanings }
  , { walsCode := "kil", iso := "lub", value := .affectiveMeanings }
  , { walsCode := "kij", iso := "gia", value := .otherOrNone }
  , { walsCode := "kou", iso := "bkm", value := .affectiveMeanings }
  , { walsCode := "kor", iso := "kor", value := .affectiveMeanings }
  , { walsCode := "kfe", iso := "kfz", value := .logicalMeanings }
  , { walsCode := "lah", iso := "lhu", value := .otherOrNone }
  , { walsCode := "lkt", iso := "lkt", value := .otherOrNone }
  , { walsCode := "lns", iso := "lns", value := .affectiveMeanings }
  , { walsCode := "lao", iso := "lao", value := .affectiveMeanings }
  , { walsCode := "lav", iso := "lvk", value := .affectiveMeanings }
  , { walsCode := "lov", iso := "lbo", value := .affectiveMeanings }
  , { walsCode := "lye", iso := "lee", value := .logicalMeanings }
  , { walsCode := "mad", iso := "mhi", value := .affectiveMeanings }
  , { walsCode := "mal", iso := "plt", value := .affectiveMeanings }
  , { walsCode := "myk", iso := "zlm", value := .affectiveMeanings }
  , { walsCode := "mym", iso := "mal", value := .logicalMeanings }
  , { walsCode := "mlt", iso := "mlt", value := .logicalMeanings }
  , { walsCode := "mla", iso := "", value := .affectiveMeanings }
  , { walsCode := "mnk", iso := "emk", value := .logicalMeanings }
  , { walsCode := "may", iso := "ayz", value := .affectiveMeanings }
  , { walsCode := "mbz", iso := "mtk", value := .affectiveMeanings }
  , { walsCode := "mei", iso := "mni", value := .otherOrNone }
  , { walsCode := "hok", iso := "nan", value := .affectiveMeanings }
  , { walsCode := "min", iso := "min", value := .affectiveMeanings }
  , { walsCode := "mlm", iso := "mra", value := .otherOrNone }
  , { walsCode := "mon", iso := "mnw", value := .otherOrNone }
  , { walsCode := "moo", iso := "mos", value := .logicalMeanings }
  , { walsCode := "mdb", iso := "dmw", value := .otherOrNone }
  , { walsCode := "nez", iso := "nez", value := .otherOrNone }
  , { walsCode := "nif", iso := "num", value := .affectiveMeanings }
  , { walsCode := "nvs", iso := "niv", value := .otherOrNone }
  , { walsCode := "ood", iso := "ood", value := .affectiveMeanings }
  , { walsCode := "oi", iso := "oyb", value := .affectiveMeanings }
  , { walsCode := "oya", iso := "ory", value := .logicalMeanings }
  , { walsCode := "pms", iso := "pma", value := .affectiveMeanings }
  , { walsCode := "prs", iso := "pes", value := .logicalMeanings }
  , { walsCode := "prh", iso := "myp", value := .otherOrNone }
  , { walsCode := "fma", iso := "fuc", value := .logicalMeanings }
  , { walsCode := "rus", iso := "rus", value := .affectiveMeanings }
  , { walsCode := "slb", iso := "sbe", value := .affectiveMeanings }
  , { walsCode := "sam", iso := "smo", value := .affectiveMeanings }
  , { walsCode := "sml", iso := "sza", value := .otherOrNone }
  , { walsCode := "scr", iso := "hbs", value := .logicalMeanings }
  , { walsCode := "svk", iso := "slk", value := .affectiveMeanings }
  , { walsCode := "som", iso := "som", value := .logicalMeanings }
  , { walsCode := "spa", iso := "spa", value := .affectiveMeanings }
  , { walsCode := "spc", iso := "spa", value := .affectiveMeanings }
  , { walsCode := "sra", iso := "srn", value := .logicalMeanings }
  , { walsCode := "swa", iso := "swh", value := .affectiveMeanings }
  , { walsCode := "swe", iso := "swe", value := .affectiveMeanings }
  , { walsCode := "tab", iso := "mky", value := .affectiveMeanings }
  , { walsCode := "tag", iso := "tgl", value := .otherOrNone }
  , { walsCode := "tel", iso := "tel", value := .logicalMeanings }
  , { walsCode := "ter", iso := "ttr", value := .affectiveMeanings }
  , { walsCode := "tha", iso := "tha", value := .affectiveMeanings }
  , { walsCode := "tsz", iso := "ddo", value := .logicalMeanings }
  , { walsCode := "tuk", iso := "", value := .affectiveMeanings }
  , { walsCode := "tur", iso := "tur", value := .logicalMeanings }
  , { walsCode := "udh", iso := "ude", value := .otherOrNone }
  , { walsCode := "wch", iso := "mzh", value := .otherOrNone }
  , { walsCode := "yba", iso := "yam", value := .affectiveMeanings }
  , { walsCode := "ydd", iso := "ydd", value := .affectiveMeanings }
  , { walsCode := "yor", iso := "yor", value := .affectiveMeanings }
  , { walsCode := "yko", iso := "yux", value := .otherOrNone }
  , { walsCode := "zsq", iso := "zab", value := .affectiveMeanings }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F142A
