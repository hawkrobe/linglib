import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 123A: Relativization on Obliques
@cite{comrie-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 123A`.

Chapter 123, 112 languages.
-/

namespace Datasets.WALS.F123A

/-- WALS 123A values. -/
inductive ObliqueRelativization where
  /-- Relative pronoun (13 languages). -/
  | relativePronoun
  /-- Non-reduction (14 languages). -/
  | nonReduction
  /-- Pronoun-retention (20 languages). -/
  | pronounRetention
  /-- Gap (55 languages). -/
  | gap
  /-- Not possible (10 languages). -/
  | notPossible
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 123A dataset (112 languages). -/
def allData : List (Datapoint ObliqueRelativization) :=
  [ { walsCode := "abk", iso := "abk", value := .gap }
  , { walsCode := "ace", iso := "ace", value := .gap }
  , { walsCode := "aco", iso := "kjq", value := .relativePronoun }
  , { walsCode := "ala", iso := "amp", value := .gap }
  , { walsCode := "ame", iso := "aey", value := .nonReduction }
  , { walsCode := "any", iso := "anu", value := .pronounRetention }
  , { walsCode := "aeg", iso := "arz", value := .pronounRetention }
  , { walsCode := "bab", iso := "bav", value := .pronounRetention }
  , { walsCode := "bag", iso := "bmi", value := .pronounRetention }
  , { walsCode := "bak", iso := "bkc", value := .pronounRetention }
  , { walsCode := "bam", iso := "bam", value := .nonReduction }
  , { walsCode := "brs", iso := "bsn", value := .gap }
  , { walsCode := "bsq", iso := "eus", value := .notPossible }
  , { walsCode := "bkr", iso := "btx", value := .notPossible }
  , { walsCode := "bma", iso := "tzm", value := .gap }
  , { walsCode := "bob", iso := "bni", value := .gap }
  , { walsCode := "blq", iso := "bol", value := .pronounRetention }
  , { walsCode := "bul", iso := "bul", value := .relativePronoun }
  , { walsCode := "brm", iso := "mya", value := .gap }
  , { walsCode := "cnl", iso := "ram", value := .nonReduction }
  , { walsCode := "cha", iso := "cha", value := .gap }
  , { walsCode := "cle", iso := "cle", value := .gap }
  , { walsCode := "die", iso := "dih", value := .nonReduction }
  , { walsCode := "eng", iso := "eng", value := .relativePronoun }
  , { walsCode := "epe", iso := "sja", value := .nonReduction }
  , { walsCode := "eve", iso := "evn", value := .gap }
  , { walsCode := "ewa", iso := "ewe", value := .pronounRetention }
  , { walsCode := "fin", iso := "fin", value := .relativePronoun }
  , { walsCode := "fre", iso := "fra", value := .relativePronoun }
  , { walsCode := "fur", iso := "fvr", value := .gap }
  , { walsCode := "gae", iso := "gla", value := .pronounRetention }
  , { walsCode := "geo", iso := "kat", value := .relativePronoun }
  , { walsCode := "ger", iso := "deu", value := .relativePronoun }
  , { walsCode := "goo", iso := "gni", value := .nonReduction }
  , { walsCode := "grk", iso := "ell", value := .relativePronoun }
  , { walsCode := "grw", iso := "kal", value := .gap }
  , { walsCode := "gua", iso := "gug", value := .pronounRetention }
  , { walsCode := "hau", iso := "hau", value := .pronounRetention }
  , { walsCode := "heb", iso := "heb", value := .pronounRetention }
  , { walsCode := "hin", iso := "hin", value := .nonReduction }
  , { walsCode := "hix", iso := "hix", value := .nonReduction }
  , { walsCode := "hun", iso := "hun", value := .relativePronoun }
  , { walsCode := "hzb", iso := "huz", value := .gap }
  , { walsCode := "ika", iso := "arh", value := .nonReduction }
  , { walsCode := "imo", iso := "imn", value := .gap }
  , { walsCode := "ind", iso := "ind", value := .gap }
  , { walsCode := "ing", iso := "inh", value := .gap }
  , { walsCode := "iri", iso := "gle", value := .pronounRetention }
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
  , { walsCode := "kob", iso := "kpw", value := .gap }
  , { walsCode := "kor", iso := "kor", value := .gap }
  , { walsCode := "kfe", iso := "kfz", value := .gap }
  , { walsCode := "kch", iso := "khq", value := .gap }
  , { walsCode := "kse", iso := "ses", value := .gap }
  , { walsCode := "kro", iso := "kgo", value := .pronounRetention }
  , { walsCode := "knm", iso := "kun", value := .gap }
  , { walsCode := "kxo", iso := "xuu", value := .gap }
  , { walsCode := "lkt", iso := "lkt", value := .nonReduction }
  , { walsCode := "lan", iso := "laj", value := .pronounRetention }
  , { walsCode := "lat", iso := "lav", value := .relativePronoun }
  , { walsCode := "lav", iso := "lvk", value := .nonReduction }
  , { walsCode := "lez", iso := "lez", value := .gap }
  , { walsCode := "lin", iso := "lin", value := .pronounRetention }
  , { walsCode := "luo", iso := "luo", value := .pronounRetention }
  , { walsCode := "mle", iso := "mdy", value := .gap }
  , { walsCode := "maa", iso := "mas", value := .gap }
  , { walsCode := "mal", iso := "plt", value := .notPossible }
  , { walsCode := "mnd", iso := "cmn", value := .gap }
  , { walsCode := "mao", iso := "mri", value := .gap }
  , { walsCode := "map", iso := "arn", value := .gap }
  , { walsCode := "mrt", iso := "vma", value := .notPossible }
  , { walsCode := "may", iso := "ayz", value := .gap }
  , { walsCode := "mei", iso := "mni", value := .gap }
  , { walsCode := "mxc", iso := "mig", value := .gap }
  , { walsCode := "miy", iso := "mkf", value := .pronounRetention }
  , { walsCode := "mna", iso := "mnb", value := .gap }
  , { walsCode := "nbb", iso := "nmb", value := .gap }
  , { walsCode := "ndy", iso := "djk", value := .gap }
  , { walsCode := "ngi", iso := "wyb", value := .gap }
  , { walsCode := "nug", iso := "nuy", value := .gap }
  , { walsCode := "orh", iso := "hae", value := .gap }
  , { walsCode := "pms", iso := "pma", value := .pronounRetention }
  , { walsCode := "per", iso := "pip", value := .gap }
  , { walsCode := "prs", iso := "pes", value := .pronounRetention }
  , { walsCode := "prh", iso := "myp", value := .notPossible }
  , { walsCode := "pit", iso := "pjt", value := .gap }
  , { walsCode := "qim", iso := "qvi", value := .gap }
  , { walsCode := "rus", iso := "rus", value := .relativePronoun }
  , { walsCode := "see", iso := "trv", value := .notPossible }
  , { walsCode := "sla", iso := "den", value := .nonReduction }
  , { walsCode := "spa", iso := "spa", value := .relativePronoun }
  , { walsCode := "sup", iso := "spp", value := .nonReduction }
  , { walsCode := "swa", iso := "swh", value := .notPossible }
  , { walsCode := "tag", iso := "tgl", value := .notPossible }
  , { walsCode := "tha", iso := "tha", value := .gap }
  , { walsCode := "tuk", iso := "", value := .gap }
  , { walsCode := "tur", iso := "tur", value := .gap }
  , { walsCode := "ung", iso := "ung", value := .gap }
  , { walsCode := "usa", iso := "wnu", value := .nonReduction }
  , { walsCode := "wra", iso := "wba", value := .notPossible }
  , { walsCode := "war", iso := "pav", value := .gap }
  , { walsCode := "yko", iso := "yux", value := .notPossible }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F123A
