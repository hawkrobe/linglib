import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 110A: Periphrastic Causative Constructions
@cite{song-2013-periphrastic}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 110A`.

Chapter 110, 118 languages.
-/

namespace Datasets.WALS.F110A

/-- WALS 110A values. -/
inductive PeriphrasticCausativeType where
  /-- Sequential but no purposive (35 languages). -/
  | sequentialOnly
  /-- Purposive but no sequential (68 languages). -/
  | purposiveOnly
  /-- Both (15 languages). -/
  | both
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 110A dataset (118 languages). -/
def allData : List (Datapoint PeriphrasticCausativeType) :=
  [ { walsCode := "abk", iso := "abk", value := .purposiveOnly }
  , { walsCode := "aji", iso := "aji", value := .purposiveOnly }
  , { walsCode := "ame", iso := "aey", value := .sequentialOnly }
  , { walsCode := "aeg", iso := "arz", value := .purposiveOnly }
  , { walsCode := "arm", iso := "hye", value := .purposiveOnly }
  , { walsCode := "atc", iso := "upv", value := .sequentialOnly }
  , { walsCode := "awn", iso := "awn", value := .purposiveOnly }
  , { walsCode := "bab", iso := "bav", value := .sequentialOnly }
  , { walsCode := "bag", iso := "bmi", value := .sequentialOnly }
  , { walsCode := "bsq", iso := "eus", value := .purposiveOnly }
  , { walsCode := "bkr", iso := "btx", value := .purposiveOnly }
  , { walsCode := "brm", iso := "mya", value := .purposiveOnly }
  , { walsCode := "cha", iso := "cha", value := .purposiveOnly }
  , { walsCode := "die", iso := "dih", value := .sequentialOnly }
  , { walsCode := "diy", iso := "dif", value := .sequentialOnly }
  , { walsCode := "djr", iso := "ddj", value := .purposiveOnly }
  , { walsCode := "eng", iso := "eng", value := .sequentialOnly }
  , { walsCode := "epe", iso := "sja", value := .sequentialOnly }
  , { walsCode := "ewe", iso := "ewe", value := .sequentialOnly }
  , { walsCode := "fij", iso := "fij", value := .purposiveOnly }
  , { walsCode := "fin", iso := "fin", value := .purposiveOnly }
  , { walsCode := "geo", iso := "kat", value := .purposiveOnly }
  , { walsCode := "ger", iso := "deu", value := .sequentialOnly }
  , { walsCode := "goo", iso := "gni", value := .purposiveOnly }
  , { walsCode := "grk", iso := "ell", value := .purposiveOnly }
  , { walsCode := "hau", iso := "hau", value := .sequentialOnly }
  , { walsCode := "heb", iso := "heb", value := .purposiveOnly }
  , { walsCode := "hin", iso := "hin", value := .purposiveOnly }
  , { walsCode := "hmo", iso := "hnj", value := .sequentialOnly }
  , { walsCode := "hun", iso := "hun", value := .both }
  , { walsCode := "igb", iso := "ibo", value := .sequentialOnly }
  , { walsCode := "ika", iso := "arh", value := .purposiveOnly }
  , { walsCode := "ind", iso := "ind", value := .sequentialOnly }
  , { walsCode := "iri", iso := "gle", value := .purposiveOnly }
  , { walsCode := "jak", iso := "jac", value := .both }
  , { walsCode := "knd", iso := "kan", value := .purposiveOnly }
  , { walsCode := "knr", iso := "knc", value := .sequentialOnly }
  , { walsCode := "kay", iso := "gyd", value := .purposiveOnly }
  , { walsCode := "khm", iso := "khm", value := .both }
  , { walsCode := "kmu", iso := "kjg", value := .sequentialOnly }
  , { walsCode := "klv", iso := "kij", value := .sequentialOnly }
  , { walsCode := "kin", iso := "kin", value := .both }
  , { walsCode := "krb", iso := "gil", value := .purposiveOnly }
  , { walsCode := "kob", iso := "kpw", value := .sequentialOnly }
  , { walsCode := "kol", iso := "kfb", value := .purposiveOnly }
  , { walsCode := "kor", iso := "kor", value := .purposiveOnly }
  , { walsCode := "kfe", iso := "kfz", value := .sequentialOnly }
  , { walsCode := "kse", iso := "ses", value := .both }
  , { walsCode := "kro", iso := "kgo", value := .purposiveOnly }
  , { walsCode := "knm", iso := "kun", value := .both }
  , { walsCode := "lah", iso := "lhu", value := .purposiveOnly }
  , { walsCode := "lan", iso := "laj", value := .both }
  , { walsCode := "lat", iso := "lav", value := .purposiveOnly }
  , { walsCode := "lav", iso := "lvk", value := .sequentialOnly }
  , { walsCode := "lep", iso := "lep", value := .purposiveOnly }
  , { walsCode := "let", iso := "lti", value := .sequentialOnly }
  , { walsCode := "lez", iso := "lez", value := .purposiveOnly }
  , { walsCode := "lim", iso := "lif", value := .purposiveOnly }
  , { walsCode := "maa", iso := "mas", value := .purposiveOnly }
  , { walsCode := "mal", iso := "plt", value := .purposiveOnly }
  , { walsCode := "mnm", iso := "mva", value := .sequentialOnly }
  , { walsCode := "mao", iso := "mri", value := .purposiveOnly }
  , { walsCode := "mhi", iso := "mar", value := .purposiveOnly }
  , { walsCode := "mrt", iso := "vma", value := .purposiveOnly }
  , { walsCode := "may", iso := "ayz", value := .sequentialOnly }
  , { walsCode := "mxc", iso := "mig", value := .sequentialOnly }
  , { walsCode := "mul", iso := "mlm", value := .sequentialOnly }
  , { walsCode := "mrl", iso := "mur", value := .purposiveOnly }
  , { walsCode := "nht", iso := "nhg", value := .purposiveOnly }
  , { walsCode := "nav", iso := "nav", value := .sequentialOnly }
  , { walsCode := "ndy", iso := "djk", value := .sequentialOnly }
  , { walsCode := "ngi", iso := "wyb", value := .purposiveOnly }
  , { walsCode := "nym", iso := "nym", value := .purposiveOnly }
  , { walsCode := "ond", iso := "one", value := .purposiveOnly }
  , { walsCode := "orh", iso := "hae", value := .purposiveOnly }
  , { walsCode := "otm", iso := "ote", value := .purposiveOnly }
  , { walsCode := "pms", iso := "pma", value := .sequentialOnly }
  , { walsCode := "psm", iso := "pqm", value := .sequentialOnly }
  , { walsCode := "pau", iso := "pad", value := .purposiveOnly }
  , { walsCode := "prs", iso := "pes", value := .purposiveOnly }
  , { walsCode := "prh", iso := "myp", value := .purposiveOnly }
  , { walsCode := "ram", iso := "rma", value := .purposiveOnly }
  , { walsCode := "rej", iso := "rej", value := .sequentialOnly }
  , { walsCode := "ret", iso := "tnc", value := .purposiveOnly }
  , { walsCode := "rus", iso := "rus", value := .purposiveOnly }
  , { walsCode := "src", iso := "srs", value := .purposiveOnly }
  , { walsCode := "shk", iso := "shp", value := .purposiveOnly }
  , { walsCode := "shn", iso := "sna", value := .purposiveOnly }
  , { walsCode := "shu", iso := "shs", value := .purposiveOnly }
  , { walsCode := "spa", iso := "spa", value := .both }
  , { walsCode := "sup", iso := "spp", value := .both }
  , { walsCode := "swa", iso := "swh", value := .purposiveOnly }
  , { walsCode := "tab", iso := "mky", value := .sequentialOnly }
  , { walsCode := "tag", iso := "tgl", value := .purposiveOnly }
  , { walsCode := "tml", iso := "tam", value := .purposiveOnly }
  , { walsCode := "tha", iso := "tha", value := .both }
  , { walsCode := "tib", iso := "bod", value := .purposiveOnly }
  , { walsCode := "tuk", iso := "", value := .both }
  , { walsCode := "tna", iso := "tuv", value := .sequentialOnly }
  , { walsCode := "tur", iso := "tur", value := .purposiveOnly }
  , { walsCode := "tvl", iso := "tvl", value := .both }
  , { walsCode := "tzo", iso := "tzo", value := .purposiveOnly }
  , { walsCode := "ung", iso := "ung", value := .purposiveOnly }
  , { walsCode := "vai", iso := "vai", value := .purposiveOnly }
  , { walsCode := "vie", iso := "vie", value := .both }
  , { walsCode := "wam", iso := "wmb", value := .purposiveOnly }
  , { walsCode := "war", iso := "pav", value := .purposiveOnly }
  , { walsCode := "wrl", iso := "wbp", value := .purposiveOnly }
  , { walsCode := "wic", iso := "wic", value := .purposiveOnly }
  , { walsCode := "wch", iso := "mzh", value := .sequentialOnly }
  , { walsCode := "yap", iso := "yap", value := .sequentialOnly }
  , { walsCode := "yaq", iso := "yaq", value := .purposiveOnly }
  , { walsCode := "yay", iso := "pcc", value := .sequentialOnly }
  , { walsCode := "yid", iso := "yii", value := .purposiveOnly }
  , { walsCode := "yim", iso := "yee", value := .both }
  , { walsCode := "yor", iso := "yor", value := .both }
  , { walsCode := "yuw", iso := "kld", value := .purposiveOnly }
  , { walsCode := "zul", iso := "zul", value := .purposiveOnly }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F110A
