import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 140A: Question Particles in Sign Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 140A`.

Chapter 140, 38 languages.
-/

namespace Core.WALS.F140A

/-- WALS 140A values. -/
inductive QuestionParticlesInSignLanguages where
  | none  -- None (25 languages)
  | one  -- One (9 languages)
  | moreThanOne  -- More than one (4 languages)
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 140A dataset (38 languages). -/
def allData : List (Datapoint QuestionParticlesInSignLanguages) :=
  [ { walsCode := "ada", language := "Adamorobe Sign Language", iso := "ads", value := .none }
  , { walsCode := "asl", language := "American Sign Language", iso := "ase", value := .one }
  , { walsCode := "aus", language := "Auslan", iso := "asf", value := .none }
  , { walsCode := "bsl", language := "British Sign Language", iso := "bfi", value := .none }
  , { walsCode := "csl", language := "Chinese Sign Language", iso := "csl", value := .moreThanOne }
  , { walsCode := "dge", language := "Deutsche Gebärdensprache", iso := "gsg", value := .none }
  , { walsCode := "fsl", language := "Finnish Sign Language", iso := "fse", value := .one }
  , { walsCode := "gsl", language := "Greek Sign Language", iso := "gss", value := .none }
  , { walsCode := "hks", language := "Hong Kong Sign Language", iso := "hks", value := .moreThanOne }
  , { walsCode := "ics", language := "Icelandic Sign Language", iso := "icl", value := .none }
  , { walsCode := "ipi", language := "Indo-Pakistani Sign Language (Indian dialects)", iso := "ins", value := .none }
  , { walsCode := "irs", language := "Irish Sign Language", iso := "isg", value := .none }
  , { walsCode := "iss", language := "Israeli Sign Language", iso := "isr", value := .none }
  , { walsCode := "kkl", language := "Kata Kolok", iso := "bqy", value := .none }
  , { walsCode := "ksl", language := "Kenyan Sign Language", iso := "xki", value := .one }
  , { walsCode := "lsf", language := "Langue des Signes Française", iso := "fsl", value := .none }
  , { walsCode := "lsq", language := "Langue des Signes Québecoise", iso := "fcs", value := .none }
  , { walsCode := "lsa", language := "Lengua de Señas Argentina", iso := "aed", value := .none }
  , { walsCode := "lse", language := "Lengua de Señas Española", iso := "ssp", value := .one }
  , { walsCode := "lii", language := "Lingua Italiana dei Segni", iso := "ise", value := .none }
  , { walsCode := "lgh", language := "Lughat al-Isharat al-Lubnaniya", iso := "jos", value := .none }
  , { walsCode := "lgp", language := "Língua Gestual Portuguesa", iso := "psr", value := .none }
  , { walsCode := "lsb", language := "Língua de Sinais Brasileira", iso := "bzs", value := .none }
  , { walsCode := "ned", language := "Nederlandse Gebarentaal", iso := "dse", value := .none }
  , { walsCode := "nzs", language := "New Zealand Sign Language", iso := "nzs", value := .none }
  , { walsCode := "nih", language := "Nihon Shuwa (Japanese Sign Language)", iso := "jsl", value := .one }
  , { walsCode := "nte", language := "Norsk Tegnspråk", iso := "nsl", value := .none }
  , { walsCode := "psl", language := "Plains-Indians Sign Language", iso := "psd", value := .one }
  , { walsCode := "rsl", language := "Russian Sign Language", iso := "rsl", value := .none }
  , { walsCode := "ssl", language := "South Korean Sign Language", iso := "kvk", value := .moreThanOne }
  , { walsCode := "svt", language := "Svenska Teckenspråket", iso := "swl", value := .none }
  , { walsCode := "tzi", language := "Taiwanese Sign Language (Ziran Shouyu)", iso := "tss", value := .moreThanOne }
  , { walsCode := "tsl", language := "Tanzania Sign Language", iso := "tza", value := .one }
  , { walsCode := "ths", language := "Thai Sign Language", iso := "tsq", value := .none }
  , { walsCode := "tui", language := "Türk Isaret Dili", iso := "tsm", value := .one }
  , { walsCode := "ugs", language := "Ugandan Sign Language", iso := "ugn", value := .none }
  , { walsCode := "usl", language := "Urubú Sign Language", iso := "uks", value := .one }
  , { walsCode := "vla", language := "Vlaamse Gebarentaal", iso := "vgt", value := .none }
  ]

-- Count verification
theorem total_count : allData.length = 38 := by native_decide

theorem count_none :
    (allData.filter (·.value == .none)).length = 25 := by native_decide
theorem count_one :
    (allData.filter (·.value == .one)).length = 9 := by native_decide
theorem count_moreThanOne :
    (allData.filter (·.value == .moreThanOne)).length = 4 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F140A
