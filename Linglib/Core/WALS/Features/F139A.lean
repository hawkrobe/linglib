import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 139A: Irregular Negatives in Sign Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 139A`.

Chapter 139, 35 languages.
-/

namespace Core.WALS.F139A

/-- WALS 139A values. -/
inductive IrregularNegativesInSignLanguages where
  | none  -- None (1 languages)
  | one  -- One (3 languages)
  | some  -- Some (2-5) (10 languages)
  | many  -- Many (more than 5) (21 languages)
  deriving DecidableEq, Repr

/-- Complete WALS 139A dataset (35 languages). -/
def allData : List (Datapoint IrregularNegativesInSignLanguages) :=
  [ { walsCode := "ada", language := "Adamorobe Sign Language", iso := "ads", value := .some }
  , { walsCode := "asl", language := "American Sign Language", iso := "ase", value := .many }
  , { walsCode := "aus", language := "Auslan", iso := "asf", value := .many }
  , { walsCode := "bsl", language := "British Sign Language", iso := "bfi", value := .many }
  , { walsCode := "csl", language := "Chinese Sign Language", iso := "csl", value := .many }
  , { walsCode := "dge", language := "Deutsche Gebärdensprache", iso := "gsg", value := .many }
  , { walsCode := "fsl", language := "Finnish Sign Language", iso := "fse", value := .many }
  , { walsCode := "gsl", language := "Greek Sign Language", iso := "gss", value := .many }
  , { walsCode := "hks", language := "Hong Kong Sign Language", iso := "hks", value := .many }
  , { walsCode := "ics", language := "Icelandic Sign Language", iso := "icl", value := .some }
  , { walsCode := "ipi", language := "Indo-Pakistani Sign Language (Indian dialects)", iso := "ins", value := .one }
  , { walsCode := "ipk", language := "Indo-Pakistani Sign Language (Karachi dialect)", iso := "pks", value := .none }
  , { walsCode := "isl", language := "International Sign", iso := "ils", value := .some }
  , { walsCode := "irs", language := "Irish Sign Language", iso := "isg", value := .some }
  , { walsCode := "iss", language := "Israeli Sign Language", iso := "isr", value := .many }
  , { walsCode := "kkl", language := "Kata Kolok", iso := "bqy", value := .one }
  , { walsCode := "lsf", language := "Langue des Signes Française", iso := "fsl", value := .many }
  , { walsCode := "lsq", language := "Langue des Signes Québecoise", iso := "fcs", value := .many }
  , { walsCode := "lsa", language := "Lengua de Señas Argentina", iso := "aed", value := .many }
  , { walsCode := "lse", language := "Lengua de Señas Española", iso := "ssp", value := .one }
  , { walsCode := "lii", language := "Lingua Italiana dei Segni", iso := "ise", value := .some }
  , { walsCode := "lgh", language := "Lughat al-Isharat al-Lubnaniya", iso := "jos", value := .some }
  , { walsCode := "lsb", language := "Língua de Sinais Brasileira", iso := "bzs", value := .many }
  , { walsCode := "ned", language := "Nederlandse Gebarentaal", iso := "dse", value := .some }
  , { walsCode := "nzs", language := "New Zealand Sign Language", iso := "nzs", value := .many }
  , { walsCode := "nih", language := "Nihon Shuwa (Japanese Sign Language)", iso := "jsl", value := .many }
  , { walsCode := "rsl", language := "Russian Sign Language", iso := "rsl", value := .many }
  , { walsCode := "ssl", language := "South Korean Sign Language", iso := "kvk", value := .many }
  , { walsCode := "svt", language := "Svenska Teckenspråket", iso := "swl", value := .many }
  , { walsCode := "tzi", language := "Taiwanese Sign Language (Ziran Shouyu)", iso := "tss", value := .many }
  , { walsCode := "tsl", language := "Tanzania Sign Language", iso := "tza", value := .some }
  , { walsCode := "ths", language := "Thai Sign Language", iso := "tsq", value := .some }
  , { walsCode := "tui", language := "Türk Isaret Dili", iso := "tsm", value := .some }
  , { walsCode := "ugs", language := "Ugandan Sign Language", iso := "ugn", value := .many }
  , { walsCode := "vla", language := "Vlaamse Gebarentaal", iso := "vgt", value := .many }
  ]

-- Count verification
theorem total_count : allData.length = 35 := by native_decide

theorem count_none :
    (allData.filter (·.value == .none)).length = 1 := by native_decide
theorem count_one :
    (allData.filter (·.value == .one)).length = 3 := by native_decide
theorem count_some :
    (allData.filter (·.value == .some)).length = 10 := by native_decide
theorem count_many :
    (allData.filter (·.value == .many)).length = 21 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F139A
