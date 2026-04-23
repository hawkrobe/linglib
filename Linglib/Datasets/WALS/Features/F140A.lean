import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 140A: Question Particles in Sign Languages
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 140A`.

Chapter 140, 38 languages.
-/

namespace Datasets.WALS.F140A

/-- WALS 140A values. -/
inductive QuestionParticlesInSignLanguages where
  /-- None (25 languages). -/
  | none
  /-- One (9 languages). -/
  | one
  /-- More than one (4 languages). -/
  | moreThanOne
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 140A dataset (38 languages). -/
def allData : List (Datapoint QuestionParticlesInSignLanguages) :=
  [ { walsCode := "ada", iso := "ads", value := .none }
  , { walsCode := "asl", iso := "ase", value := .one }
  , { walsCode := "aus", iso := "asf", value := .none }
  , { walsCode := "bsl", iso := "bfi", value := .none }
  , { walsCode := "csl", iso := "csl", value := .moreThanOne }
  , { walsCode := "dge", iso := "gsg", value := .none }
  , { walsCode := "fsl", iso := "fse", value := .one }
  , { walsCode := "gsl", iso := "gss", value := .none }
  , { walsCode := "hks", iso := "hks", value := .moreThanOne }
  , { walsCode := "ics", iso := "icl", value := .none }
  , { walsCode := "ipi", iso := "ins", value := .none }
  , { walsCode := "irs", iso := "isg", value := .none }
  , { walsCode := "iss", iso := "isr", value := .none }
  , { walsCode := "kkl", iso := "bqy", value := .none }
  , { walsCode := "ksl", iso := "xki", value := .one }
  , { walsCode := "lsf", iso := "fsl", value := .none }
  , { walsCode := "lsq", iso := "fcs", value := .none }
  , { walsCode := "lsa", iso := "aed", value := .none }
  , { walsCode := "lse", iso := "ssp", value := .one }
  , { walsCode := "lii", iso := "ise", value := .none }
  , { walsCode := "lgh", iso := "jos", value := .none }
  , { walsCode := "lgp", iso := "psr", value := .none }
  , { walsCode := "lsb", iso := "bzs", value := .none }
  , { walsCode := "ned", iso := "dse", value := .none }
  , { walsCode := "nzs", iso := "nzs", value := .none }
  , { walsCode := "nih", iso := "jsl", value := .one }
  , { walsCode := "nte", iso := "nsl", value := .none }
  , { walsCode := "psl", iso := "psd", value := .one }
  , { walsCode := "rsl", iso := "rsl", value := .none }
  , { walsCode := "ssl", iso := "kvk", value := .moreThanOne }
  , { walsCode := "svt", iso := "swl", value := .none }
  , { walsCode := "tzi", iso := "tss", value := .moreThanOne }
  , { walsCode := "tsl", iso := "tza", value := .one }
  , { walsCode := "ths", iso := "tsq", value := .none }
  , { walsCode := "tui", iso := "tsm", value := .one }
  , { walsCode := "ugs", iso := "ugn", value := .none }
  , { walsCode := "usl", iso := "uks", value := .one }
  , { walsCode := "vla", iso := "vgt", value := .none }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F140A
