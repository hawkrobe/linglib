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
  /-- None (1 languages). -/
  | none
  /-- One (3 languages). -/
  | one
  /-- Some (2-5) (10 languages). -/
  | some
  /-- Many (more than 5) (21 languages). -/
  | many
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 139A dataset (35 languages). -/
def allData : List (Datapoint IrregularNegativesInSignLanguages) :=
  [ { walsCode := "ada", iso := "ads", value := .some }
  , { walsCode := "asl", iso := "ase", value := .many }
  , { walsCode := "aus", iso := "asf", value := .many }
  , { walsCode := "bsl", iso := "bfi", value := .many }
  , { walsCode := "csl", iso := "csl", value := .many }
  , { walsCode := "dge", iso := "gsg", value := .many }
  , { walsCode := "fsl", iso := "fse", value := .many }
  , { walsCode := "gsl", iso := "gss", value := .many }
  , { walsCode := "hks", iso := "hks", value := .many }
  , { walsCode := "ics", iso := "icl", value := .some }
  , { walsCode := "ipi", iso := "ins", value := .one }
  , { walsCode := "ipk", iso := "pks", value := .none }
  , { walsCode := "isl", iso := "ils", value := .some }
  , { walsCode := "irs", iso := "isg", value := .some }
  , { walsCode := "iss", iso := "isr", value := .many }
  , { walsCode := "kkl", iso := "bqy", value := .one }
  , { walsCode := "lsf", iso := "fsl", value := .many }
  , { walsCode := "lsq", iso := "fcs", value := .many }
  , { walsCode := "lsa", iso := "aed", value := .many }
  , { walsCode := "lse", iso := "ssp", value := .one }
  , { walsCode := "lii", iso := "ise", value := .some }
  , { walsCode := "lgh", iso := "jos", value := .some }
  , { walsCode := "lsb", iso := "bzs", value := .many }
  , { walsCode := "ned", iso := "dse", value := .some }
  , { walsCode := "nzs", iso := "nzs", value := .many }
  , { walsCode := "nih", iso := "jsl", value := .many }
  , { walsCode := "rsl", iso := "rsl", value := .many }
  , { walsCode := "ssl", iso := "kvk", value := .many }
  , { walsCode := "svt", iso := "swl", value := .many }
  , { walsCode := "tzi", iso := "tss", value := .many }
  , { walsCode := "tsl", iso := "tza", value := .some }
  , { walsCode := "ths", iso := "tsq", value := .some }
  , { walsCode := "tui", iso := "tsm", value := .some }
  , { walsCode := "ugs", iso := "ugn", value := .many }
  , { walsCode := "vla", iso := "vgt", value := .many }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F139A
