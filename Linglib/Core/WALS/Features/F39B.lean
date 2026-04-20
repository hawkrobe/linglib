import Linglib.Core.WALS.Datapoint

/-!
# WALS Feature 39B: Inclusive/Exclusive Forms in Pama-Nyungan
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 39B`.

Chapter 39, 71 languages.
-/

namespace Core.WALS.F39B

/-- WALS 39B values. -/
inductive InclusiveExclusiveFormsInPamaNyungan where
  /-- No inclusive/exclusive opposition (31 languages). -/
  | noInclusiveExclusiveOpposition
  /-- Inclusive and exclusive differentiated (40 languages). -/
  | inclusiveAndExclusiveDifferentiated
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 39B dataset (71 languages). -/
def allData : List (Datapoint InclusiveExclusiveFormsInPamaNyungan) :=
  [ { walsCode := "aly", iso := "aly", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "agt", iso := "awg", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "abn", iso := "ard", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "arr", iso := "", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "amp", iso := "aer", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "bxj", iso := "bxj", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "bii", iso := "bzr", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "dhl", iso := "dhl", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "dhr", iso := "dhr", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "diy", iso := "dif", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "dja", iso := "dyy", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "djp", iso := "dwu", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "djr", iso := "ddj", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "dyi", iso := "dbl", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "gid", iso := "gih", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ggd", iso := "ggd", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "gum", iso := "kgs", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "gny", iso := "gyy", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "guf", iso := "guf", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "guu", iso := "kky", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "kgu", iso := "ktg", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "vka", iso := "vka", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "kyt", iso := "gbb", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "knc", iso := "uwa", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "kya", iso := "gvn", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "lnj", iso := "lnj", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mdm", iso := "dmd", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mny", iso := "zmc", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "mrt", iso := "vma", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mbb", iso := "vmb", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "mrj", iso := "nju", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "mdb", iso := "dmw", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "mrw", iso := "zmu", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ngr", iso := "nay", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "nlr", iso := "nrk", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nlu", iso := "nrl", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "ngw", iso := "nxn", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ngi", iso := "wyb", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nha", iso := "nha", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "nly", iso := "nly", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nyr", iso := "nna", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nya", iso := "nyt", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "nju", iso := "nys", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "pkn", iso := "drl", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "bly", iso := "nad", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "pny", iso := "pnw", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "pit", iso := "pjt", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ppi", iso := "pit", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ump", iso := "ump", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "uhi", iso := "urf", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wkw", iso := "wkw", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wlm", iso := "wmt", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wgg", iso := "wgg", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wbt", iso := "wbt", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wrl", iso := "wbp", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wrg", iso := "wgy", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wgu", iso := "wrg", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wru", iso := "wrm", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wat", iso := "wbv", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wem", iso := "xww", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wdo", iso := "pjt", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "wmu", iso := "wim", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "wwr", iso := "wyi", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "ylr", iso := "ylr", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yny", iso := "jao", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "yyg", iso := "xya", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yid", iso := "yii", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yin", iso := "yij", value := .inclusiveAndExclusiveDifferentiated }
  , { walsCode := "yng", iso := "yia", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "ylb", iso := "mpj", value := .noInclusiveExclusiveOpposition }
  , { walsCode := "yuw", iso := "kld", value := .inclusiveAndExclusiveDifferentiated }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Core.WALS.F39B
