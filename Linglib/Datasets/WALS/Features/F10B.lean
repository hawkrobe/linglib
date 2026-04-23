import Linglib.Datasets.WALS.Datapoint

/-!
# WALS Feature 10B: Nasal Vowels in West Africa
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 10B`.

Chapter 10, 40 languages.
-/

namespace Datasets.WALS.F10B

/-- WALS 10B values. -/
inductive NasalVowelsInWestAfrica where
  /-- no nasal vs. oral vowel contrast (20 languages). -/
  | noNasalVsOralVowelContrast
  /-- two-way nasal vs. oral vowel contrast (/ṽ/ vs. /V/) without nasal spreading (7 languages). -/
  | twoWayNasalVsOralVowelContrastWithoutNasalSpreading
  /-- two-way nasal vs. oral vowel contrast (/ṽ/ vs. /V/) with nasal spreading (4 languages). -/
  | twoWayNasalVsOralVowelContrastWithNasalSpreading
  /-- four-way nasal vs. oral vowel contrast (/ṽ/ vs. /ṽː/ vs. /V/ vs. /Vː/) without nasal spreading (5 languages). -/
  | fourWayNasalVsOralVowelContrastWithoutNasalSpreading
  /-- four-way nasal vs. oral vowel contrast (/ṽ/ vs. /ṽː/ vs. /V/ v /Vː/) with nasal spreading (4 languages). -/
  | fourWayNasalVsOralVowelContrastWithNasalSpreading
  deriving DecidableEq, BEq, Repr

/-- Complete WALS 10B dataset (40 languages). -/
def allData : List (Datapoint NasalVowelsInWestAfrica) :=
  [ { walsCode := "aka", iso := "axk", value := .noNasalVsOralVowelContrast }
  , { walsCode := "avt", iso := "avn", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "bfi", iso := "ksf", value := .noNasalVsOralVowelContrast }
  , { walsCode := "blz", iso := "", value := .noNasalVsOralVowelContrast }
  , { walsCode := "ban", iso := "bcw", value := .noNasalVsOralVowelContrast }
  , { walsCode := "ble", iso := "bci", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "bsr", iso := "bsc", value := .noNasalVsOralVowelContrast }
  , { walsCode := "bfd", iso := "bif", value := .noNasalVsOralVowelContrast }
  , { walsCode := "buy", iso := "bwu", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "dga", iso := "dga", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "dgb", iso := "dag", value := .noNasalVsOralVowelContrast }
  , { walsCode := "day", iso := "dai", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "doy", iso := "dow", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "ebi", iso := "igb", value := .noNasalVsOralVowelContrast }
  , { walsCode := "ega", iso := "ega", value := .noNasalVsOralVowelContrast }
  , { walsCode := "gad", iso := "ged", value := .noNasalVsOralVowelContrast }
  , { walsCode := "gbk", iso := "gya", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "gir", iso := "glj", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "grm", iso := "gux", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "kis", iso := "kss", value := .noNasalVsOralVowelContrast }
  , { walsCode := "krn", iso := "kqz", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "ksp", iso := "kia", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "ktk", iso := "aal", value := .noNasalVsOralVowelContrast }
  , { walsCode := "laa", iso := "gdm", value := .noNasalVsOralVowelContrast }
  , { walsCode := "lam", iso := "lme", value := .noNasalVsOralVowelContrast }
  , { walsCode := "lok", iso := "lok", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "mdz", iso := "mda", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "mdk", iso := "mnk", value := .noNasalVsOralVowelContrast }
  , { walsCode := "mby", iso := "myb", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "mdo", iso := "gmm", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "moo", iso := "mos", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "oku", iso := "oku", value := .noNasalVsOralVowelContrast }
  , { walsCode := "pod", iso := "pbi", value := .noNasalVsOralVowelContrast }
  , { walsCode := "fma", iso := "fuc", value := .noNasalVsOralVowelContrast }
  , { walsCode := "snd", iso := "sef", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "tne", iso := "tem", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "tik", iso := "tik", value := .noNasalVsOralVowelContrast }
  , { walsCode := "dts", iso := "dts", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "wmn", iso := "wem", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "yem", iso := "ybb", value := .noNasalVsOralVowelContrast }
  ]

/-- Look up a language by WALS code. -/
def lookup (code : String) := Datapoint.lookup allData code

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) := Datapoint.lookupISO allData iso

end Datasets.WALS.F10B
