/-!
# WALS Feature 10B: Nasal Vowels in West Africa
@cite{wals-2013}

Auto-generated from WALS v2020.4 CLDF data.
**Do not edit by hand** — regenerate with `python3 scripts/gen_wals.py 10B`.

Chapter 10, 40 languages.
-/

namespace Core.WALS.F10B

/-- WALS 10B values. -/
inductive NasalVowelsInWestAfrica where
  | noNasalVsOralVowelContrast  -- no nasal vs. oral vowel contrast (20 languages)
  | twoWayNasalVsOralVowelContrastWithoutNasalSpreading  -- two-way nasal vs. oral vowel contrast (/ṽ/ vs. /V/) without nasal spreading (7 languages)
  | twoWayNasalVsOralVowelContrastWithNasalSpreading  -- two-way nasal vs. oral vowel contrast (/ṽ/ vs. /V/) with nasal spreading (4 languages)
  | fourWayNasalVsOralVowelContrastWithoutNasalSpreading  -- four-way nasal vs. oral vowel contrast (/ṽ/ vs. /ṽː/ vs. /V/ vs. /Vː/) without nasal spreading (5 languages)
  | fourWayNasalVsOralVowelContrastWithNasalSpreading  -- four-way nasal vs. oral vowel contrast (/ṽ/ vs. /ṽː/ vs. /V/ v /Vː/) with nasal spreading (4 languages)
  deriving DecidableEq, BEq, Repr

/-- A single WALS 10B datapoint. -/
structure Datapoint where
  walsCode : String
  language : String
  iso : String
  value : NasalVowelsInWestAfrica
  deriving Repr, BEq, DecidableEq

/-- Complete WALS 10B dataset (40 languages). -/
def allData : List Datapoint :=
  [ { walsCode := "aka", language := "Aka", iso := "axk", value := .noNasalVsOralVowelContrast }
  , { walsCode := "avt", language := "Avatime", iso := "avn", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "bfi", language := "Bafia", iso := "ksf", value := .noNasalVsOralVowelContrast }
  , { walsCode := "blz", language := "Balanta", iso := "", value := .noNasalVsOralVowelContrast }
  , { walsCode := "ban", language := "Bana", iso := "bcw", value := .noNasalVsOralVowelContrast }
  , { walsCode := "ble", language := "Baoulé", iso := "bci", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "bsr", language := "Basari", iso := "bsc", value := .noNasalVsOralVowelContrast }
  , { walsCode := "bfd", language := "Biafada", iso := "bif", value := .noNasalVsOralVowelContrast }
  , { walsCode := "buy", language := "Buli (in Ghana)", iso := "bwu", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "dga", language := "Dagaare", iso := "dga", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "dgb", language := "Dagbani", iso := "dag", value := .noNasalVsOralVowelContrast }
  , { walsCode := "day", language := "Day", iso := "dai", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "doy", language := "Doyayo", iso := "dow", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "ebi", language := "Ebira", iso := "igb", value := .noNasalVsOralVowelContrast }
  , { walsCode := "ega", language := "Ega", iso := "ega", value := .noNasalVsOralVowelContrast }
  , { walsCode := "gad", language := "Gade", iso := "ged", value := .noNasalVsOralVowelContrast }
  , { walsCode := "gbk", language := "Gbaya (Northwest)", iso := "gya", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "gir", language := "Gula Iro", iso := "glj", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "grm", language := "Gurma", iso := "gux", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "kis", language := "Kisi", iso := "kss", value := .noNasalVsOralVowelContrast }
  , { walsCode := "krn", language := "Korana", iso := "kqz", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "ksp", language := "Kosop", iso := "kia", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "ktk", language := "Kotoko", iso := "aal", value := .noNasalVsOralVowelContrast }
  , { walsCode := "laa", language := "Laal", iso := "gdm", value := .noNasalVsOralVowelContrast }
  , { walsCode := "lam", language := "Lamé", iso := "lme", value := .noNasalVsOralVowelContrast }
  , { walsCode := "lok", language := "Loko", iso := "lok", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "mdz", language := "Mada (in Nigeria)", iso := "mda", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "mdk", language := "Mandinka", iso := "mnk", value := .noNasalVsOralVowelContrast }
  , { walsCode := "mby", language := "Mbay", iso := "myb", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "mdo", language := "Mbodomo", iso := "gmm", value := .twoWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "moo", language := "Mooré", iso := "mos", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "oku", language := "Oku", iso := "oku", value := .noNasalVsOralVowelContrast }
  , { walsCode := "pod", language := "Podoko", iso := "pbi", value := .noNasalVsOralVowelContrast }
  , { walsCode := "fma", language := "Pulaar", iso := "fuc", value := .noNasalVsOralVowelContrast }
  , { walsCode := "snd", language := "Senadi", iso := "sef", value := .fourWayNasalVsOralVowelContrastWithNasalSpreading }
  , { walsCode := "tne", language := "Temne", iso := "tem", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "tik", language := "Tikar", iso := "tik", value := .noNasalVsOralVowelContrast }
  , { walsCode := "dts", language := "Toro So", iso := "dts", value := .fourWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "wmn", language := "Wéménugbé", iso := "wem", value := .twoWayNasalVsOralVowelContrastWithoutNasalSpreading }
  , { walsCode := "yem", language := "Yemba", iso := "ybb", value := .noNasalVsOralVowelContrast }
  ]

-- Count verification
theorem total_count : allData.length = 40 := by native_decide

theorem count_noNasalVsOralVowelContrast :
    (allData.filter (·.value == .noNasalVsOralVowelContrast)).length = 20 := by native_decide
theorem count_twoWayNasalVsOralVowelContrastWithoutNasalSpreading :
    (allData.filter (·.value == .twoWayNasalVsOralVowelContrastWithoutNasalSpreading)).length = 7 := by native_decide
theorem count_twoWayNasalVsOralVowelContrastWithNasalSpreading :
    (allData.filter (·.value == .twoWayNasalVsOralVowelContrastWithNasalSpreading)).length = 4 := by native_decide
theorem count_fourWayNasalVsOralVowelContrastWithoutNasalSpreading :
    (allData.filter (·.value == .fourWayNasalVsOralVowelContrastWithoutNasalSpreading)).length = 5 := by native_decide
theorem count_fourWayNasalVsOralVowelContrastWithNasalSpreading :
    (allData.filter (·.value == .fourWayNasalVsOralVowelContrastWithNasalSpreading)).length = 4 := by native_decide

/-- Look up a language by WALS code. -/
def lookup (code : String) : Option Datapoint :=
  allData.find? (·.walsCode == code)

/-- Look up a language by ISO 639-3 code. -/
def lookupISO (iso : String) : Option Datapoint :=
  allData.find? (·.iso == iso)

end Core.WALS.F10B
