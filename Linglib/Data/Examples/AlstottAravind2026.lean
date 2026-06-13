import Linglib.Data.Examples.Schema

/-!
# `AlstottAravind2026` — typed example data

Auto-generated from `Linglib/Data/Examples/AlstottAravind2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlstottAravind2026.Examples`.
-/

namespace AlstottAravind2026.Examples

open Data.Examples

def before_stative : LinguisticExample :=
  { id := "alstottaravind2026_before_stative"
    source := ⟨"rett-2020", "UNVERIFIED"⟩
    reportedIn := some ⟨"alstott-aravind-2026", "UNVERIFIED"⟩
    language := "stan1293"
    primaryText := "John left before she was president."
    discourseSegments := []
    glossedTokens := []
    translation := "John left before she was president."
    context := "*Before* with a stative embedded clause: the default before-start reading (ME precedes the onset of EE) is the only salient one; no coercion operator is involved."
    judgment := .acceptable
    alternatives := []
    readings := [("before-start (default)", .acceptable)]
    paperFeatures := [("connective", "before"), ("clause", "embedded"), ("vendler_class", "state"), ("default_reading", "before-start")]
    comment := "Schematic illustration of Rett 2020's telicity-sensitive default readings for *before*/*after*; sentence not verified verbatim against either paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def before_accomplishment : LinguisticExample :=
  { id := "alstottaravind2026_before_accomplishment"
    source := ⟨"rett-2020", "UNVERIFIED"⟩
    reportedIn := some ⟨"alstott-aravind-2026", "UNVERIFIED Exp. 2"⟩
    language := "stan1293"
    primaryText := "John left before she climbed the mountain."
    discourseSegments := []
    glossedTokens := []
    translation := "John left before she climbed the mountain."
    context := "*Before* with a telic (accomplishment) embedded clause: before-start is the default; the before-finish reading requires the covert COMPLET operator and incurs a processing cost (Alstott & Aravind 2026, Exp. 2)."
    judgment := .acceptable
    alternatives := []
    readings := [("before-start (default)", .acceptable), ("before-finish (COMPLET)", .acceptable)]
    paperFeatures := [("connective", "before"), ("clause", "embedded"), ("vendler_class", "accomplishment"), ("default_reading", "before-start"), ("coercion", "COMPLET"), ("coerced_reading", "before-finish")]
    comment := "Schematic illustration of Rett 2020's telicity-sensitive default readings for *before*/*after*; the COMPLET condition is the one tested in Alstott & Aravind 2026 Exp. 2. Sentence not verified verbatim against either paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def after_stative : LinguisticExample :=
  { id := "alstottaravind2026_after_stative"
    source := ⟨"rett-2020", "UNVERIFIED"⟩
    reportedIn := some ⟨"alstott-aravind-2026", "UNVERIFIED Exp. 4"⟩
    language := "stan1293"
    primaryText := "John left after she was surprised."
    discourseSegments := []
    glossedTokens := []
    translation := "John left after she was surprised."
    context := "*After* with a stative (atelic) embedded clause: after-finish is the default; the after-start reading requires the covert INCHOAT operator and incurs a processing cost (Alstott & Aravind 2026, Exp. 4)."
    judgment := .acceptable
    alternatives := []
    readings := [("after-finish (default)", .acceptable), ("after-start (INCHOAT)", .acceptable)]
    paperFeatures := [("connective", "after"), ("clause", "embedded"), ("vendler_class", "state"), ("default_reading", "after-finish"), ("coercion", "INCHOAT"), ("coerced_reading", "after-start")]
    comment := "Schematic illustration of Rett 2020's telicity-sensitive default readings for *before*/*after*; the INCHOAT condition is the one tested in Alstott & Aravind 2026 Exp. 4. Sentence not verified verbatim against either paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def after_accomplishment : LinguisticExample :=
  { id := "alstottaravind2026_after_accomplishment"
    source := ⟨"rett-2020", "UNVERIFIED"⟩
    reportedIn := some ⟨"alstott-aravind-2026", "UNVERIFIED"⟩
    language := "stan1293"
    primaryText := "John left after she climbed the mountain."
    discourseSegments := []
    glossedTokens := []
    translation := "John left after she climbed the mountain."
    context := "*After* with a telic (accomplishment) embedded clause: the default after-finish reading (ME follows the telos of EE) is the only salient one; no coercion operator is involved."
    judgment := .acceptable
    alternatives := []
    readings := [("after-finish (default)", .acceptable)]
    paperFeatures := [("connective", "after"), ("clause", "embedded"), ("vendler_class", "accomplishment"), ("default_reading", "after-finish")]
    comment := "Schematic illustration of Rett 2020's telicity-sensitive default readings for *before*/*after*; sentence not verified verbatim against either paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [before_stative, before_accomplishment, after_stative, after_accomplishment]

end AlstottAravind2026.Examples
