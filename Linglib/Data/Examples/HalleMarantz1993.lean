import Linglib.Data.Examples.Schema

/-!
# `HalleMarantz1993` — typed example data

Auto-generated from `Linglib/Data/Examples/HalleMarantz1993.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HalleMarantz1993.Examples`.
-/

namespace HalleMarantz1993.Examples

open Data.Examples

def beat_past_participle : LinguisticExample :=
  { id := "hallemarantz1993_beat_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beaten"
    discourseSegments := []
    glossedTokens := [("beat-en", "beat-PST.PTCP")]
    translation := "past participle of 'beat'"
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "past_participle"), ("suffix", "-n")]
    comment := "Halle & Marantz 1993 (7), row 'Past participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def beat_past_finite : LinguisticExample :=
  { id := "hallemarantz1993_beat_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beat"
    discourseSegments := []
    glossedTokens := [("beat", "beat.PST")]
    translation := "finite past of 'beat'"
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "past_finite"), ("suffix", "∅")]
    comment := "Halle & Marantz 1993 (7), row 'Past finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def beat_nonpast_3sg : LinguisticExample :=
  { id := "hallemarantz1993_beat_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beats"
    discourseSegments := []
    glossedTokens := [("beat-s", "beat-3SG.PRS")]
    translation := "third-singular present of 'beat'"
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "nonpast_3sg"), ("suffix", "-z")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite 3rd sg': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def beat_nonpast_participle : LinguisticExample :=
  { id := "hallemarantz1993_beat_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beating"
    discourseSegments := []
    glossedTokens := [("beat-ing", "beat-PRS.PTCP")]
    translation := "present participle of 'beat'"
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "nonpast_participle"), ("suffix", "-ing")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def beat_nonpast_finite : LinguisticExample :=
  { id := "hallemarantz1993_beat_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "beat"
    discourseSegments := []
    glossedTokens := [("beat", "beat.PRS")]
    translation := "present of 'beat'"
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "beat"), ("part", "nonpast_finite"), ("suffix", "∅")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def put_past_participle : LinguisticExample :=
  { id := "hallemarantz1993_put_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "put"
    discourseSegments := []
    glossedTokens := [("put", "put.PST.PTCP")]
    translation := "past participle of 'put'"
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "past_participle"), ("suffix", "∅")]
    comment := "Halle & Marantz 1993 (7), row 'Past participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def put_past_finite : LinguisticExample :=
  { id := "hallemarantz1993_put_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "put"
    discourseSegments := []
    glossedTokens := [("put", "put.PST")]
    translation := "finite past of 'put'"
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "past_finite"), ("suffix", "∅")]
    comment := "Halle & Marantz 1993 (7), row 'Past finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def put_nonpast_3sg : LinguisticExample :=
  { id := "hallemarantz1993_put_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "puts"
    discourseSegments := []
    glossedTokens := [("put-s", "put-3SG.PRS")]
    translation := "third-singular present of 'put'"
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "nonpast_3sg"), ("suffix", "-z")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite 3rd sg': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def put_nonpast_participle : LinguisticExample :=
  { id := "hallemarantz1993_put_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "putting"
    discourseSegments := []
    glossedTokens := [("putt-ing", "put-PRS.PTCP")]
    translation := "present participle of 'put'"
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "nonpast_participle"), ("suffix", "-ing")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def put_nonpast_finite : LinguisticExample :=
  { id := "hallemarantz1993_put_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "put"
    discourseSegments := []
    glossedTokens := [("put", "put.PRS")]
    translation := "present of 'put'"
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "put"), ("part", "nonpast_finite"), ("suffix", "∅")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def dwell_past_participle : LinguisticExample :=
  { id := "hallemarantz1993_dwell_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwelt"
    discourseSegments := []
    glossedTokens := [("dwel-t", "dwell-PST.PTCP")]
    translation := "past participle of 'dwell'"
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "past_participle"), ("suffix", "-t")]
    comment := "Halle & Marantz 1993 (7), row 'Past participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def dwell_past_finite : LinguisticExample :=
  { id := "hallemarantz1993_dwell_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwelt"
    discourseSegments := []
    glossedTokens := [("dwel-t", "dwell-PST")]
    translation := "finite past of 'dwell'"
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "past_finite"), ("suffix", "-t")]
    comment := "Halle & Marantz 1993 (7), row 'Past finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def dwell_nonpast_3sg : LinguisticExample :=
  { id := "hallemarantz1993_dwell_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwells"
    discourseSegments := []
    glossedTokens := [("dwell-s", "dwell-3SG.PRS")]
    translation := "third-singular present of 'dwell'"
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "nonpast_3sg"), ("suffix", "-z")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite 3rd sg': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def dwell_nonpast_participle : LinguisticExample :=
  { id := "hallemarantz1993_dwell_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwelling"
    discourseSegments := []
    glossedTokens := [("dwell-ing", "dwell-PRS.PTCP")]
    translation := "present participle of 'dwell'"
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "nonpast_participle"), ("suffix", "-ing")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def dwell_nonpast_finite : LinguisticExample :=
  { id := "hallemarantz1993_dwell_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "dwell"
    discourseSegments := []
    glossedTokens := [("dwell", "dwell.PRS")]
    translation := "present of 'dwell'"
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "dwell"), ("part", "nonpast_finite"), ("suffix", "∅")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def play_past_participle : LinguisticExample :=
  { id := "hallemarantz1993_play_past_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "played"
    discourseSegments := []
    glossedTokens := [("play-ed", "play-PST.PTCP")]
    translation := "past participle of 'play'"
    context := "Row 'Past participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "past_participle"), ("suffix", "-d")]
    comment := "Halle & Marantz 1993 (7), row 'Past participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def play_past_finite : LinguisticExample :=
  { id := "hallemarantz1993_play_past_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "played"
    discourseSegments := []
    glossedTokens := [("play-ed", "play-PST")]
    translation := "finite past of 'play'"
    context := "Row 'Past finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "past_finite"), ("suffix", "-d")]
    comment := "Halle & Marantz 1993 (7), row 'Past finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def play_nonpast_3sg : LinguisticExample :=
  { id := "hallemarantz1993_play_nonpast_3sg"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "plays"
    discourseSegments := []
    glossedTokens := [("play-s", "play-3SG.PRS")]
    translation := "third-singular present of 'play'"
    context := "Row 'Nonpast finite 3rd sg' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "nonpast_3sg"), ("suffix", "-z")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite 3rd sg': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def play_nonpast_participle : LinguisticExample :=
  { id := "hallemarantz1993_play_nonpast_participle"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "playing"
    discourseSegments := []
    glossedTokens := [("play-ing", "play-PRS.PTCP")]
    translation := "present participle of 'play'"
    context := "Row 'Nonpast participle' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "nonpast_participle"), ("suffix", "-ing")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast participle': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def play_nonpast_finite : LinguisticExample :=
  { id := "hallemarantz1993_play_nonpast_finite"
    source := ⟨"halle-marantz-1993", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "play"
    discourseSegments := []
    glossedTokens := [("play", "play.PRS")]
    translation := "present of 'play'"
    context := "Row 'Nonpast finite' of the principal-parts table."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "play"), ("part", "nonpast_finite"), ("suffix", "∅")]
    comment := "Halle & Marantz 1993 (7), row 'Nonpast finite': the suffix is the paper's own segmentation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [beat_past_participle, beat_past_finite, beat_nonpast_3sg, beat_nonpast_participle, beat_nonpast_finite, put_past_participle, put_past_finite, put_nonpast_3sg, put_nonpast_participle, put_nonpast_finite, dwell_past_participle, dwell_past_finite, dwell_nonpast_3sg, dwell_nonpast_participle, dwell_nonpast_finite, play_past_participle, play_past_finite, play_nonpast_3sg, play_nonpast_participle, play_nonpast_finite]

end HalleMarantz1993.Examples
