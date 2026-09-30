module

public import Linglib.Data.Examples.Schema

/-!
# `Anscombe1964` — typed example data

Auto-generated from `Linglib/Data/Examples/Anscombe1964.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Anscombe1964.Examples`.
-/

@[expose] public section

namespace Anscombe1964.Examples

open Data.Examples

def i : LinguisticExample :=
  { id := "anscombe1964_i"
    source := ⟨"anscombe-1964", "§I (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the Parthenon was there before the Dome of the Rock was there, and the Dome of the Rock was there before St. Peter's was there, then the Parthenon was there before St. Peter's was there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "transitivity")]
    comment := "" }

def ii : LinguisticExample :=
  { id := "anscombe1964_ii"
    source := ⟨"anscombe-1964", "§I (ii)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If St. Peter's was there after the Dome of the Rock was there, and the Dome of the Rock was there after the Parthenon was there, then St. Peter's was there after the Parthenon was there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "transitivity")]
    comment := "" }

def mutual_before : LinguisticExample :=
  { id := "anscombe1964_mutual_before"
    source := ⟨"anscombe-1964", "§I"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "St. Peter's was there before the Parthenon was there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "mutual")]
    comment := "Incompatible with the consequent, and hence the antecedent, of (i)." }

def mutual_after : LinguisticExample :=
  { id := "anscombe1964_mutual_after"
    source := ⟨"anscombe-1964", "§I"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The Parthenon was there after St. Peter's was there."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")]
    comment := "Compatible with the consequent and antecedent of (ii): after is not asymmetric." }

def born : LinguisticExample :=
  { id := "anscombe1964_born"
    source := ⟨"anscombe-1964", "§II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was born after the Parthenon was there; the Parthenon was there after I was born; ergo, I was born after I was born."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "transitivity_failure")]
    comment := "After is not unrestrictedly transitive." }

def scout : LinguisticExample :=
  { id := "anscombe1964_scout"
    source := ⟨"anscombe-1964", "§II"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I was a Boy Scout after you were one."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "alternative_verifications")]
    comment := "True if I became one after you did, if I went on after you stopped, or if I was one for a while after you became one." }

def james1 : LinguisticExample :=
  { id := "anscombe1964_james1"
    source := ⟨"anscombe-1964", "§III (1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James began being ill after John began to be ill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "begin_after_begin")]
    comment := "" }

def james2 : LinguisticExample :=
  { id := "anscombe1964_james2"
    source := ⟨"anscombe-1964", "§III (2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James began being ill after John stopped being ill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "begin_after_stop")]
    comment := "" }

def james3 : LinguisticExample :=
  { id := "anscombe1964_james3"
    source := ⟨"anscombe-1964", "§III (3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James was ill after John began to be ill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "overlap_after_begin")]
    comment := "" }

def james4 : LinguisticExample :=
  { id := "anscombe1964_james4"
    source := ⟨"anscombe-1964", "§III (4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "James was ill after John stopped being ill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "verification"), ("verification", "after_stop")]
    comment := "" }

def greece : LinguisticExample :=
  { id := "anscombe1964_greece"
    source := ⟨"anscombe-1964", "§IV"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A time at which I was in Greece was before every time at which you were in Italy."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "quantification")]
    comment := "Right for 'I was in Greece before you were ever in Italy' (§V), stronger than plain 'before'." }

def italy : LinguisticExample :=
  { id := "anscombe1964_italy"
    source := ⟨"anscombe-1964", "§IV"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A time at which you were in Italy was after a time at which I was in Greece."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "quantification")]
    comment := "" }

def glass : LinguisticExample :=
  { id := "anscombe1964_glass"
    source := ⟨"anscombe-1964", "§V"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He studied his appearance in the glass before he used the telephone."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "before"), ("pattern", "before_ever")]
    comment := "Does not suggest that he did so before he ever in his life used the telephone." }

def battle : LinguisticExample :=
  { id := "anscombe1964_battle"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The battle took place after it rained, and it rained after the battle started."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")]
    comment := "Not inconsistent, unlike 'The battle took place after the rain'." }

def quarrel : LinguisticExample :=
  { id := "anscombe1964_quarrel"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I left after they quarreled, and they quarreled after I left."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")]
    comment := "" }

def report : LinguisticExample :=
  { id := "anscombe1964_report"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I arrived after he was reading the report, and he was reading the report after I arrived."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "mutual")]
    comment := "" }

def arrival : LinguisticExample :=
  { id := "anscombe1964_arrival"
    source := ⟨"anscombe-1964", "§VII"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her arrival was after their conversation."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "nominal"), ("instantaneous", "yes")]
    comment := "Events named by nouns: one wholly preceded the other, so before and after are converses." }

def john_tom : LinguisticExample :=
  { id := "anscombe1964_john_tom"
    source := ⟨"anscombe-1964", "§IX"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived somewhere after Tom."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("connective", "after"), ("pattern", "instantaneous"), ("instantaneous", "yes")]
    comment := "No possibility that Tom also arrived after John." }

def all : List LinguisticExample := [i, ii, mutual_before, mutual_after, born, scout, james1, james2, james3, james4, greece, italy, glass, battle, quarrel, report, arrival, john_tom]

end Anscombe1964.Examples
