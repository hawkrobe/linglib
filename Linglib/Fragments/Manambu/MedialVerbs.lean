import Linglib.Syntax.Clause.Chaining

/-!
# Manambu Medial Clause Markers [aikhenvald-2008]

Medial clause markers (clause chain linkers) in Manambu (Ndu family, East Sepik,
Papua New Guinea). Data from [aikhenvald-2008] and [sarvasy-aikhenvald-2025].

Manambu has a rich system of medial clause markers that encode:
1. **Switch-reference**: SS (same subject) vs. DS (different subject), or neutral
2. **Temporal/logical relation**: completive, cotemporaneous, immediate sequence,
   reason, condition
3. **Subject agreement**: some DS markers trigger subject agreement on the
   medial verb; SS markers do not

## Inventory ([sarvasy-aikhenvald-2025]: Table 3)

| Form | SR | Meaning | Subject marking |
|------|-----|---------|-----------------|
| -ku | SS | temporal completive 'after' | no |
| -k | DS | reason, real condition | yes |
| -ta:y | SS | cotemporaneous 'while' | no |
| -taka | SS | immediate sequence 'as soon as, just as' | no |
| -kab | DS | brief temporal overlap 'as soon as' | yes |
| -ta:y-kab | SS | brief temporal overlap 'as soon as' | no |
| -lak | neutral | reason, consequence 'because, so' | yes |
| -ga:y | SS | unlikely condition 'if' | no |
| -n | neutral | sequential or simultaneous, manner | no |

The language's clause-chaining system (`chaining`) is read off this inventory where it can be:
the switch-reference type from the SS and DS markers, its obligatoriness from the absence of
neutral markers, the agreement profile from the markers that index the subject, and the marked
relations from the markers' relations.
-/

namespace Manambu.MedialVerbs

open Clause.Chaining (InterclauseRelation)

/-- Switch-reference value on a medial clause marker. -/
inductive SRValue where
  | ss       -- same subject as following clause
  | ds       -- different subject from following clause
  | neutral  -- not sensitive to subject continuity
  deriving DecidableEq, Repr, Inhabited

/-- A medial clause marker entry in Manambu. -/
structure MarkerEntry where
  /-- Morphological form (suffix on the medial verb). -/
  form : String
  /-- Switch-reference value. -/
  sr : SRValue
  /-- Semantic relation gloss. -/
  gloss : String
  /-- The interclausal relations the marker encodes. -/
  relations : List InterclauseRelation
  /-- Whether subject agreement appears on the medial verb with this marker. -/
  hasSubjectMarking : Bool
  deriving Repr, BEq

/-! ### Marker inventory ([sarvasy-aikhenvald-2025]: Table 3) -/

/-- -ku: SS, temporal completive 'after'. No subject marking. -/
def ku : MarkerEntry :=
  { form := "-ku", sr := .ss, gloss := "after (completive)", relations := [.sequential],
    hasSubjectMarking := false }

/-- -k: DS, reason or real condition. Subject marking on medial verb. -/
def k : MarkerEntry :=
  { form := "-k", sr := .ds, gloss := "reason/real condition",
    relations := [.causal, .conditional], hasSubjectMarking := true }

/-- -ta:y: SS, cotemporaneous 'while'. No subject marking. -/
def tay : MarkerEntry :=
  { form := "-ta:y", sr := .ss, gloss := "while (cotemporaneous)", relations := [.simultaneous],
    hasSubjectMarking := false }

/-- -taka: SS, immediate sequence 'as soon as, just as'. No subject marking. -/
def taka : MarkerEntry :=
  { form := "-taka", sr := .ss, gloss := "as soon as (immediate sequence)",
    relations := [.sequential], hasSubjectMarking := false }

/-- -kab: DS, brief temporal overlap 'as soon as'. Subject marking present. -/
def kab : MarkerEntry :=
  { form := "-kab", sr := .ds, gloss := "as soon as (brief overlap)",
    relations := [.sequential], hasSubjectMarking := true }

/-- -ta:y-kab: SS, brief temporal overlap 'as soon as'. No subject marking.
    Morphologically complex: cotemporaneous -ta:y + overlap -kab. -/
def tayKab : MarkerEntry :=
  { form := "-ta:y-kab", sr := .ss, gloss := "as soon as (brief overlap)",
    relations := [.sequential], hasSubjectMarking := false }

/-- -lak: neutral (not SR-sensitive), reason/consequence 'because, so'.
    Subject marking present. -/
def lak : MarkerEntry :=
  { form := "-lak", sr := .neutral, gloss := "because/so (reason/consequence)",
    relations := [.causal], hasSubjectMarking := true }

/-- -ga:y: SS, unlikely condition 'if (unlikely)'. No subject marking. -/
def gay : MarkerEntry :=
  { form := "-ga:y", sr := .ss, gloss := "if (unlikely condition)", relations := [.conditional],
    hasSubjectMarking := false }

/-- -n: neutral (not SR-sensitive), sequential or simultaneous action, manner.
    No subject marking. The most semantically general medial marker. -/
def n : MarkerEntry :=
  { form := "-n", sr := .neutral, gloss := "and/while/by (sequential/simultaneous/manner)",
    relations := [.sequential, .simultaneous, .manner], hasSubjectMarking := false }

/-- All medial clause markers. -/
def allMarkers : List MarkerEntry :=
  [ku, k, tay, taka, kab, tayKab, lak, gay, n]

/-! ### Derived properties -/

/-- SS markers. -/
def ssMarkers : List MarkerEntry := allMarkers.filter (·.sr == .ss)

/-- DS markers. -/
def dsMarkers : List MarkerEntry := allMarkers.filter (·.sr == .ds)

/-- Neutral markers (not SR-sensitive). -/
def neutralMarkers : List MarkerEntry := allMarkers.filter (·.sr == .neutral)

/-- Markers that trigger subject agreement. -/
def markersWithSubjAgreement : List MarkerEntry :=
  allMarkers.filter (·.hasSubjectMarking)

/-- Manambu's clause-chaining system: medial-final chains with a binary switch-reference system
that two neutral markers escape, medial verbs partially inflected for the subject under
different-subject marking, relative tense fused with the marking, no mood or aspect, a dedicated
dependent-clause negator, both bridging constructions, and dependent clauses on their own
([sarvasy-aikhenvald-2025] Ch. 6, [aikhenvald-2008]). -/
def chaining : Clause.Chaining.System where
  direction := .medialFinal
  srSystem := if dsMarkers.isEmpty then .none else .ssDs
  srTarget := some .subjectOnly
  srObligatory := neutralMarkers.isEmpty
  srMarkedness := some .ssUnmarked
  medialMorph := {
    tense := .restricted
    agreement := if markersWithSubjAgreement.isEmpty then .absent
      else if markersWithSubjAgreement.length = allMarkers.length then .full else .restricted
    mood := .absent
    polarity := .restricted
    aspect := .absent }
  relationsMarked := (allMarkers.flatMap (·.relations)).eraseDups
  hasRecapLinkage := true
  hasSummaryLinkage := true
  medialCanStandAlone := true

end Manambu.MedialVerbs
