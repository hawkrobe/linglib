/-!
# Manambu Medial Clause Markers @cite{aikhenvald-2008}


Medial clause markers (clause chain linkers) in Manambu (Ndu family, East Sepik,
Papua New Guinea). Data from @cite{aikhenvald-2008} and @cite{sarvasy-aikhenvald-2025}.

Manambu has a rich system of medial clause markers that encode:
1. **Switch-reference**: SS (same subject) vs. DS (different subject), or neutral
2. **Temporal/logical relation**: completive, cotemporaneous, immediate sequence,
   reason, condition
3. **Subject agreement**: some DS markers trigger subject agreement on the
   medial verb; SS markers do not

## Inventory (@cite{sarvasy-aikhenvald-2025}: Table 3)

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

-/

namespace Fragments.Manambu.MedialVerbs

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
  /-- Whether subject agreement appears on the medial verb with this marker. -/
  hasSubjectMarking : Bool
  deriving Repr, BEq

-- ============================================================================
-- § Marker inventory (@cite{sarvasy-aikhenvald-2025}: Table 3)
-- ============================================================================

/-- -ku: SS, temporal completive 'after'. No subject marking. -/
def ku : MarkerEntry :=
  { form := "-ku", sr := .ss, gloss := "after (completive)", hasSubjectMarking := false }

/-- -k: DS, reason or real condition. Subject marking on medial verb. -/
def k : MarkerEntry :=
  { form := "-k", sr := .ds, gloss := "reason/real condition", hasSubjectMarking := true }

/-- -ta:y: SS, cotemporaneous 'while'. No subject marking. -/
def tay : MarkerEntry :=
  { form := "-ta:y", sr := .ss, gloss := "while (cotemporaneous)", hasSubjectMarking := false }

/-- -taka: SS, immediate sequence 'as soon as, just as'. No subject marking. -/
def taka : MarkerEntry :=
  { form := "-taka", sr := .ss, gloss := "as soon as (immediate sequence)", hasSubjectMarking := false }

/-- -kab: DS, brief temporal overlap 'as soon as'. Subject marking present. -/
def kab : MarkerEntry :=
  { form := "-kab", sr := .ds, gloss := "as soon as (brief overlap)", hasSubjectMarking := true }

/-- -ta:y-kab: SS, brief temporal overlap 'as soon as'. No subject marking.
    Morphologically complex: cotemporaneous -ta:y + overlap -kab. -/
def tayKab : MarkerEntry :=
  { form := "-ta:y-kab", sr := .ss, gloss := "as soon as (brief overlap)", hasSubjectMarking := false }

/-- -lak: neutral (not SR-sensitive), reason/consequence 'because, so'.
    Subject marking present. -/
def lak : MarkerEntry :=
  { form := "-lak", sr := .neutral, gloss := "because/so (reason/consequence)", hasSubjectMarking := true }

/-- -ga:y: SS, unlikely condition 'if (unlikely)'. No subject marking. -/
def gay : MarkerEntry :=
  { form := "-ga:y", sr := .ss, gloss := "if (unlikely condition)", hasSubjectMarking := false }

/-- -n: neutral (not SR-sensitive), sequential or simultaneous action, manner.
    No subject marking. The most semantically general medial marker. -/
def n : MarkerEntry :=
  { form := "-n", sr := .neutral, gloss := "and/while/by (sequential/simultaneous/manner)", hasSubjectMarking := false }

/-- All medial clause markers. -/
def allMarkers : List MarkerEntry :=
  [ku, k, tay, taka, kab, tayKab, lak, gay, n]

-- ============================================================================
-- § Derived properties
-- ============================================================================

/-- SS markers. -/
def ssMarkers : List MarkerEntry := allMarkers.filter (·.sr == .ss)

/-- DS markers. -/
def dsMarkers : List MarkerEntry := allMarkers.filter (·.sr == .ds)

/-- Neutral markers (not SR-sensitive). -/
def neutralMarkers : List MarkerEntry := allMarkers.filter (·.sr == .neutral)

/-- Markers that trigger subject agreement. -/
def markersWithSubjAgreement : List MarkerEntry :=
  allMarkers.filter (·.hasSubjectMarking)

-- ============================================================================
-- § Verification theorems
-- ============================================================================

/-- 9 medial clause markers in total. -/
theorem marker_count : allMarkers.length = 9 := rfl

/-- 5 SS markers. -/
theorem ss_count : ssMarkers.length = 5 := rfl

/-- 2 DS markers. -/
theorem ds_count : dsMarkers.length = 2 := rfl

/-- 2 neutral markers. -/
theorem neutral_count : neutralMarkers.length = 2 := rfl

/-- 9 = 5 + 2 + 2: SS + DS + neutral exhausts the inventory. -/
theorem sr_partition :
    ssMarkers.length + dsMarkers.length + neutralMarkers.length
    = allMarkers.length := rfl

/-- No SS marker triggers subject agreement. -/
theorem ss_no_subject_marking :
    ssMarkers.all (! ·.hasSubjectMarking) = true := rfl

/-- Every DS marker triggers subject agreement. -/
theorem ds_has_subject_marking :
    dsMarkers.all (·.hasSubjectMarking) = true := rfl

/-- Subject marking correlates with DS or neutral status: it never appears
    with SS. This reflects the structural logic — when subjects are the same,
    marking the subject on the medial verb would be redundant. -/
theorem subject_marking_implies_not_ss :
    markersWithSubjAgreement.all (·.sr != .ss) = true := rfl

end Fragments.Manambu.MedialVerbs
