import Linglib.Theories.Semantics.Tense.Basic

/-!
# Kratzer (1998): More Structural Analogies Between Pronouns and Tenses

Kratzer's theory: the simultaneous reading under attitude embedding arises
from **SOT deletion**, not from tense ambiguity or variable binding.
Past tense is always past — it never means "zero tense." When embedded
past morphology is identical to matrix past morphology, a morphological
deletion rule optionally removes the embedded tense, leaving the embedded
clause temporally dependent on the matrix event time.

## Core Mechanisms

1. **SOT deletion**: morphological identity triggers optional deletion of
   embedded tense, yielding the simultaneous reading
2. **Past is always past**: no zero-tense reading — past morphology always
   encodes temporal precedence
3. **Shifted = genuine past**: embedded past without deletion gives R < E_matrix

## Key Distinction from Ogihara

Kratzer and Ogihara make the same SOT predictions (both derive shifted
and simultaneous readings) but differ on what "past" means:
- Kratzer: past is NEVER ambiguous; simultaneous = deletion of past
- Ogihara: past IS ambiguous; simultaneous = zero-tense reading of past

## References

- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
  *SALT VIII*, 92-110.
-/

namespace IntensionalSemantics.Tense.Kratzer

open Core.Tense
open Core.Reichenbach
open IntensionalSemantics.Tense


-- ════════════════════════════════════════════════════════════════
-- § SOT Deletion
-- ════════════════════════════════════════════════════════════════

/-- Kratzer's SOT deletion: when embedded tense morphology is identical
    to matrix tense morphology, the embedded tense can be optionally
    deleted, making the embedded clause temporally dependent on the
    matrix event time.

    `matrixTense`: the tense of the matrix clause
    `embeddedTense`: the tense of the embedded clause
    Returns whether deletion is possible. -/
def sotDeletionApplicable (matrixTense embeddedTense : GramTense) : Bool :=
  matrixTense == embeddedTense

/-- Deletion is applicable for past-under-past (the core SOT case). -/
theorem past_past_deletion :
    sotDeletionApplicable .past .past = true := rfl

/-- Deletion is NOT applicable for present-under-past (no morphological
    identity between present and past). -/
theorem present_past_no_deletion :
    sotDeletionApplicable .past .present = false := rfl

/-- When SOT deletion applies, the embedded reference time becomes
    the matrix event time (the embedded clause inherits matrix temporal
    coordinates). -/
def applyDeletion {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) : ReichenbachFrame Time where
  speechTime := matrixFrame.speechTime
  perspectiveTime := matrixFrame.eventTime
  referenceTime := matrixFrame.eventTime  -- R' = E_matrix after deletion
  eventTime := matrixFrame.eventTime


-- ════════════════════════════════════════════════════════════════
-- § Derivation Theorems
-- ════════════════════════════════════════════════════════════════

/-- Kratzer derives the simultaneous reading via SOT deletion.
    When deletion applies, R' = E_matrix, giving the PRESENT relation. -/
theorem kratzer_derives_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time)
    (hDeletion : sotDeletionApplicable .past .past = true) :
    (applyDeletion matrixFrame).isPresent := by
  simp [applyDeletion, ReichenbachFrame.isPresent]

/-- Kratzer derives the shifted reading: genuine past (no deletion).
    When deletion does not apply (or is not chosen), the embedded
    past tense contributes its own temporal precedence. -/
theorem kratzer_derives_shifted {Time : Type*} [LinearOrder Time]
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time)
    (hPast : embeddedR < matrixFrame.eventTime) :
    (embeddedFrame matrixFrame embeddedR embeddedE).isPast := by
  simp [embeddedFrame, ReichenbachFrame.isPast]
  exact hPast

/-- SOT deletion yields the simultaneous reading: R' = E_matrix. -/
theorem kratzer_deletion_yields_simultaneous {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) :
    (applyDeletion matrixFrame).referenceTime = matrixFrame.eventTime :=
  rfl

-- ════════════════════════════════════════════════════════════════
-- § Theory Identity Card
-- ════════════════════════════════════════════════════════════════

/-- Kratzer (1998) theory identity card. -/
def KratzerTense : TenseTheory where
  name := "Kratzer 1998"
  citation := "Kratzer, A. (1998). More structural analogies between pronouns and tenses. SALT VIII, 92-110."
  hasTemporalDeRe := false
  hasULC := false
  hasZeroTense := false
  hasSOTDeletion := true
  simultaneousMechanism := "SOT deletion of morphologically identical embedded tense"

/-- Kratzer's key claim: past is NEVER zero tense. The simultaneous
    reading comes from deletion, not from an ambiguity in what "past"
    means. This is a categorical structural difference from Ogihara. -/
theorem kratzer_no_zero_tense :
    KratzerTense.hasZeroTense = false := rfl

/-- Kratzer uses deletion (not ambiguity) for the simultaneous reading. -/
theorem kratzer_uses_deletion :
    KratzerTense.hasSOTDeletion = true := rfl


end IntensionalSemantics.Tense.Kratzer
