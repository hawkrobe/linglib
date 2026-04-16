import Linglib.Theories.Semantics.Tense.Evidential
import Linglib.Fragments.Turkish.TAM

/-!
# Göksel & Kerslake 2005: Turkish Evidential TAM
@cite{goksel-kerslake-2005} @cite{cumming-2026}

Bridge between Turkish TAM data and @cite{cumming-2026}'s (S, A, T) evidential
framework. The key prediction: Turkish -DI and -mIş differ in their
**evidential perspective constraint** (EPCondition), not primarily in their
temporal (UPCondition) constraint.

## The -DI / -mIş contrast

- **-DI** (past definite): speaker directly witnessed the event. Evidence
  was acquired contemporaneously with the event (A overlaps T).
  EPCondition: `contemporaneous`.

- **-mIş** (evidential): speaker did not witness the event. Evidence
  was acquired strictly after the event (A > T).
  EPCondition: `strictDownstream`.

Both share the same utterance perspective: past (T < S). The evidential
dimension is what distinguishes them — a prediction from the (S, A, T)
framework applied to Turkish.
-/

namespace GokselKerslake2005

open Semantics.Tense.Evidential
open Fragments.Turkish.TAM

-- ============================================================================
-- § 1: EP/UP assignments for Turkish TAM
-- ============================================================================

/-- Turkish -DI (witnessed past): contemporaneous evidence acquisition.
    The speaker was present at the time of the event. -/
def diEP : EPCondition := .contemporaneous

/-- Turkish -mIş (indirect/reportative): strictly downstream evidence.
    The speaker learned about the event after it occurred. -/
def mişEP : EPCondition := .strictDownstream

/-- Both -DI and -mIş are past tense: T < S. -/
def diUP : UPCondition := .past
def mişUP : UPCondition := .past

-- ============================================================================
-- § 2: Predictions
-- ============================================================================

/-- -DI and -mIş share temporal constraint but differ in evidential perspective. -/
theorem same_tense_different_evidence :
    diUP = mişUP ∧ diEP ≠ mişEP := by
  exact ⟨rfl, by decide⟩

/-- Both -DI and -mIş occupy the TAM slot in the Turkish suffix template.
    They are in complementary distribution: you cannot have both. -/
theorem di_miş_same_slot :
    let di := (entries.filter (·.category == .pastDef)).head!
    let miş := (entries.filter (·.category == .evidential)).head!
    di.category != miş.category = true := by native_decide

/-- -DI is the only category with contemporaneous EP (direct witness). -/
theorem di_unique_direct : diEP = .contemporaneous := rfl

/-- -mIş EP is strictly downstream — evidence comes after the event. -/
theorem miş_indirect : mişEP = .strictDownstream := rfl

end GokselKerslake2005
