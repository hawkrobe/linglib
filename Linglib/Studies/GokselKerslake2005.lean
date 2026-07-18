import Linglib.Semantics.Tense.Evidential
import Linglib.Fragments.Turkish.TAM
import Linglib.Fragments.Turkish.SuffixTemplate
import Linglib.Fragments.Turkish.VowelHarmony

/-!
# Göksel & Kerslake 2005: Turkish Evidential TAM
[goksel-kerslake-2005] [cumming-2026]

Bridge between Turkish TAM data and [cumming-2026]'s (S, A, T) evidential
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

open Tense.Evidential
open Turkish.TAM

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

/-- -DI is the only category with contemporaneous EP (direct witness). -/
theorem di_unique_direct : diEP = .contemporaneous := rfl

/-- -mIş EP is strictly downstream — evidence comes after the event. -/
theorem miş_indirect : mişEP = .strictDownstream := rfl

-- ============================================================================
-- § 3: The suffix template (Ch 6, 8, 13-14)
-- ============================================================================

/-! Ordering predictions derived from the Fragment templates
(`Turkish.SuffixTemplate.verbTemplate`/`nounTemplate`), checked as
slot-position facts rather than re-typed rank tables. -/

open Turkish.SuffixTemplate

/-- The verbal template has a single TAM slot, so -DI and -mIş — both
TAM-category suffixes — are in complementary distribution: a simplex
verb form cannot carry both. -/
theorem tam_slot_unique :
    verbTemplate.suffixSlots.count .tam = 1 := by decide

/-- Negation strictly precedes TAM in the template, matching the surface
order stem-NEG-TAM: every symmetric negative in the TAM inventory spells
NEG before the TAM suffix (gel-**me**-**di** 'come-NEG-PST'). -/
theorem negation_precedes_tam :
    verbTemplate.suffixSlots.idxOf .negation < verbTemplate.suffixSlots.idxOf .tam ∧
    ∀ e ∈ entries, e.isNegSymmetric → e.negSuffix.data.take 2 = ['-', 'm'] := by decide

/-- The question particle mI fills the outermost verbal slot, following
agreement: gel-di-**m** **mi**? (come-PST-1SG Q). -/
theorem question_is_outermost :
    ∀ s ∈ verbTemplate.suffixSlots,
      verbTemplate.suffixSlots.idxOf s ≤ verbTemplate.suffixSlots.idxOf .question := by
  decide

/-- Nominal ordering: plural before possessive before case
(ev-**ler**-**im**-**de** 'house-PL-1SG.POSS-LOC'). -/
theorem noun_slot_order :
    nounTemplate.suffixSlots.idxOf .plural < nounTemplate.suffixSlots.idxOf .possessive ∧
    nounTemplate.suffixSlots.idxOf .possessive < nounTemplate.suffixSlots.idxOf .case := by
  decide

-- ============================================================================
-- § 4: Vowel harmony resolves TAM suffix vowels
-- ============================================================================

open Turkish.VowelHarmony

/-- The archiphonemic I in progressive -Iyor resolves to 4 surface vowels
by stem harmony: kol → -ıyor, gel → -iyor, kork → -uyor, göz → -üyor. -/
theorem progressive_I_resolution :
    resolveI true  false = ı_vowel ∧
    resolveI false false = i_vowel ∧
    resolveI true  true  = u_vowel ∧
    resolveI false true  = ü_vowel := ⟨rfl, rfl, rfl, rfl⟩

/-- The archiphonemic A in future -(y)AcAK resolves to a/e by palatal
harmony: kol → -(y)acak, gel → -(y)ecek. -/
theorem future_A_resolution :
    resolveA true  = a_vowel ∧
    resolveA false = e_vowel := ⟨rfl, rfl⟩

end GokselKerslake2005
