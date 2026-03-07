import Linglib.Fragments.English.FunctionWords
import Linglib.Theories.Semantics.Attitudes.EpistemicThreshold

/-!
# Epistemic Threshold Bridge

Connects the English modal fragment (`Fragments.English.FunctionWords`) to
Ying et al.'s (2025) epistemic threshold semantics
(`Theories.Semantics.Attitudes.EpistemicThreshold`).

## The Bridge

Each English epistemic modal auxiliary maps to an `EpistemicEntry` with a
fitted threshold from Table 1(b). The bridge proves:

1. **Form agreement**: the Fragment's `form` field matches the Theory's `name`
2. **Force–threshold consistency**: necessity-force modals have strictly
   higher thresholds than possibility-force modals on their epistemic reading
3. **Within-force scalar ordering**: threshold ordering captures scalar
   differences (must > should, may > might) that binary force cannot express

## Dependency Direction

    Fragments/English/FunctionWords.lean (AuxEntry, modalMeaning)
                    ↓
    Theories/Semantics/Attitudes/EpistemicThreshold.lean (EpistemicEntry, θ)
                    ↓
    Phenomena/Modality/EpistemicThresholdBridge.lean (this file)
-/

namespace Phenomena.Modality.EpistemicThresholdBridge

open Fragments.English.FunctionWords
open Semantics.Attitudes.EpistemicThreshold (EpistemicEntry)
open Core.ModalLogic (ModalForce ModalFlavor ForceFlavor)

-- ============================================================================
-- §1. Fragment → Theory Mapping
-- ============================================================================

/-- Map an English modal auxiliary to its epistemic threshold entry.
    Only epistemic modals have a threshold; non-epistemic uses (deontic,
    circumstantial) are `none`.

    The mapping derives from the Fragment's `form` field — no duplication
    of lexical data. -/
def toEpistemicEntry (a : AuxEntry) : Option EpistemicEntry :=
  match a.form with
  | "must"   => some .must_
  | "should" => some .should_
  | "may"    => some .may_
  | "might"  => some .might_
  | "could"  => some .could_
  | _        => none

/-- Extract the epistemic force of a modal auxiliary, if it has an
    epistemic reading. Returns `none` for purely deontic/circumstantial
    modals (e.g., `shall`). -/
def epistemicForce (a : AuxEntry) : Option ModalForce :=
  let epMeanings := a.modalMeaning.filter (·.flavor == .epistemic)
  epMeanings.head?.map (·.force)

-- ============================================================================
-- §2. Form Agreement
-- ============================================================================

/-! Per-entry verification: the Fragment's `form` matches the Theory's `name`.
These are true by construction since `toEpistemicEntry` pattern-matches on
the Fragment's form and returns the corresponding Theory entry. -/

theorem must_form : (toEpistemicEntry must).map (·.name) = some "must" := rfl
theorem should_form : (toEpistemicEntry should).map (·.name) = some "should" := rfl
theorem may_form : (toEpistemicEntry may).map (·.name) = some "may" := rfl
theorem might_form : (toEpistemicEntry might).map (·.name) = some "might" := rfl
theorem could_form : (toEpistemicEntry could).map (·.name) = some "could" := rfl

/-- Non-epistemic modals have no threshold entry. -/
theorem shall_no_threshold : toEpistemicEntry shall = none := rfl

-- ============================================================================
-- §3. Force–Threshold Consistency
-- ============================================================================

/-! The key empirical prediction: necessity-force epistemic modals have
strictly higher thresholds than possibility-force epistemic modals.

    □ modals: must (0.95) > should (0.80)
    ◇ modals: may (0.30) > might/could (0.20)
    □ > ◇: should (0.80) > may (0.30)

This connects two independent characterizations of the same items:
- @cite{kratzer-1981}: force is an algebraic property of the modal operator
- @cite{ying-zhi-xuan-wong-mansinghka-tenenbaum-2025}: threshold is a fitted parameter over credence -/

/-- Every necessity-force epistemic modal has a higher threshold than
    every possibility-force epistemic modal. -/
theorem necessity_gt_possibility_must_might :
    EpistemicEntry.must_.θ > EpistemicEntry.might_.θ := by
  show (1 : ℚ)/5 < 19/20; norm_num

theorem necessity_gt_possibility_must_may :
    EpistemicEntry.must_.θ > EpistemicEntry.may_.θ := by
  show (3 : ℚ)/10 < 19/20; norm_num

theorem necessity_gt_possibility_should_might :
    EpistemicEntry.should_.θ > EpistemicEntry.might_.θ := by
  show (1 : ℚ)/5 < 4/5; norm_num

theorem necessity_gt_possibility_should_may :
    EpistemicEntry.should_.θ > EpistemicEntry.may_.θ := by
  show (3 : ℚ)/10 < 4/5; norm_num

theorem necessity_gt_possibility_should_could :
    EpistemicEntry.should_.θ > EpistemicEntry.could_.θ := by
  show (1 : ℚ)/5 < 4/5; norm_num

/-- The epistemic force of `must` is necessity (derived from Fragment). -/
theorem must_is_necessity : epistemicForce must = some .necessity := rfl

/-- The epistemic force of `might` is possibility (derived from Fragment). -/
theorem might_is_possibility : epistemicForce might = some .possibility := rfl

/-- The epistemic force of `should` is weak necessity (derived from Fragment). -/
theorem should_is_weakNecessity : epistemicForce should = some .weakNecessity := rfl

/-- The epistemic force of `may` is possibility (derived from Fragment). -/
theorem may_is_possibility : epistemicForce may = some .possibility := rfl

-- ============================================================================
-- §4. Within-Force Ordering
-- ============================================================================

/-! Thresholds decrease monotonically with force: must (□) > should (□w) >
    may (◇) > might = could (◇). The □ > □w gap is captured by the 3-way
    `ModalForce` distinction; the within-◇ gap remains a scalar difference. -/

/-- □ > □w: must (strong necessity) > should (weak necessity). -/
theorem must_gt_should : EpistemicEntry.must_.θ > EpistemicEntry.should_.θ := by
  show (4 : ℚ)/5 < 19/20; norm_num

/-- Among possibility modals: may > might. Both are ◇ but `may` is stronger. -/
theorem may_gt_might : EpistemicEntry.may_.θ > EpistemicEntry.might_.θ := by
  show (1 : ℚ)/5 < 3/10; norm_num

/-- `might` = `could` in threshold (both 0.20). -/
theorem might_eq_could : EpistemicEntry.might_.θ = EpistemicEntry.could_.θ := rfl

end Phenomena.Modality.EpistemicThresholdBridge
