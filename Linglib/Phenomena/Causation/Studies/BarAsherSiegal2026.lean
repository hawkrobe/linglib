import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# @cite{bar-asher-siegal-2026}: Causation and Causal Relations
@cite{bar-asher-siegal-2026} @cite{baglini-bar-asher-siegal-2025} @cite{baglini-bar-asher-siegal-2020}

Formalization of the door-opening scenario from @cite{bar-asher-siegal-2026}
Figure 1: a structural equation model with two alternative sufficient sets
for a single effect (the door opening).

## The Door-Opening Model

Variables:
- A: handle is turned
- B: lock is disengaged (modeled as lock=false)
- C: circuit is closed
- D: electricity is running
- E: button is pressed
- F: door opens (the effect)

Two sufficient sets:
- **Manual opening** (I): Handle=1 ∧ Lock=0 ⊨ Door opens
- **Automatic opening** (H): Circuit=1 ∧ Electricity=1 ∧ Lock=0 ⊨ Door opens

## Key Results

The model demonstrates CC-selection at work:

1. **Completion mode** (CoS verbs like *open*): the handle satisfies
   completion CC-selection in the manual-only scenario — it completes
   the manual sufficient set. "John opened the door" is felicitous.

2. **Member mode** (verb *cause*): the handle does NOT satisfy member
   CC-selection even in the manual-only scenario, because Def 10b
   considers supersituations that activate the automatic pathway.
   "John caused the door to open" is infelicitous when alternative
   pathways exist in the causal model.

3. **Single-pathway model**: when the automatic pathway is absent from
   the model entirely, BOTH modes are satisfied. This captures the
   intuition that "John caused the door to open" is felicitous when
   there's genuinely no alternative explanation.
-/

namespace BarAsherSiegal2026

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity
open Semantics.Causation.CCSelection

/-! ## Variables -/

def handle : Variable := mkVar "handle"
/-- Lock state. Both pathways require `(lock, false)` — the lock must NOT
    be engaged. After the @cite{schulz-2011}/@cite{fitting-1985}
    info-monotone substrate landed, this negative-precondition encoding
    is first-class — no positive `lockDisengaged` workaround needed. -/
def lock : Variable := mkVar "lock"
def circuit : Variable := mkVar "circuit"
def electricity : Variable := mkVar "electricity"
def button : Variable := mkVar "button"
def doorOpens : Variable := mkVar "door_opens"

/-! ## Causal Laws -/

/-- Manual pathway: handle turned ∧ ¬lock → door opens. -/
def manualLaw : CausalLaw :=
  { preconditions := [(handle, true), (lock, false)], effect := doorOpens }

/-- Automatic pathway: circuit ∧ electricity ∧ ¬lock → door opens. -/
def automaticLaw : CausalLaw :=
  { preconditions := [(circuit, true), (electricity, true), (lock, false)],
    effect := doorOpens }

/-- Button press closes the circuit. -/
def buttonLaw : CausalLaw := CausalLaw.simple button circuit

/-! ## Two Models

We formalize two variants: the full model (both pathways) and a
single-pathway model (manual only). The contrast between them
demonstrates how model structure affects CC-selection. -/

/-- Full door dynamics: both manual and automatic pathways. -/
def doorDynamics : CausalDynamics :=
  ⟨[manualLaw, automaticLaw, buttonLaw]⟩

/-- Single-pathway model: manual only (no automatic system). -/
def manualOnlyDynamics : CausalDynamics :=
  ⟨[manualLaw]⟩

/-- Background: lock is not engaged (enabling condition for both pathways). -/
def unlocked : Situation := Situation.empty.extend lock false

/-! ## § 1. Sufficiency Results -/

/-- Handle is sufficient for door opening when lock is disengaged. -/
theorem handle_sufficient :
    causallySufficient doorDynamics unlocked handle doorOpens := by
  unfold causallySufficient
  rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]
  decide

/-- Button is sufficient for door opening when electricity is on
    and lock is disengaged. -/
theorem button_sufficient :
    causallySufficient doorDynamics
      (Situation.empty.extend electricity true |>.extend lock false)
      button doorOpens := by
  unfold causallySufficient
  rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 2 (by decide)]
  decide

/-- Handle alone is NOT sufficient — lock must be disengaged. -/
theorem handle_not_sufficient_locked :
    ¬ (causallySufficient doorDynamics Situation.empty handle doorOpens) := by
  unfold causallySufficient
  rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]
  decide

/-! ## § 2. CC-Selection: Full Model (Both Pathways)

The critical demonstration: with two alternative sufficient sets in the
causal model, completion and member CC-selection modes diverge. -/

/-- **Completion mode succeeds**: the handle completes the manual
    sufficient set. "John opened the door" is felicitous because the
    handle is the completing condition — adding it makes the effect
    inevitable, and removing it blocks the effect (simple but-for). -/
theorem handle_completion_full :
    ccConstraintSatisfied .completionOfSufficientSet
      doorDynamics unlocked handle doorOpens := by
  show completesForEffect _ _ _ _
  refine ⟨?_, ?_⟩
  · rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]; decide
  · intro h
    rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)] at h
    revert h; decide

/-- **Member mode fails**: "John caused the door to open" is infelicitous
    in the full model. Def 10b necessity considers supersituations that
    activate the automatic pathway — since the door COULD have opened
    without John (via button + electricity), John's action is not
    necessary in the Def 10b sense.

    This captures the key @cite{bar-asher-siegal-2026} insight: the
    verb *cause* requires that no alternative pathway exists, while
    CoS verbs like *open* only require completing ONE sufficient set. -/
theorem handle_member_fails_full :
    ¬ ccConstraintSatisfied .memberOfSufficientSet
      doorDynamics unlocked handle doorOpens := by
  -- causallyNecessary requires supersituation enumeration — keep native_decide
  -- (decidability through Nat.find-based normalDevelopment doesn't cleanly reduce)
  native_decide

/-- Actualization holds for handle in the full model. -/
theorem handle_actualized :
    actualizationHolds doorDynamics unlocked handle doorOpens := by
  show completesForEffect _ _ _ _
  refine ⟨?_, ?_⟩
  · rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]; decide
  · intro h
    rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)] at h
    revert h; decide

/-- When both pathways are active, NEITHER satisfies completion mode:
    removing either cause still leaves the effect via the other pathway. -/
theorem neither_completes_both_active :
    let bg := Situation.empty.extend handle true |>.extend button true
                |>.extend electricity true |>.extend lock false
    ¬ (ccConstraintSatisfied .completionOfSufficientSet doorDynamics bg handle doorOpens) ∧
    ¬ (ccConstraintSatisfied .completionOfSufficientSet doorDynamics bg button doorOpens) := by
  refine ⟨?_, ?_⟩
  all_goals
    intro ⟨_hSuf, hNotBut⟩
    apply hNotBut
    rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 2 (by decide)]
    decide

/-! ## § 3. CC-Selection: Single-Pathway Model

When the automatic pathway is absent from the model entirely, both
CC-selection modes succeed. This captures the intuition that
"John caused the door to open" is felicitous when there genuinely
is no alternative explanation. -/

/-- In the single-pathway model, handle satisfies BOTH CC-selection modes. -/
theorem handle_both_modes_single :
    ccConstraintSatisfied .completionOfSufficientSet
      manualOnlyDynamics unlocked handle doorOpens ∧
    ccConstraintSatisfied .memberOfSufficientSet
      manualOnlyDynamics unlocked handle doorOpens := by
  -- Member mode (causallyNecessary) keeps native_decide; completion
  -- migrates via rewrite + decide
  refine ⟨?_, ?_⟩
  · show completesForEffect _ _ _ _
    refine ⟨?_, ?_⟩
    · rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]; decide
    · intro h
      rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)] at h
      revert h; decide
  · native_decide  -- causeSem includes causallyNecessary

/-- Single-pathway: handle is necessary (no alternative pathway exists). -/
theorem handle_necessary_single :
    causallyNecessary manualOnlyDynamics unlocked handle doorOpens := by
  native_decide  -- causallyNecessary needs supersituation enumeration

/-! ## § 4. Causal Profiles -/

/-- Full model: handle is sufficient and direct, but NOT necessary
    (alternative automatic pathway exists in the model). -/
theorem handle_profile_full :
    causallySufficient doorDynamics unlocked handle doorOpens ∧
    ¬ causallyNecessary doorDynamics unlocked handle doorOpens ∧
    hasDirectLaw doorDynamics handle doorOpens := by
  refine ⟨?_, ?_, ?_⟩
  · unfold causallySufficient
    rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]; decide
  · native_decide  -- ¬ causallyNecessary needs enumeration
  · decide

/-- Single-pathway model: handle is sufficient, necessary, AND direct. -/
theorem handle_profile_single :
    causallySufficient manualOnlyDynamics unlocked handle doorOpens ∧
    causallyNecessary manualOnlyDynamics unlocked handle doorOpens ∧
    hasDirectLaw manualOnlyDynamics handle doorOpens := by
  refine ⟨?_, ?_, ?_⟩
  · unfold causallySufficient
    rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]; decide
  · native_decide  -- causallyNecessary
  · decide

/-! ## § 5. The Divergence: *open* vs *cause*

The central prediction of @cite{bar-asher-siegal-2026}: CoS verbs
and the verb *cause* impose different CC-selection constraints,
yielding different felicity patterns from the same causal model. -/

/-- *Open* (completion mode) is felicitous in the full model;
    *cause* (member mode) is not.

    "John opened the door" — true (handle completed the manual set)
    "John caused the door to open" — false (alternative pathway exists)

    This is the formalization of @cite{bar-asher-siegal-2026}'s
    central claim that causative constructions impose distinct
    model-theoretic constraints on cause selection. -/
theorem open_not_cause_full :
    ccConstraintSatisfied .completionOfSufficientSet
      doorDynamics unlocked handle doorOpens ∧
    ¬ ccConstraintSatisfied .memberOfSufficientSet
      doorDynamics unlocked handle doorOpens := by
  refine ⟨?_, ?_⟩
  · exact handle_completion_full
  · exact handle_member_fails_full

/-- In the single-pathway model, both are felicitous:
    "John opened the door" AND "John caused the door to open." -/
theorem open_and_cause_single :
    ccConstraintSatisfied .completionOfSufficientSet
      manualOnlyDynamics unlocked handle doorOpens ∧
    ccConstraintSatisfied .memberOfSufficientSet
      manualOnlyDynamics unlocked handle doorOpens :=
  handle_both_modes_single

/-! ## § 6. Structural Dependency -/

/-- Package the manual-only scenario as a `CausalDependency`. -/
def johnOpenedDoor : CausalDependency :=
  { cause := handle, effect := doorOpens,
    dynamics := manualOnlyDynamics, background := unlocked }

theorem johnOpenedDoor_completion :
    johnOpenedDoor.satisfies .completionOfSufficientSet := by
  show completesForEffect _ _ _ _
  refine ⟨?_, ?_⟩
  · rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]; decide
  · intro h
    rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)] at h
    revert h; decide

theorem johnOpenedDoor_actualized : johnOpenedDoor.actualized := by
  show completesForEffect _ _ _ _
  refine ⟨?_, ?_⟩
  · rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)]; decide
  · intro h
    rw [normalDevelopment_eq_iterate_of_fixpoint _ _ 1 (by decide)] at h
    revert h; decide

/-! ## § 7. Situation-based necessity (Nadathur 2024 Def 12b)

The CC-selection facts above use `causallyNecessary` (@cite{nadathur-2024}
Def 10b — necessity of **facts**). The Bar-Asher Siegal 2026 door
scenario is naturally a Def **12b** question — necessity of the whole
**situation** s = (handle=1, lock=0). Def 12b asks whether every
perturbation of this situation's ancestor-determinations fails to
achieve doorOpens=1. -/

/-- The "John turned the handle with the lock disengaged" situation. -/
def handleSituation : Situation :=
  Situation.empty.extend handle true |>.extend lock false

/-- Direct demonstration of Def 12b's verdict on the full model: a
    perturbation s' = (handle=0, lock=0, circuit=1, electricity=1)
    achieves doorOpens=1 via the automatic pathway, witnessing that
    `handleSituation` is NOT situationally necessary for
    ⟨doorOpens, true⟩ in `doorDynamics`.

    This formalizes the Bar-Asher Siegal claim about *cause* (member-mode
    selection) at the situation level: with the automatic pathway active
    in the model, no whole-situation cause attribution to handle-turning
    can be sustained. -/
theorem handleSituation_not_situationally_necessary_full :
    ¬ situationallyNecessary doorDynamics handleSituation doorOpens true := by
  -- Witness s' = (handle=0, lock=0, circuit=1, electricity=1) covers
  -- handleSituation's ancestor commitments (handle, lock) but disagrees
  -- on handle, doesn't fix doorOpens, and the automatic pathway fires.
  let s' : Situation :=
    Situation.empty.extend handle false |>.extend lock false
      |>.extend circuit true |>.extend electricity true
  intro h
  apply h s'
  · -- (i) handleSituation determines only {handle, lock}; both fixed in s'
    intro Y _ _; revert Y; decide
  · -- (ii) s' disagrees with handleSituation on `handle` (true vs false)
    refine ⟨handle, ?_, ?_, ?_⟩ <;> decide
  · -- (iii) s' doesn't fix doorOpens
    decide
  · -- Outcome: develop s' → doorOpens=true (automaticLaw fires in 1 round)
    rw [normalDevelopment_eq_iterate_of_fixpoint doorDynamics s' 1 (by decide)]
    decide

end BarAsherSiegal2026
