import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Structural Causation Tests
@cite{nadathur-lauer-2020} @cite{pearl-2000}

Verification that `Core.Causal` correctly models classic causal
structures from the philosophy and linguistics literature. Each section
sets up a concrete `CausalDynamics`, states the expected causal profile,
and proves the predictions match via `native_decide`.

## Scenarios

| Scenario | Structure | Key prediction |
|----------|-----------|----------------|
| Preemption | A→C, B→C, A fires first | A sufficient+necessary, B sufficient but not necessary |
| Prevention | A→C, B blocks A | B necessary for ¬C |
| Enabling | A background, B→(A∧B→C) | B sufficient given A, not without A |
| Double prevention | A prevents B, B prevents C | A enables C indirectly |
| Symmetric overdetermination | A→C, B→C, both present | Neither necessary |

-/

namespace Phenomena.Causation.StructuralCausation

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity

/-! ## 1. Early preemption

Billy and Suzy both throw rocks at a bottle. Suzy's rock arrives first
and shatters the bottle. Billy's rock would have shattered it otherwise.

Model: two independent laws, both causes present. This is structurally
identical to overdetermination in the Causation API (both sufficient,
neither necessary). The API does not distinguish temporal preemption
from symmetric overdetermination — both reduce to disjunctive causation. -/

section Preemption

def suzyThrows : Variable := mkVar "suzy_throws"
def billyThrows : Variable := mkVar "billy_throws"
def bottleShatters : Variable := mkVar "bottle_shatters"

def preemptionDyn : CausalDynamics :=
  CausalDynamics.disjunctiveCausation suzyThrows billyThrows bottleShatters

def preemptionBg : Situation :=
  Situation.empty.extend suzyThrows true |>.extend billyThrows true

/-- Suzy's throw is sufficient for shattering. -/
theorem suzy_sufficient :
    causallySufficient preemptionDyn Situation.empty suzyThrows bottleShatters := by
  native_decide

/-- Billy's throw is also sufficient (backup cause). -/
theorem billy_sufficient :
    causallySufficient preemptionDyn Situation.empty billyThrows bottleShatters := by
  native_decide

/-- Neither is necessary when both are present (overdetermination). -/
theorem suzy_not_necessary :
    ¬ (causallyNecessary preemptionDyn preemptionBg suzyThrows bottleShatters) := by
  native_decide

theorem billy_not_necessary :
    ¬ (causallyNecessary preemptionDyn preemptionBg billyThrows bottleShatters) := by
  native_decide

/-- "Suzy made the bottle shatter" is true; "Suzy caused the bottle to
    shatter" is false — matching Nadathur & Lauer's prediction for
    overdetermination. -/
theorem preemption_make_not_cause :
    makeSem preemptionDyn preemptionBg suzyThrows bottleShatters ∧
    ¬ (causeSem preemptionDyn preemptionBg suzyThrows bottleShatters) := by
  constructor <;> native_decide

/-- When Suzy is the sole thrower, she both "made" and "caused" the
    shattering. Under @cite{nadathur-2024} Def 10b, the background
    encodes Billy's absence rather than Suzy's presence. -/
theorem suzy_solo_make_and_cause :
    let bg := Situation.empty.extend billyThrows false
    makeSem preemptionDyn bg suzyThrows bottleShatters ∧
    causeSem preemptionDyn bg suzyThrows bottleShatters := by
  constructor <;> native_decide

end Preemption

/-! ## 2. Prevention

A surgeon operates (S), which prevents the patient from dying (D).
Without surgery the disease (B) would kill the patient.

Model: B → D (disease causes death), S ∧ B → ¬D is modeled by making
surgery block the disease law. We model this as: B → D is the only law,
and surgery removes B from the situation (counterfactual intervention). -/

section Prevention

def disease : Variable := mkVar "disease"
def surgery : Variable := mkVar "surgery"
def death : Variable := mkVar "death"

/-- Without surgery: disease → death. -/
def preventionDyn : CausalDynamics :=
  ⟨[CausalLaw.conjunctive disease (mkVar "no_surgery") death]⟩

/-- Background: disease present, no surgery (no_surgery = true). -/
def preventionBg : Situation :=
  Situation.empty.extend disease true |>.extend (mkVar "no_surgery") true

/-- Disease is sufficient for death when surgery is absent. -/
theorem disease_sufficient_no_surgery :
    causallySufficient preventionDyn
      (Situation.empty.extend (mkVar "no_surgery") true)
      disease death = true := by
  native_decide

/-- Disease is NOT sufficient for death in an empty background
    (needs the no_surgery enabling condition). -/
theorem disease_not_sufficient_alone :
    ¬ (causallySufficient preventionDyn Situation.empty disease death) := by
  native_decide

end Prevention

/-! ## 3. Enabling conditions

Oxygen is present (background). Striking a match (M) causes fire (F)
only when oxygen (O) is present: O ∧ M → F.

The match is an *agent cause*; oxygen is an *enabling condition*.
Nadathur & Lauer predict "make" is appropriate for the match
(sufficient given oxygen) while "cause" requires necessity. -/

section Enabling

def matchStrike : Variable := mkVar "match_strike"
def oxygenPresent : Variable := mkVar "oxygen_present"
def flame : Variable := mkVar "flame"

def enablingDyn : CausalDynamics :=
  ⟨[CausalLaw.conjunctive matchStrike oxygenPresent flame]⟩

def oxygenBg : Situation :=
  Situation.empty.extend oxygenPresent true

/-- Match is sufficient for fire given oxygen. -/
theorem match_sufficient_given_oxygen :
    causallySufficient enablingDyn oxygenBg matchStrike flame := by
  native_decide

/-- Match is NOT sufficient without oxygen. -/
theorem match_not_sufficient_without_oxygen :
    ¬ (causallySufficient enablingDyn Situation.empty matchStrike flame) := by
  native_decide

/-- Match is necessary for fire given oxygen. -/
theorem match_necessary :
    causallyNecessary enablingDyn oxygenBg matchStrike flame := by
  native_decide

/-- Oxygen is also necessary for fire given match. -/
theorem oxygen_necessary :
    let bg := Situation.empty.extend matchStrike true
    causallyNecessary enablingDyn bg oxygenPresent flame := by
  native_decide

/-- Both "make" and "cause" are true for the match (given oxygen). -/
theorem match_make_and_cause :
    makeSem enablingDyn oxygenBg matchStrike flame ∧
    causeSem enablingDyn oxygenBg matchStrike flame := by
  constructor <;> native_decide

end Enabling

/-! ## 4. Causal chain with bypass

A → B → C, but also A → C directly. B is an intermediate that is
not necessary because A has a direct path to C.

Model: two laws: A → B, A → C. -/

section ChainBypass

def a : Variable := mkVar "a"
def b : Variable := mkVar "b"
def c : Variable := mkVar "c"

def bypassDyn : CausalDynamics :=
  ⟨[CausalLaw.simple a b, CausalLaw.simple a c]⟩

/-- A is sufficient for C (direct law). -/
theorem a_sufficient_for_c :
    causallySufficient bypassDyn Situation.empty a c := by
  native_decide

/-- A is necessary for C (only cause). -/
theorem a_necessary_for_c :
    causallyNecessary bypassDyn Situation.empty a c := by
  native_decide

/-- B is NOT sufficient for C (no law B → C). -/
theorem b_not_sufficient_for_c :
    ¬ (causallySufficient bypassDyn Situation.empty b c) := by
  native_decide

end ChainBypass

/-! ## 5. Causal profiles summary

Verify sufficiency, necessity, and directness for each scenario. -/

section Profiles

/-- Preemption (both present): sufficient, not necessary, direct. -/
theorem preemption_profile :
    causallySufficient preemptionDyn preemptionBg suzyThrows bottleShatters ∧
    ¬ causallyNecessary preemptionDyn preemptionBg suzyThrows bottleShatters ∧
    hasDirectLaw preemptionDyn suzyThrows bottleShatters := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Enabling: match is sufficient, necessary, direct (given oxygen).
    Under @cite{nadathur-2024} Def 10b, bg excludes the cause. -/
theorem enabling_profile :
    causallySufficient enablingDyn oxygenBg matchStrike flame ∧
    causallyNecessary enablingDyn oxygenBg matchStrike flame ∧
    hasDirectLaw enablingDyn matchStrike flame := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Chain bypass: A is sufficient, necessary, direct for C. -/
theorem bypass_profile_a :
    causallySufficient bypassDyn Situation.empty a c ∧
    causallyNecessary bypassDyn Situation.empty a c ∧
    hasDirectLaw bypassDyn a c := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Chain bypass: B has no causal power over C.
    B is not sufficient (no B→C law), but IS necessary under Def 10b:
    the only way to achieve C is through A→C, which also fires A→B,
    so every path to C entails B. -/
theorem bypass_profile_b :
    ¬ causallySufficient bypassDyn Situation.empty b c ∧
    causallyNecessary bypassDyn Situation.empty b c ∧
    ¬ hasDirectLaw bypassDyn b c := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end Profiles

/-! ## 6. Intervention (Pearl's do-operator)

Verify that `intervene` correctly cuts incoming laws and that
`manipulates` detects interventionist causation. -/

section Intervention

/-- Intervening on the effect of a simple law cuts the law.
    do(bottleShatters = false) in preemption removes both laws
    targeting bottleShatters. -/
theorem intervene_cuts_laws :
    let (dyn', _) := intervene preemptionDyn Situation.empty bottleShatters false
    dyn'.laws.length = 0 := by native_decide

/-- After do(bottleShatters = false), the bottle doesn't shatter even
    with Suzy throwing — the intervention overrides the dynamics. -/
theorem intervene_overrides :
    let (dyn', s') := intervene preemptionDyn
      (Situation.empty.extend suzyThrows true) bottleShatters false
    (normalDevelopment dyn' s').hasValue bottleShatters false = true := by
  native_decide

/-- Suzy's throw manipulates the bottle: do(throw=T) vs do(throw=F)
    yield different outcomes. -/
theorem suzy_manipulates_bottle :
    manipulates preemptionDyn Situation.empty suzyThrows bottleShatters := by
  native_decide

/-- In enabling, the match manipulates the flame (given oxygen). -/
theorem match_manipulates_flame :
    manipulates enablingDyn oxygenBg matchStrike flame := by
  native_decide

/-- In chain bypass, B does NOT manipulate C (no B → C law). -/
theorem b_does_not_manipulate_c :
    ¬ (manipulates bypassDyn Situation.empty b c) := by
  native_decide

/-- A manipulates C in the bypass model (direct law A → C). -/
theorem a_manipulates_c :
    manipulates bypassDyn Situation.empty a c := by
  native_decide

end Intervention

/-! ## 7. Actual causation

Retrospective causal judgments: "did X actually cause Y in this situation?"
`actuallyCaused` tests whether the cause occurred AND was causally necessary
(under @cite{nadathur-2024} Def 10b). -/

section ActualCausation

/-- In preemption (both throwers), Suzy did NOT actually cause the
    shattering — Billy's backup blocks necessity. -/
theorem preemption_suzy_not_actual_cause :
    ¬ (actuallyCaused preemptionDyn preemptionBg suzyThrows bottleShatters) := by
  native_decide

/-- When Suzy is the sole thrower, she actually caused the shattering. -/
theorem solo_suzy_actual_cause :
    let bg := Situation.empty.extend suzyThrows true |>.extend billyThrows false
    actuallyCaused preemptionDyn bg suzyThrows bottleShatters := by
  native_decide

/-- In the enabling scenario, the match actually caused the flame
    (given oxygen as background). -/
theorem match_actually_caused_flame :
    let bg := oxygenBg.extend matchStrike true
    actuallyCaused enablingDyn bg matchStrike flame := by
  native_decide

end ActualCausation

/-! ## 8. Make and cause are truth-conditionally distinct

The main linguistic claim of @cite{nadathur-lauer-2020}: "make" and "cause"
are not synonyms — there exist scenarios where one is true and the other false.

Witnessed by disjunctive overdetermination: lightning OR arsonist → fire.
With both present, lightning is sufficient (makeSem) but not necessary
(¬ (causeSem)) because the arsonist backup blocks but-for. -/

theorem make_cause_truth_conditionally_distinct :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      makeSem dyn s c e ≠ causeSem dyn s c e := by
  exact ⟨.disjunctiveCausation (mkVar "l") (mkVar "a") (mkVar "f"),
         Situation.empty.extend (mkVar "l") true |>.extend (mkVar "a") true,
         mkVar "l", mkVar "f", by decide⟩

end Phenomena.Causation.StructuralCausation
