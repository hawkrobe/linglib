import Linglib.Core.Causation
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Modality.Kratzer
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

/-!
# Ability Modals and Actuality Inferences (Nadathur 2023, Chapter 1)

Bridges **causality**, **modality**, and **aspect** to derive actuality
inferences for ability modals cross-linguistically.

## Central Claim

Actuality inferences arise from a three-way interaction:
1. **Ability = causal sufficiency** in circumstantial modal base
2. **Perfective aspect** requires the complement to be actualized
3. **Imperfective aspect** is compatible with unrealized complements

## Key Result

`perfective_ability_entails_complement`: perfective + ability → complement true.

This explains why Greek *boro* (PFV) entails the complement but *boro* (IMPF)
does not, and similarly for Hindi *saknaa*, French *pouvoir*, etc.

## Cross-Module Connections

| From | To | Via |
|------|-----|-----|
| `Core.Causation` | `Modal.Kratzer` | `AbilityScenario.background` |
| `Causative.Sufficiency` | this file | `abilityAt = causallySufficient` |
| `Modal.Kratzer` | this file | `toCircumstantialBase` |
| `ViewpointAspect` | this file | `toKleinViewpoint` |

## References

- Nadathur, P. (2023). Actuality Inferences: Causality, Aspect, and Modality.
- Kratzer, A. (1981). The Notional Category of Modality.
- Hacquard, V. (2006). Aspects of Modality. MIT dissertation.
-/

namespace Nadathur2023.Ability

open Core.Causation
open IntensionalSemantics.Attitude.Intensional (World allWorlds)
open IntensionalSemantics.Modal.Kratzer (ModalBase ConvBackground)
open TruthConditional.Verb.ViewpointAspect (ViewpointType ViewpointAspectB)

-- ════════════════════════════════════════════════════
-- Ability Scenario
-- ════════════════════════════════════════════════════

/-- An ability scenario bundles a causal model with a world-to-situation mapping.

    The key bridge: each possible world `w : World` projects to a `Situation`
    in the causal model via `background`. Ability at `w` reduces to causal
    sufficiency in the projected situation.

    The background encodes the factual state of each world, including whether
    the action was actually performed. Ability is counterfactual (would the
    action suffice?), while actualization is factual (was the action performed
    and did the complement follow?). -/
structure AbilityScenario where
  /-- The causal dynamics governing action → complement -/
  dynamics : CausalDynamics
  /-- The action variable (agent's action) -/
  action : Variable
  /-- The complement variable (outcome) -/
  complement : Variable
  /-- Maps each possible world to its background causal situation.
      The background encodes whether the action was performed at that world. -/
  background : World → Situation

-- ════════════════════════════════════════════════════
-- Core Semantics
-- ════════════════════════════════════════════════════

/-- Ability at world `w`: the agent's action is causally sufficient for
    the complement in the background situation of `w`.

    This IS Kratzer's circumstantial possibility: the relevant "circumstances"
    are the causal background at `w`, and "ability" means the action
    guarantees the outcome given those circumstances.

    Note: this is a **counterfactual** check — it extends the background
    with action=true to test sufficiency, regardless of whether the action
    was actually performed. -/
def abilityAt (sc : AbilityScenario) (w : World) : Bool :=
  causallySufficient sc.dynamics (sc.background w) sc.action sc.complement

/-- The complement is actualized at `w`: the action WAS performed at `w`
    (it's in the background) AND the complement developed via normal
    causal propagation.

    This is the **factual** counterpart to `abilityAt`: not "would the
    action suffice?" but "was the action done and did the outcome follow?" -/
def complementActualized (sc : AbilityScenario) (w : World) : Bool :=
  factuallyDeveloped sc.dynamics (sc.background w) sc.action sc.complement

/-- `complementActualized` is an instance of the `factuallyDeveloped` primitive. -/
theorem complementActualized_eq_factuallyDeveloped (sc : AbilityScenario) (w : World) :
    complementActualized sc w =
      factuallyDeveloped sc.dynamics (sc.background w) sc.action sc.complement := rfl

/-- Ability with aspectual modulation.

    - **Perfective**: requires both ability AND actualization (the event
      is viewed as completed within the reference time)
    - **Imperfective**: requires only ability (the state of being able
      is viewed from within, without requiring completion) -/
def abilityWithAspect (sc : AbilityScenario) (asp : ViewpointAspectB)
    (w : World) : Bool :=
  match asp with
  | .perfective => abilityAt sc w && complementActualized sc w
  | .imperfective => abilityAt sc w

-- ════════════════════════════════════════════════════
-- Bridge to Kratzer Modal Semantics
-- ════════════════════════════════════════════════════

/-- Convert an `AbilityScenario` to a Kratzer circumstantial modal base.

    The modal base at each world returns propositions encoding the
    causal background. Specifically: the proposition "the action is
    causally sufficient for the complement" restricted to worlds
    sharing the same background. -/
def toCircumstantialBase (sc : AbilityScenario) : ModalBase :=
  λ _w => [λ w' => abilityAt sc w']

/-- Ability as Kratzer possibility: "can VP" is ◇(complement) where
    the modal base encodes circumstantial facts.

    This bridges the causal model to Kratzer's framework: ability
    IS circumstantial possibility, where the "circumstances" are
    the causal structure. -/
def abilityAsKratzerPossibility (sc : AbilityScenario) (w : World) : Bool :=
  IntensionalSemantics.Modal.Kratzer.simplePossibility
    (toCircumstantialBase sc)
    (λ w' => complementActualized sc w')
    w

-- ════════════════════════════════════════════════════
-- Key Theorems
-- ════════════════════════════════════════════════════

/-- **Central result**: perfective ability entails complement actualization.

    If `abilityWithAspect sc .perfective w = true`, then the complement
    is actualized at `w`. This is the formal account of actuality inferences
    for ability modals.

    Proof: immediate from the definition — perfective conjoins ability
    with actualization. -/
theorem perfective_ability_entails_complement (sc : AbilityScenario) (w : World)
    (h : abilityWithAspect sc .perfective w = true) :
    complementActualized sc w = true := by
  simp only [abilityWithAspect, Bool.and_eq_true] at h
  exact h.2

/-- Imperfective ability is compatible with an unrealized complement.

    Existential witness: a concrete scenario where the agent has the ability
    (action is sufficient) but the complement is not actualized (action not
    performed at that world). -/
theorem imperfective_ability_compatible_with_unrealized :
    ∃ (sc : AbilityScenario) (w : World),
      abilityWithAspect sc .imperfective w = true ∧
      complementActualized sc w = false := by
  -- Witness: action → complement law, but action not performed at w0
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let sc : AbilityScenario := {
    dynamics := dyn
    action := act
    complement := comp
    -- Background: action not performed at any world
    background := λ _ => Situation.empty
  }
  exact ⟨sc, .w0, by native_decide, by native_decide⟩

/-- Ability = causal sufficiency (definitional). -/
theorem ability_is_causal_sufficiency (sc : AbilityScenario) (w : World) :
    abilityAt sc w = causallySufficient sc.dynamics (sc.background w)
      sc.action sc.complement := rfl

/-- **Aspect governs actuality**: the same scenario yields different
    entailment patterns under different aspects.

    With perfective: ability → complement actualized.
    With imperfective: ability ↛ complement actualized.

    Demonstrated by a concrete scenario where:
    - At w0 (action performed): perfective ability holds, complement actualized
    - At w1 (action not performed): imperfective ability holds, complement NOT actualized -/
theorem aspect_governs_actuality :
    ∃ (sc : AbilityScenario) (w : World),
      abilityWithAspect sc .perfective w = true ∧
      abilityWithAspect sc .imperfective w = true ∧
      complementActualized sc w = true ∧
      ∃ w', abilityWithAspect sc .imperfective w' = true ∧
            complementActualized sc w' = false := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  -- w0: action performed (in background). w1: action NOT performed.
  let bg : World → Situation := λ w =>
    match w with
    | .w0 => Situation.empty.extend act true
    | _ => Situation.empty
  let sc : AbilityScenario := {
    dynamics := dyn
    action := act
    complement := comp
    background := bg
  }
  exact ⟨sc, .w0, by native_decide, by native_decide, by native_decide,
         .w1, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- Contrast with Implicatives
-- ════════════════════════════════════════════════════

/-- Ability differs from implicative verbs: ability can hold without
    actualization (impossible for *manage*).

    For *manage*, `manageSem` ALWAYS includes complement truth.
    For ability, only perfective aspect forces complement truth.
    Here we show ability holds at a world where the complement is NOT actualized. -/
theorem ability_differs_from_implicative :
    ∃ (sc : AbilityScenario) (w : World),
      abilityAt sc w = true ∧ complementActualized sc w = false := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let sc : AbilityScenario := {
    dynamics := dyn
    action := act
    complement := comp
    background := λ _ => Situation.empty  -- action not performed
  }
  exact ⟨sc, .w0, by native_decide, by native_decide⟩

end Nadathur2023.Ability
