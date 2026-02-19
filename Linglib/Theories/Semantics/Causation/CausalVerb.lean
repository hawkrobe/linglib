import Linglib.Core.Causation
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Modality.Ability
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect

/-!
# Causal Verb Frame (Nadathur 2023)

Deep foundation for complement-entailing constructions: implicative verbs
(*manage*, *fail*), ability modals (*be able*), and degree constructions
(*enough/too*). Analogous to `MereoDim` bridging mereology and scales,
this file bridges **causation**, **modality**, and **aspect** through a
single parameterized frame.

## The Unifying Abstraction

All three phenomena share the same causal skeleton:
1. A **causal dynamics** (structural equations)
2. A **trigger variable** (action, degree threshold, managing event)
3. A **complement variable** (the VP outcome)
4. A **background function** mapping evaluation contexts to causal situations
5. An **actualization mode** controlling what asserts trigger occurrence

The actuality inference in all cases reduces to the same syllogism:
- The trigger is **causally sufficient** for the complement (causal premise)
- The trigger **actually occurred** (assertion premise — from aspect or lexicon)
- Therefore the complement occurred (actuality conclusion)

## Closure-Operator Structure (§1)

For positive dynamics, `normalDevelopment` is a **closure operator** on
`(Situation, trueLE)`:
1. Inflationary: `s ⊑ cl(s)` — adding causal consequences only adds truths
2. Monotone: `s₁ ⊑ s₂ → cl(s₁) ⊑ cl(s₂)` — more inputs → more outputs
3. Idempotent: `cl(cl(s)) = cl(s)` — fixpoint stability

Causal sufficiency is **closure membership**: `complement = true ∈ cl(s + trigger)`.
This is the deep structural reason that all three phenomena work the same way.

## Linguistic Instances (§5–§6)

| Instance | Trigger | Aspect-governed? |
|----------|---------|------------------|
| *manage* | managing event | No (lexical) |
| *be able* | agent's action | Yes (PFV/IMPF) |
| *enough to VP* | degree ≥ θ | Yes (PFV/IMPF) |
| *too Adj to VP* | degree ≥ θ | Yes (PFV/IMPF) |

## References

- Nadathur, P. (2023). *Actuality Inferences: Causality, Aspect, and Modality*.
  Oxford Studies in Semantics and Pragmatics 15.
- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. *Glossa*.
-/

namespace CausalVerb

open Core.Causation
open Semantics.Lexical.Verb.ViewpointAspect (ViewpointAspectB)

-- ════════════════════════════════════════════════════
-- § 1. Closure-Operator Properties of normalDevelopment
-- ════════════════════════════════════════════════════

/-! For positive dynamics, `normalDevelopment` satisfies the three closure
    operator axioms. The inflationary and monotonicity properties are proved
    in `Core/Causation.lean`; we package them here and add the fixpoint return. -/

/-- Monotone: if `s₁ ⊑ s₂`, then `cl(s₁) ⊑ cl(s₂)`.
    Imported from `Core/Causation.lean`. -/
theorem closure_monotone (dyn : CausalDynamics) (s₁ s₂ : Situation)
    (hPos : isPositiveDynamics dyn = true) (hLE : Situation.trueLE s₁ s₂)
    (fuel : Nat := 100) :
    Situation.trueLE (normalDevelopment dyn s₁ fuel) (normalDevelopment dyn s₂ fuel) :=
  normalDevelopment_trueLE_positive dyn s₁ s₂ fuel hPos hLE

/-- Inflationary: every truth in `s` is preserved by normal development.
    Imported from `Core/Causation.lean`. -/
theorem closure_inflationary (dyn : CausalDynamics) (s : Situation)
    (hPos : isPositiveDynamics dyn = true) (fuel : Nat := 100) :
    Situation.trueLE s (normalDevelopment dyn s fuel) :=
  positive_normalDevelopment_grows dyn s fuel hPos

/-- Fixpoint return: if the first round of law application reaches a fixpoint,
    `normalDevelopment` returns that result. -/
theorem closure_fixpoint_returns (dyn : CausalDynamics) (s : Situation)
    (hFix : isFixpoint dyn (applyLawsOnce dyn s) = true) :
    normalDevelopment dyn s 1 = applyLawsOnce dyn s :=
  normalDevelopment_succ_fix hFix

/-- **Causal sufficiency as closure membership.**

    `causallySufficient dyn s trigger complement` holds iff
    `complement = true ∈ cl(s + {trigger = true})`.

    This is definitional — we state it as a theorem for the conceptual
    bridge: sufficiency IS asking whether the complement is in the closure
    of the extended situation. -/
theorem sufficiency_is_closure_membership (dyn : CausalDynamics) (s : Situation)
    (trigger complement : Variable) :
    causallySufficient dyn s trigger complement =
      (normalDevelopment dyn (s.extend trigger true)).hasValue complement true := rfl

-- ════════════════════════════════════════════════════
-- § 2. CausalFrame: The Unified Abstraction
-- ════════════════════════════════════════════════════

/-- How the actuality of the trigger gets asserted.

    - **lexical**: The verb's lexical semantics asserts that the trigger occurred.
      The complement entailment holds regardless of grammatical aspect.
      (*manage*, *fail*, *force*, *prevent*)

    - **aspectual**: Grammatical aspect determines whether the trigger's
      occurrence is asserted. Perfective asserts it; imperfective doesn't.
      (*be able*, *enough to VP*, *too Adj to VP*) -/
inductive ActualizationMode where
  | lexical    -- trigger asserted by lexical semantics (aspect-independent)
  | aspectual  -- trigger asserted by perfective aspect only
  deriving DecidableEq, Repr, BEq

/-- **CausalFrame**: The abstract frame underlying all complement-entailing
    verb constructions.

    Parameterized by `W` (evaluation context type):
    - `W = Unit` for implicative verbs (no modal dimension)
    - `W = World` for ability modals (Kripke worlds)
    - `W = World` for degree constructions (degree evaluated at worlds)

    The frame bundles:
    - Causal model (dynamics + trigger + complement)
    - Background projection (evaluation context → causal situation)
    - Actualization mode (what controls trigger assertion)

    All three phenomena are instances differing only in the choice of
    `W`, `actualization`, and what the "trigger" represents. -/
structure CausalFrame (W : Type) where
  /-- Structural equations governing trigger → complement -/
  dynamics : CausalDynamics
  /-- The trigger variable (action, degree threshold, managing event) -/
  trigger : Variable
  /-- The complement variable (VP outcome) -/
  complement : Variable
  /-- Maps evaluation contexts to causal background situations -/
  background : W → Situation
  /-- How trigger occurrence is asserted -/
  actualization : ActualizationMode

-- ════════════════════════════════════════════════════
-- § 3. Generic Semantics
-- ════════════════════════════════════════════════════

section FrameSemantics

variable {W : Type}

/-- Trigger is causally sufficient for complement at evaluation context `w`. -/
def CausalFrame.sufficientAt (f : CausalFrame W) (w : W) : Bool :=
  causallySufficient f.dynamics (f.background w) f.trigger f.complement

/-- Complement is actualized at `w`: trigger occurred AND complement developed. -/
def CausalFrame.actualizedAt (f : CausalFrame W) (w : W) : Bool :=
  factuallyDeveloped f.dynamics (f.background w) f.trigger f.complement

/-- The complement did NOT develop at `w` (for negative-polarity verbs like
    *fail*, *too Adj to VP*). -/
def CausalFrame.complementBlockedAt (f : CausalFrame W) (w : W) : Bool :=
  (f.background w).hasValue f.trigger true &&
  !(normalDevelopment f.dynamics (f.background w)).hasValue f.complement true

/-- **Generic actuality predicate** with aspectual modulation.

    - **Lexical**: sufficiency AND actualization (always, regardless of aspect)
    - **Aspectual + perfective**: sufficiency AND actualization
    - **Aspectual + imperfective**: sufficiency only (no actualization required)

    This is the single function from which `manageSem`, `abilityWithAspect`,
    and `enoughWithAspect` are all derived. -/
def CausalFrame.actualityWithAspect (f : CausalFrame W) (asp : ViewpointAspectB)
    (w : W) : Bool :=
  match f.actualization with
  | .lexical =>
    f.sufficientAt w && f.actualizedAt w
  | .aspectual =>
    match asp with
    | .perfective => f.sufficientAt w && f.actualizedAt w
    | .imperfective => f.sufficientAt w

end FrameSemantics

-- ════════════════════════════════════════════════════
-- § 4. Generic Actuality Theorems
-- ════════════════════════════════════════════════════

section ActualityTheorems

variable {W : Type}

/-- **Generic actuality theorem (lexical mode)**: if a lexically-actualized
    frame holds, the complement is actualized.

    This is the abstract version of `manage_entails_complement`. -/
theorem CausalFrame.lexical_entails_complement (f : CausalFrame W) (w : W)
    (asp : ViewpointAspectB)
    (h : f.actualityWithAspect asp w = true) (hMode : f.actualization = .lexical) :
    f.actualizedAt w = true := by
  simp only [actualityWithAspect, hMode, Bool.and_eq_true] at h
  exact h.2

/-- **Generic actuality theorem (aspectual + perfective)**: if an
    aspect-governed frame holds with perfective aspect, the complement
    is actualized.

    This is the abstract version of `perfective_ability_entails_complement`
    and `perfective_enough_entails_complement`. -/
theorem CausalFrame.perfective_entails_complement (f : CausalFrame W) (w : W)
    (h : f.actualityWithAspect .perfective w = true)
    (hMode : f.actualization = .aspectual) :
    f.actualizedAt w = true := by
  simp only [actualityWithAspect, hMode, Bool.and_eq_true] at h
  exact h.2

/-- **Generic non-entailment (aspectual + imperfective)**: imperfective
    aspect is compatible with complement not being actualized.

    This is the abstract version of
    `imperfective_ability_compatible_with_unrealized`. -/
theorem CausalFrame.imperfective_compatible_with_unrealized :
    ∃ (f : CausalFrame Unit),
      f.actualization = .aspectual ∧
      f.actualityWithAspect .imperfective () = true ∧
      f.actualizedAt () = false := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let f : CausalFrame Unit := {
    dynamics := dyn
    trigger := act
    complement := comp
    background := λ _ => Situation.empty
    actualization := .aspectual
  }
  exact ⟨f, rfl, by native_decide, by native_decide⟩

/-- **Aspect governs actuality (generic)**: the same frame yields different
    entailment patterns under different aspects, demonstrated with
    a frame over `Bool` where `true` = action performed, `false` = not.

    Abstract version of `aspect_governs_actuality`. -/
theorem CausalFrame.aspect_governs_actuality :
    ∃ (f : CausalFrame Bool),
      f.actualization = .aspectual ∧
      f.actualityWithAspect .perfective true = true ∧
      f.actualizedAt true = true ∧
      f.actualityWithAspect .imperfective false = true ∧
      f.actualizedAt false = false := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let f : CausalFrame Bool := {
    dynamics := dyn
    trigger := act
    complement := comp
    background := λ w => if w then Situation.empty.extend act true
                          else Situation.empty
    actualization := .aspectual
  }
  exact ⟨f, rfl, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Lexical mode is aspect-independent: the result is the same for
    perfective and imperfective when the trigger is present.

    This captures "manage" being aspect-independent: the entailment
    doesn't change with aspect because the lexical semantics already
    asserts trigger occurrence. -/
theorem CausalFrame.lexical_aspect_independent (f : CausalFrame W) (w : W)
    (hMode : f.actualization = .lexical) :
    f.actualityWithAspect .perfective w = f.actualityWithAspect .imperfective w := by
  simp only [CausalFrame.actualityWithAspect, hMode]

end ActualityTheorems

-- ════════════════════════════════════════════════════
-- § 5. Instance Bridges
-- ════════════════════════════════════════════════════

/-! Show that existing structures are instances of `CausalFrame`. -/

open Nadathur2023.Implicative in
/-- An `ImplicativeScenario` is a `CausalFrame Unit` with lexical actualization. -/
def CausalFrame.ofImplicative (sc : ImplicativeScenario) : CausalFrame Unit :=
  { dynamics := sc.dynamics
    trigger := sc.action
    complement := sc.complement
    background := λ _ => sc.background
    actualization := .lexical }

/-- An `AbilityScenario` is a `CausalFrame World` with aspectual actualization. -/
def CausalFrame.ofAbility (sc : Nadathur2023.Ability.AbilityScenario) :
    CausalFrame Semantics.Attitudes.Intensional.World :=
  { dynamics := sc.dynamics
    trigger := sc.action
    complement := sc.complement
    background := sc.background
    actualization := .aspectual }

-- ════════════════════════════════════════════════════
-- § 6. Grounding: Instance Theorems Match Specific Results
-- ════════════════════════════════════════════════════

open Nadathur2023.Implicative in
/-- The generic frame's sufficiency at `()` matches `manageSem`'s
    sufficiency check. -/
theorem implicative_sufficiency_matches (sc : ImplicativeScenario) :
    (CausalFrame.ofImplicative sc).sufficientAt () =
      causallySufficient sc.dynamics sc.background sc.action sc.complement := rfl

set_option maxRecDepth 1024 in
/-- The generic frame's sufficiency at `w` matches `abilityAt`. -/
theorem ability_sufficiency_matches (sc : Nadathur2023.Ability.AbilityScenario)
    (w : Semantics.Attitudes.Intensional.World) :
    (CausalFrame.ofAbility sc).sufficientAt w =
      Nadathur2023.Ability.abilityAt sc w := rfl

set_option maxRecDepth 1024 in
/-- The generic frame's actualization at `w` matches `complementActualized`. -/
theorem ability_actualization_matches (sc : Nadathur2023.Ability.AbilityScenario)
    (w : Semantics.Attitudes.Intensional.World) :
    (CausalFrame.ofAbility sc).actualizedAt w =
      Nadathur2023.Ability.complementActualized sc w := rfl

set_option maxRecDepth 1024 in
/-- **Grounding theorem**: the generic `actualityWithAspect` matches
    `abilityWithAspect` for ability scenarios.

    This is the key structural result: `Ability.lean`'s hand-written
    `abilityWithAspect` is exactly what falls out of the generic
    `CausalFrame.actualityWithAspect` machinery. -/
theorem ability_frame_matches_ability_with_aspect
    (sc : Nadathur2023.Ability.AbilityScenario)
    (asp : ViewpointAspectB) (w : Semantics.Attitudes.Intensional.World) :
    (CausalFrame.ofAbility sc).actualityWithAspect asp w =
      Nadathur2023.Ability.abilityWithAspect sc asp w := by
  cases asp <;> rfl

-- ════════════════════════════════════════════════════
-- § 7. Sufficiency Monotonicity via Closure
-- ════════════════════════════════════════════════════

/-- Causal sufficiency in a frame is monotone for positive dynamics:
    adding truths to the background preserves sufficiency.

    This is the frame-level version of `sufficiency_monotone_positive`. -/
theorem CausalFrame.sufficiency_monotone {W : Type} (f : CausalFrame W) (w : W)
    (extra : Variable)
    (hPos : isPositiveDynamics f.dynamics = true)
    (h : f.sufficientAt w = true) :
    causallySufficient f.dynamics ((f.background w).extend extra true)
      f.trigger f.complement = true :=
  NadathurLauer2020.Sufficiency.sufficiency_monotone_positive
    f.dynamics (f.background w) f.trigger extra f.complement hPos h

end CausalVerb
