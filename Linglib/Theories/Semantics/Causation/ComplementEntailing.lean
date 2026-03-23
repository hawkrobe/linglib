import Linglib.Core.StructuralEquationModel
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Implicative
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Theories.Semantics.Tense.Aspect.Core

/-!
# Causal Frame: Unified Abstraction for Complement-Entailing Constructions
@cite{nadathur-2023} @cite{nadathur-lauer-2020}

The single parameterized type underlying implicative verbs (*manage*, *fail*),
ability modals (*be able*, *sak*), light verbs (*le*), and degree constructions
(*enough/too*).

## The Unifying Abstraction

All complement-entailing constructions share the same causal skeleton:
1. A **causal dynamics** (structural equations)
2. A **trigger variable** (action, degree threshold, managing event)
3. A **complement variable** (the VP outcome)
4. A **background function** mapping evaluation contexts to causal situations
5. An **actualization mode** controlling what asserts trigger occurrence

The actuality inference in all cases reduces to the same syllogism:
- The trigger is **causally sufficient** for the complement (causal premise)
- The trigger **actually occurred** (assertion premise — from aspect or lexicon)
- Therefore the complement occurred (actuality conclusion)

## Actualization Mode

The key parameter distinguishing implicatives from ability modals
(@cite{nadathur-2023}, Chapter 1):

| Instance | Trigger | Actualization |
|----------|---------|---------------|
| *manage* | managing event | `.lexical` (aspect-independent) |
| *le* (Hindi LV) | volitional choice | `.lexical` (aspect-independent) |
| *be able* / *sak* | agent's action | `.aspectual` (PFV/IMPF) |
| *enough to VP* | degree ≥ θ | `.aspectual` (PFV/IMPF) |

-/

namespace CausalVerb

open Core.StructuralEquationModel
open Semantics.Tense.Aspect.Core (ViewpointAspectB)

-- ════════════════════════════════════════════════════
-- § 1. ActualizationMode
-- ════════════════════════════════════════════════════

/-- How the actuality of the trigger gets asserted.

    - **lexical**: The verb's lexical semantics asserts that the trigger occurred.
      The complement entailment holds regardless of grammatical aspect.
      (*manage*, *fail*, *force*, *prevent*, *le*)

    - **aspectual**: Grammatical aspect determines whether the trigger's
      occurrence is asserted. Perfective asserts it; imperfective doesn't.
      (*be able*, *sak*, *enough to VP*, *too Adj to VP*) -/
inductive ActualizationMode where
  | lexical    -- trigger asserted by lexical semantics (aspect-independent)
  | aspectual  -- trigger asserted by perfective aspect only
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. CausalFrame
-- ════════════════════════════════════════════════════

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

    All complement-entailing constructions are instances differing only in
    the choice of `W`, `actualization`, and what the "trigger" represents. -/
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

    This is the single function from which the semantics of *manage*,
    ability modals, and degree constructions are all derived. -/
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

    This is the abstract version of the entailment pattern for *manage*. -/
theorem CausalFrame.lexical_entails_complement (f : CausalFrame W) (w : W)
    (asp : ViewpointAspectB)
    (h : f.actualityWithAspect asp w = true) (hMode : f.actualization = .lexical) :
    f.actualizedAt w = true := by
  simp only [actualityWithAspect, hMode, Bool.and_eq_true] at h
  exact h.2

/-- **Generic actuality theorem (aspectual + perfective)**: if an
    aspect-governed frame holds with perfective aspect, the complement
    is actualized.

    This is the abstract version of actuality entailments for ability
    modals and degree constructions. -/
theorem CausalFrame.perfective_entails_complement (f : CausalFrame W) (w : W)
    (h : f.actualityWithAspect .perfective w = true)
    (hMode : f.actualization = .aspectual) :
    f.actualizedAt w = true := by
  simp only [actualityWithAspect, hMode, Bool.and_eq_true] at h
  exact h.2

/-- **Generic non-entailment (aspectual + imperfective)**: imperfective
    aspect is compatible with complement not being actualized.

    This is the abstract version of the observation that imperfective
    ability modals don't entail their complements. -/
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
    a frame over `Bool` where `true` = action performed, `false` = not. -/
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

    This captures *manage* being aspect-independent: the entailment
    doesn't change with aspect because the lexical semantics already
    asserts trigger occurrence. -/
theorem CausalFrame.lexical_aspect_independent (f : CausalFrame W) (w : W)
    (hMode : f.actualization = .lexical) :
    f.actualityWithAspect .perfective w = f.actualityWithAspect .imperfective w := by
  simp only [CausalFrame.actualityWithAspect, hMode]

/-- **Imperfective is pure sufficiency** for aspectually-governed frames:
    imperfective asserts only causal sufficiency, with no event actualization. -/
theorem CausalFrame.imperfective_is_pure_sufficiency (f : CausalFrame W) (w : W)
    (hMode : f.actualization = .aspectual) :
    f.actualityWithAspect .imperfective w = f.sufficientAt w := by
  simp only [CausalFrame.actualityWithAspect, hMode]

/-- **Perfective adds actualization**: perfective = imperfective ∧ actualized
    for aspectually-governed frames. -/
theorem CausalFrame.perfective_adds_actualization (f : CausalFrame W) (w : W)
    (hMode : f.actualization = .aspectual) :
    f.actualityWithAspect .perfective w =
      (f.actualityWithAspect .imperfective w && f.actualizedAt w) := by
  simp only [CausalFrame.actualityWithAspect, hMode]

end ActualityTheorems

-- ════════════════════════════════════════════════════
-- § 5. Sufficiency Monotonicity via Closure
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

-- ════════════════════════════════════════════════════
-- § 6. Ability Frame Constructor
-- ════════════════════════════════════════════════════

open Semantics.Attitudes.Intensional (World) in
/-- Construct an ability-modal `CausalFrame`: a world-indexed causal model
    where actualization is governed by aspect (not lexical assertion).

    Each possible world `w : World` projects to a `Situation` in the causal
    model via `background`. Ability at `w` reduces to causal sufficiency in
    the projected situation.

    - **Imperfective**: sufficiency only (pure ability, compatible with
      complement unrealized)
    - **Perfective**: sufficiency AND actualization (actuality entailment)

    This replaces the former `AbilityScenario` structure — ability modals
    are just `CausalFrame World` with `actualization = .aspectual`. -/
def abilityFrame (dynamics : CausalDynamics) (action complement : Variable)
    (background : World → Situation) : CausalFrame World :=
  { dynamics
    trigger := action
    complement
    background
    actualization := .aspectual }

open Semantics.Attitudes.Intensional (World) in
/-- `abilityFrame` always produces aspectual actualization. -/
theorem abilityFrame_aspectual (dyn : CausalDynamics) (act comp : Variable)
    (bg : World → Situation) :
    (abilityFrame dyn act comp bg).actualization = .aspectual := rfl

-- ════════════════════════════════════════════════════
-- § 7. Ability-Specific Existence Theorems
-- ════════════════════════════════════════════════════

open Semantics.Attitudes.Intensional (World) in
/-- Ability differs from implicative verbs: ability can hold without
    actualization (impossible for *manage*).

    For *manage* (`.lexical` mode), `actualityWithAspect` ALWAYS includes
    complement truth. For ability (`.aspectual` mode), only perfective
    aspect forces complement truth. -/
theorem CausalFrame.ability_differs_from_implicative :
    ∃ (f : CausalFrame World) (w : World),
      f.actualization = .aspectual ∧
      f.sufficientAt w = true ∧ f.actualizedAt w = false := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let f := abilityFrame dyn act comp (λ _ => Situation.empty)
  exact ⟨f, .w0, rfl, by native_decide, by native_decide⟩

open Semantics.Attitudes.Intensional (World) in
/-- **Aspect governs actuality for ability**: the same ability frame
    yields different entailment patterns under different aspects.

    With perfective: ability → complement actualized.
    With imperfective: ability ↛ complement actualized. -/
theorem CausalFrame.aspect_governs_ability :
    ∃ (f : CausalFrame World) (w : World),
      f.actualization = .aspectual ∧
      f.actualityWithAspect .perfective w = true ∧
      f.actualizedAt w = true ∧
      ∃ w', f.actualityWithAspect .imperfective w' = true ∧
            f.actualizedAt w' = false := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let bg : World → Situation := λ w =>
    match w with
    | .w0 => Situation.empty.extend act true
    | _ => Situation.empty
  let f := abilityFrame dyn act comp bg
  exact ⟨f, .w0, rfl, by native_decide, by native_decide,
         .w1, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 8. Closure-Operator Properties of normalDevelopment
-- ════════════════════════════════════════════════════

/-! For positive dynamics, `normalDevelopment` is a **closure operator** on
    `(Situation, trueLE)`:
    1. Inflationary: `s ⊑ cl(s)`
    2. Monotone: `s₁ ⊑ s₂ → cl(s₁) ⊑ cl(s₂)`
    3. Idempotent: `cl(cl(s)) = cl(s)`

    Causal sufficiency is **closure membership**: `complement = true ∈ cl(s + trigger)`.
    This is the deep structural reason all complement-entailing constructions work. -/

/-- Monotone: if `s₁ ⊑ s₂`, then `cl(s₁) ⊑ cl(s₂)`. -/
theorem closure_monotone (dyn : CausalDynamics) (s₁ s₂ : Situation)
    (hPos : isPositiveDynamics dyn = true) (hLE : Situation.trueLE s₁ s₂)
    (fuel : Nat := 100) :
    Situation.trueLE (normalDevelopment dyn s₁ fuel) (normalDevelopment dyn s₂ fuel) :=
  normalDevelopment_trueLE_positive dyn s₁ s₂ fuel hPos hLE

/-- Inflationary: every truth in `s` is preserved by normal development. -/
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
    Sufficiency IS asking whether the complement is in the closure
    of the extended situation. -/
theorem sufficiency_is_closure_membership (dyn : CausalDynamics) (s : Situation)
    (trigger complement : Variable) :
    causallySufficient dyn s trigger complement =
      (normalDevelopment dyn (s.extend trigger true)).hasValue complement true := rfl

-- ════════════════════════════════════════════════════
-- § 9. Instance Bridge: Implicatives → CausalFrame
-- ════════════════════════════════════════════════════

open Nadathur2024.Implicative in
/-- An `ImplicativeScenario` is a `CausalFrame Unit` with lexical actualization. -/
def CausalFrame.ofImplicative (sc : ImplicativeScenario) : CausalFrame Unit :=
  { dynamics := sc.dynamics
    trigger := sc.prerequisite
    complement := sc.complement
    background := λ _ => sc.background
    actualization := .lexical }

open Nadathur2024.Implicative in
/-- The generic frame's sufficiency at `()` matches `manageSem`'s
    sufficiency check. -/
theorem implicative_sufficiency_matches (sc : ImplicativeScenario) :
    (CausalFrame.ofImplicative sc).sufficientAt () =
      causallySufficient sc.dynamics sc.background sc.prerequisite sc.complement := rfl

end CausalVerb
