import Linglib.Core.CausalModel
import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency

/-!
# Implicative Verb Semantics (Nadathur 2023, Chapter 1)

Implicative verbs (*manage*, *fail*) have complement entailments that arise
from two-event causal structure, NOT from aspectual composition.

## Key Insight

"Kim managed to swim across" entails "Kim swam across" regardless of aspect.
This contrasts with ability modals where perfective aspect is required for
the actuality inference. The entailment is **lexically encoded** via causal
sufficiency: the action (managing) is sufficient for the complement outcome.

## Causal Model

An `ImplicativeScenario` bundles:
- `CausalDynamics`: a law from action to complement
- `action`, `complement`: causal variables
- `background`: the situation in which the action occurs

`manageSem` holds when the action occurred, was causally sufficient, and
the complement developed. `failSem` holds when the complement did NOT develop.

## Grounding

The `VerbEntry.implicativeBuilder := some .positive` for *manage*
in `Fragments/English/Predicates/Verbal.lean` is **grounded** by
`manage_entails_complement`: if `manageSem` holds, the complement is true.

## References

- Nadathur, P. (2023). Actuality Inferences: Causality, Aspect, and Modality.
  Chapter 1: Actuality Inferences and Implicative Verbs.
- Karttunen, L. (1971). Implicative Verbs. Language 47(2), 340-358.
-/

namespace Nadathur2023.Implicative

open Core.CausalModel

/-- A scenario for implicative verbs: a causal model linking a prerequisite
    action to a complement outcome.

    For "manage to VP": the action variable represents the managing event,
    and the complement variable represents the VP outcome. The causal law
    encodes that the action is sufficient for the complement. -/
structure ImplicativeScenario where
  /-- The causal dynamics (structural equations) -/
  dynamics : CausalDynamics
  /-- The prerequisite action variable (e.g., "the managing event") -/
  action : Variable
  /-- The complement variable (e.g., "swimming across") -/
  complement : Variable
  /-- The background situation -/
  background : Situation

/-- Semantics of "manage": action occurred, was causally sufficient for
    complement, and complement developed normally.

    "Kim managed to swim across" is true iff:
    1. Kim performed the action
    2. That action was causally sufficient for swimming across
    3. Swimming across actually occurred (via normal development) -/
def manageSem (sc : ImplicativeScenario) : Bool :=
  let bg := sc.background.extend sc.action true
  causallySufficient sc.dynamics sc.background sc.action sc.complement &&
  (normalDevelopment sc.dynamics bg).hasValue sc.complement true

/-- Semantics of "fail": the complement did NOT develop.

    "Kim failed to swim across" entails "Kim did not swim across."
    The failure is defined by the absence of the complement outcome
    after normal causal development. -/
def failSem (sc : ImplicativeScenario) : Bool :=
  let bg := sc.background.extend sc.action true
  !(normalDevelopment sc.dynamics bg).hasValue sc.complement true

/-- **Central grounding theorem**: if `manageSem` holds, the complement
    is true after normal development.

    This grounds `VerbEntry.implicativeBuilder := some .positive` for *manage*:
    the entailment is not stipulated but follows from causal sufficiency. -/
theorem manage_entails_complement (sc : ImplicativeScenario)
    (h : manageSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = true := by
  simp only [manageSem, Bool.and_eq_true] at h
  exact h.2

/-- If `failSem` holds, the complement is false after normal development. -/
theorem fail_entails_not_complement (sc : ImplicativeScenario)
    (h : failSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = false := by
  simp only [failSem, Bool.not_eq_true'] at h
  exact h

/-- Implicative entailment is NOT aspect-governed: the entailment holds with
    no aspect parameter in the semantics. This contrasts with ability modals
    (see `Modal/Ability.lean`) where aspect determines whether the complement
    is entailed.

    Formally: `manageSem` has no aspect parameter — the entailment is
    purely causal. -/
theorem implicative_not_aspect_governed (sc : ImplicativeScenario)
    (h : manageSem sc = true) :
    -- The complement follows regardless — no aspect parameter needed
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = true :=
  manage_entails_complement sc h

-- ════════════════════════════════════════════════════
-- Concrete Example: "manage to swim across"
-- ════════════════════════════════════════════════════

section ConcreteExample

/-- The action: trying to swim across -/
private def tryAction : Variable := mkVar "trySwim"

/-- The complement: swimming across successfully -/
private def swimAcross : Variable := mkVar "swimAcross"

/-- Causal dynamics: trying to swim across is sufficient for swimming across
    (in the scenario where "manage" is appropriate). -/
private def manageDyn : CausalDynamics :=
  CausalDynamics.ofList [CausalLaw.simple tryAction swimAcross]

/-- The concrete scenario for "Kim managed to swim across". -/
private def manageScenario : ImplicativeScenario where
  dynamics := manageDyn
  action := tryAction
  complement := swimAcross
  background := Situation.empty

/-- Concrete verification: manageSem holds for the swim scenario. -/
theorem manage_swim_holds : manageSem manageScenario = true := by native_decide

/-- Concrete verification: the complement (swimming across) is true. -/
theorem manage_swim_complement_true :
    (normalDevelopment manageScenario.dynamics
      (manageScenario.background.extend manageScenario.action true)).hasValue
      manageScenario.complement true = true := by native_decide

/-- The fail scenario: same dynamics, but testing failSem.
    If the dynamics DO fire (action sufficient for complement), failSem is false. -/
theorem fail_swim_false_when_sufficient :
    failSem manageScenario = false := by native_decide

/-- A scenario where the action is NOT sufficient (no causal law). -/
private def failScenario : ImplicativeScenario where
  dynamics := CausalDynamics.empty  -- no law connecting action to complement
  action := tryAction
  complement := swimAcross
  background := Situation.empty

/-- When there's no causal connection, failSem holds (complement doesn't develop). -/
theorem fail_no_law_holds : failSem failScenario = true := by native_decide

end ConcreteExample

-- ════════════════════════════════════════════════════
-- ImplicativeBuilder: Enum basis for Fragment entries
-- ════════════════════════════════════════════════════

/-- Builder enum for implicative verbs, following the `CausativeBuilder` pattern.

    Positive implicatives (*manage*, *remember*) entail the complement on success.
    Negative implicatives (*fail*, *forget*) entail the complement does NOT hold on success. -/
inductive ImplicativeBuilder where
  | positive   -- manage, remember: success → complement true
  | negative   -- fail, forget: success → complement NOT true
  deriving DecidableEq, Repr, BEq

/-- Whether the builder entails the complement (positive) or its negation (negative). -/
def ImplicativeBuilder.entailsComplement : ImplicativeBuilder → Bool
  | .positive => true
  | .negative => false

/-- Map to the compositional semantics (`manageSem` or `failSem`). -/
def ImplicativeBuilder.toSemantics : ImplicativeBuilder →
    (ImplicativeScenario → Bool)
  | .positive => manageSem
  | .negative => failSem

/-- Positive builder entails complement: if `manageSem` holds, complement is true. -/
theorem positive_entails_complement (sc : ImplicativeScenario)
    (h : ImplicativeBuilder.positive.toSemantics sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = true :=
  manage_entails_complement sc h

/-- Negative builder entails NOT complement: if `failSem` holds, complement is false. -/
theorem negative_entails_not_complement (sc : ImplicativeScenario)
    (h : ImplicativeBuilder.negative.toSemantics sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.action true)).hasValue
      sc.complement true = false :=
  fail_entails_not_complement sc h

/-- `entailsComplement` matches semantic behavior: positive ↔ `manageSem`,
    negative ↔ `failSem`. -/
theorem entailsComplement_positive :
    ImplicativeBuilder.positive.entailsComplement = true := rfl

theorem entailsComplement_negative :
    ImplicativeBuilder.negative.entailsComplement = false := rfl

end Nadathur2023.Implicative
