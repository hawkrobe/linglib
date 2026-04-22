import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity

/-!
# Causative Construction Selection (CC-Selection)
@cite{baglini-bar-asher-siegal-2020} @cite{baglini-bar-asher-siegal-2025} @cite{bar-asher-siegal-2026}

CC-selection (@cite{baglini-bar-asher-siegal-2025}) is the mechanism by which
causative constructions constrain which element of a causal model can be
linguistically realized as "the cause." Different constructions impose
different constraints, yielding distinct truth conditions from the same
underlying causal structure.

## CC-selection as the organizing hub

The sufficiency/necessity distinction appears across multiple types in this
library. CC-selection unifies them:

| Type | Location | Relationship to CC-selection |
|------|----------|------------------------------|
| `CCSelectionMode` | (this file) | **Primary**: how the construction selects |
| `Causative` | Builder.lean | Derived via `.selectionMode` |
| `CausationType` | ProductionDependence.lean | Derived via `.selectionMode` |

## Two core conditions (@cite{baglini-bar-asher-siegal-2025})

All causative constructions require:

1. **Epistemic inevitability**: the cause belongs to a sufficient set that
   renders the outcome inevitable from the speaker's perspective
2. **Actualization**: the cause is part of the only completed sufficient set
   realized in the actual world

## Entailment structure

`causeSem` (member mode) uses @cite{nadathur-2024} Def 10b necessity
(supersituation test). `completesForEffect` (completion mode) uses simple
but-for. Since Def 10b is strictly stronger than simple but-for:

    causeSem → completesForEffect → makeSem

So: "cause" entails "completion" entails "make." The reverse fails:
- `makeSem` without `completesForEffect`: overdetermination (backup cause
  blocks but-for)
- `completesForEffect` without `causeSem`: causal chains (Def 10b allows
  intermediate bypass via supersituation, but simple but-for holds since
  removing the root cause blocks the effect through the chain)
-/

namespace Semantics.Causation.CCSelection

open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity

-- ════════════════════════════════════════════════════
-- § 1. CC-Selection Mode
-- ════════════════════════════════════════════════════

/-- How a causative construction selects its cause from a causal model.

    @cite{baglini-bar-asher-siegal-2025}: different constructions impose
    different constraints on which condition can fill the cause role.

    - `memberOfSufficientSet`: any necessary condition within a sufficient
      set. The verb *cause* uses this — it can select any contributing
      factor. Truth conditions: `causeSem` (Def 10b necessity).
    - `completionOfSufficientSet`: the condition that **completes** a
      sufficient set — the last condition whose realization makes the effect
      inevitable. Change-of-state verbs (*open*, *break*) and resultatives
      use this. Truth conditions: `completesForEffect` (sufficiency +
      simple but-for). -/
inductive CCSelectionMode where
  /-- Overt "cause": any necessary condition within a sufficient set. -/
  | memberOfSufficientSet
  /-- CoS verbs, resultatives: the completing condition of a sufficient set. -/
  | completionOfSufficientSet
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- § 2. Completion Event
-- ════════════════════════════════════════════════════

/-- Completion event: the cause both completes a sufficient set AND is
    necessary in the current background (simple but-for test).

    @cite{baglini-bar-asher-siegal-2025}: the completion event is the
    condition whose realization makes the effect inevitable, and without
    which the effect would not have occurred.

    Uses simple counterfactual but-for rather than @cite{nadathur-2024}
    Def 10b supersituation necessity — the right granularity for
    completion events where intermediate variables are passive. -/
def completesForEffect (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Bool :=
  (normalDevelopment dyn (background.extend cause true)).hasValue effect true &&
  !(normalDevelopment dyn (background.extend cause false)).hasValue effect true

-- ════════════════════════════════════════════════════
-- § 3. CC-Selection Semantics
-- ════════════════════════════════════════════════════

/-- Map a CC-selection mode to its truth-condition function.

    - `memberOfSufficientSet` → `causeSem` (Def 10b necessity)
    - `completionOfSufficientSet` → `makeSem` (sufficiency)

    Note: `completionOfSufficientSet` maps to `makeSem` (not
    `completesForEffect`) because the but-for component is the
    CC-*selection* constraint — it determines WHICH element can be
    selected, not the truth conditions of the resulting statement.
    The truth conditions of "X opened the door" are sufficiency
    (`makeSem`); the selection constraint (`completesForEffect`)
    determines that X must be the completing condition. -/
def CCSelectionMode.toSemantics :
    CCSelectionMode → (CausalDynamics → Situation → Variable → Variable → Prop)
  | .memberOfSufficientSet => causeSem
  | .completionOfSufficientSet => makeSem

/-- Evaluate the CC-selection constraint for a given mode.

    This checks whether a condition is **selectable** as "the cause" by
    a construction using the given mode — not just whether the resulting
    statement would be true.

    - **Member**: `causeSem` — the condition occurred and was necessary
    - **Completion**: `completesForEffect` — the condition is sufficient
      AND removing it blocks the effect (simple but-for) -/
def ccConstraintSatisfied (mode : CCSelectionMode)
    (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Prop :=
  match mode with
  | .memberOfSufficientSet => causeSem dyn bg cause effect
  | .completionOfSufficientSet => completesForEffect dyn bg cause effect = true

instance (mode : CCSelectionMode) (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) :
    Decidable (ccConstraintSatisfied mode dyn bg cause effect) := by
  unfold ccConstraintSatisfied
  cases mode
  · exact inferInstanceAs (Decidable (causeSem _ _ _ _))
  · exact inferInstanceAs (Decidable (_ = true))

-- ════════════════════════════════════════════════════
-- § 4. Entailment Properties
-- ════════════════════════════════════════════════════

/-- Member selection entails completion selection **for positive dynamics**.

    `causeSem` (Def 10b necessity) → `completesForEffect` (simple but-for)
    when the dynamics have no inhibitory connections. Positive dynamics
    are monotone: setting a variable to `false` can only reduce firing,
    never enable new laws. So if normalDevelopment(bg) doesn't produce
    `e=true` (precondition of Def 10b), then normalDevelopment(bg + c=false)
    also doesn't produce `e=true`.

    The restriction to positive dynamics is necessary: with inhibitory
    laws, setting c=false can trigger new law chains that re-derive
    c=true, making simple but-for fail even when Def 10b holds
    (see `member_not_entails_completion_negative`).

    Linguistically: for standard causal models (no inhibition), if
    "X caused Y" is true, then X also completes a sufficient set for Y. -/
theorem member_entails_completion (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable)
    (hPos : isPositiveDynamics dyn = true)
    (h : ccConstraintSatisfied .memberOfSufficientSet dyn bg c e) :
    ccConstraintSatisfied .completionOfSufficientSet dyn bg c e := by
  -- h unfolds to causeSem dyn bg c e = ⟨hOccurred, hNec⟩
  obtain ⟨hOccurred, hNec⟩ := h
  -- Goal unfolds to completesForEffect dyn bg c e = true
  show completesForEffect dyn bg c e = true
  simp only [completesForEffect, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨hOccurred, ?_⟩
  -- Simple but-for: normalDev(bg + c=false) doesn't achieve e=true
  have hNoE : (normalDevelopment dyn bg).hasValue e true = false := by
    rcases Bool.eq_false_or_eq_true ((normalDevelopment dyn bg).hasValue e true)
      with h | h
    · -- h : ... = true → precondition fails → ¬ causallyNecessary
      have hNotNec : ¬ (causallyNecessary dyn bg c e) := by
        intro ⟨⟨_, hPreNotEffect⟩, _, _⟩
        rw [h] at hPreNotEffect
        exact absurd hPreNotEffect (by decide)
      exact absurd hNec hNotNec
    · exact h
  have hLE : Situation.trueLE (bg.extend c false) bg := by
    intro v hv
    by_cases hvc : v = c
    · subst hvc; simp at hv
    · rw [Situation.extend_hasValue_diff hvc] at hv; exact hv
  have hMono := normalDevelopment_trueLE_positive_default hPos hLE e
  cases heq : (normalDevelopment dyn (bg.extend c false)).hasValue e true with
  | false => rfl
  | true => exact absurd (hMono heq) (by rw [hNoE]; exact Bool.false_ne_true)

/-- Member does NOT entail completion for non-positive dynamics.

    Counterexample: inhibitory law (c=false → d=true) creates a
    re-derivation path. Setting c=false triggers d=true → c=true → e=true,
    so simple but-for fails. But Def 10b necessity holds because every
    path to e=true re-creates c=true, so no supersituation achieves
    e without c.

    This shows the positivity restriction on `member_entails_completion`
    is necessary, not just a proof convenience. -/
theorem member_not_entails_completion_negative :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      isPositiveDynamics dyn = false ∧
      ccConstraintSatisfied .memberOfSufficientSet dyn bg c e ∧
      ¬ (ccConstraintSatisfied .completionOfSufficientSet dyn bg c e) := by
  let c := mkVar "c"
  let d := mkVar "d"
  let e := mkVar "e"
  -- Inhibitory dynamics: ¬c → d, d → c, c → e
  let dyn : CausalDynamics :=
    ⟨[ { preconditions := [(c, false)], effect := d },
       CausalLaw.simple d c,
       CausalLaw.simple c e ]⟩
  use dyn, Situation.empty, c, e
  simp only [ccConstraintSatisfied]
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Completion does NOT entail membership in general.

    Causal chains: `completesForEffect` holds (simple but-for: removing
    the root blocks the effect through the chain) but `causeSem` fails
    (Def 10b: setting the intermediate directly bypasses the root).

    Witnessed by chain c → m → e from empty background. -/
theorem completion_not_entails_member :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      ccConstraintSatisfied .completionOfSufficientSet dyn bg c e ∧
      ¬ (ccConstraintSatisfied .memberOfSufficientSet dyn bg c e) := by
  let c := mkVar "c"
  let m := mkVar "m"
  let e := mkVar "e"
  let dyn := CausalDynamics.causalChain c m e
  use dyn, Situation.empty, c, e
  simp only [ccConstraintSatisfied]
  constructor <;> native_decide

/-- In single-pathway models, completion DOES entail membership.

    With no overdetermination and no intermediate bypass, Def 10b
    and simple but-for coincide. This captures @cite{fodor-1970}:
    *Sam opened the door* |= *Sam caused the door to open*. -/
theorem completion_entails_member_single_pathway
    (c e : Variable) :
    let dyn := CausalDynamics.mk [CausalLaw.simple c e]
    ccConstraintSatisfied .completionOfSufficientSet dyn Situation.empty c e →
    ccConstraintSatisfied .memberOfSufficientSet dyn Situation.empty c e := by
  intro dyn h
  -- h : completesForEffect dyn ∅ c e = true
  show causeSem dyn Situation.empty c e
  show _ ∧ _
  have hCompl : completesForEffect dyn Situation.empty c e = true := h
  simp only [completesForEffect, Bool.and_eq_true] at hCompl
  refine ⟨hCompl.1, ?_⟩
  exact simple_law_necessity c e

/-- Member mode asserts Def 10b necessity. -/
theorem member_asserts_necessity (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) (h : ccConstraintSatisfied .memberOfSufficientSet dyn bg c e) :
    causallyNecessary dyn bg c e := h.2

/-- Completion mode asserts sufficiency. -/
theorem completion_asserts_sufficiency (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) (h : ccConstraintSatisfied .completionOfSufficientSet dyn bg c e) :
    causallySufficient dyn bg c e := by
  -- h : completesForEffect dyn bg c e = true
  have hCompl : completesForEffect dyn bg c e = true := h
  simp only [completesForEffect, Bool.and_eq_true] at hCompl
  exact hCompl.1

-- ════════════════════════════════════════════════════
-- § 5. Type-Level vs Token-Level Causation
-- ════════════════════════════════════════════════════

/-- Type-level causal claim: a causal law holds between variable types.

    @cite{bar-asher-siegal-2026}: SEM models represent type-level causal
    knowledge — general dependencies among variables, independent of any
    specific event instance. A `CausalDynamics` encodes this: its laws
    state what WOULD happen given certain conditions, not what DID happen.

    `typeLevelSufficiency` checks whether a type-level causal law connects
    cause to effect: adding the cause to ANY background guarantees the effect.
    This is stronger than `causallySufficient` (which is background-relative). -/
def typeLevelSufficiency (dyn : CausalDynamics) (cause effect : Variable) : Bool :=
  causallySufficient dyn Situation.empty cause effect

/-- Token-level causal claim: in a specific actual situation, the cause
    brought about the effect.

    @cite{bar-asher-siegal-2026}: token-level causation applies to specific
    event instances, anchored to the actual world. It requires both that the
    cause occurred and that the effect counterfactually depended on it.

    This is exactly `actuallyCaused` from Necessity.lean. -/
def tokenLevelCausation (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Bool :=
  actuallyCaused dyn bg cause effect

/-- Type-level sufficiency entails token-level causation is possible.

    If a causal law connects cause to effect at the type level, then
    in any situation where the cause occurs and is the only pathway,
    it actually caused the effect. Witnessed by a simple c → e law. -/
theorem type_level_enables_token_level :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      typeLevelSufficiency dyn c e = true ∧
      tokenLevelCausation dyn bg c e = true := by
  use CausalDynamics.mk [CausalLaw.simple (mkVar "c") (mkVar "e")],
      Situation.empty.extend (mkVar "c") true, mkVar "c", mkVar "e"
  constructor <;> native_decide

/-- Type-level sufficiency does NOT guarantee token-level causation.

    Even when a causal law exists, overdetermination at the token level
    can block actual causation (the backup cause prevents necessity). -/
theorem type_level_not_sufficient_for_token :
    ∃ (dyn : CausalDynamics) (bg : Situation) (c e : Variable),
      typeLevelSufficiency dyn c e = true ∧
      tokenLevelCausation dyn bg c e = false := by
  use CausalDynamics.disjunctiveCausation (mkVar "c") (mkVar "b") (mkVar "e"),
      Situation.empty.extend (mkVar "c") true |>.extend (mkVar "b") true,
      mkVar "c", mkVar "e"
  constructor <;> native_decide

-- ════════════════════════════════════════════════════
-- § 6. Actualization Constraint
-- ════════════════════════════════════════════════════

/-- The actualization constraint: the cause is part of the only completed
    sufficient set realized in the actual world.

    @cite{baglini-bar-asher-siegal-2025} @cite{bar-asher-siegal-2026}: both
    CC-selection modes require actualization — the selected cause must belong
    to a sufficient set that (a) actually completed and (b) is the ONLY one
    that did. Condition (b) is what rules out overdetermined causes.

    Formally, this is exactly the but-for component of `completesForEffect`:
    removing the cause blocks the effect, meaning no other sufficient set
    completed without it. -/
def actualizationHolds (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) : Bool :=
  -- The cause occurred (sufficient set completed with it)
  (normalDevelopment dyn (bg.extend cause true)).hasValue effect true &&
  -- No other sufficient set completed without it (but-for)
  !(normalDevelopment dyn (bg.extend cause false)).hasValue effect true

/-- `completesForEffect` is equivalent to `actualizationHolds`.

    The but-for test in `completesForEffect` IS the actualization constraint:
    sufficiency ensures the cause's set completed, and the negated
    counterfactual ensures no other set did. -/
theorem completesForEffect_eq_actualization (dyn : CausalDynamics) (bg : Situation)
    (cause effect : Variable) :
    completesForEffect dyn bg cause effect = actualizationHolds dyn bg cause effect := rfl

/-- Actualization fails under overdetermination.

    When two independent causes are both present, neither satisfies
    actualization because removing either one still leaves the other's
    sufficient set complete. -/
theorem actualization_fails_overdetermination :
    let dyn := CausalDynamics.disjunctiveCausation (mkVar "l") (mkVar "a") (mkVar "f")
    let bg := Situation.empty.extend (mkVar "l") true |>.extend (mkVar "a") true
    actualizationHolds dyn bg (mkVar "l") (mkVar "f") = false := by
  native_decide

/-- Actualization holds for sole causes.

    When there's only one pathway and the cause completed it,
    actualization succeeds. -/
theorem actualization_holds_sole_cause :
    let dyn := CausalDynamics.mk [CausalLaw.simple (mkVar "c") (mkVar "e")]
    let bg := Situation.empty.extend (mkVar "c") true
    actualizationHolds dyn bg (mkVar "c") (mkVar "e") = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 7. Structural Dependency [c] D [e]
-- ════════════════════════════════════════════════════

/-- The structural dependency [c] D [e] from @cite{bar-asher-siegal-boneh-2020}.

    Causative constructions encode a structural dependency D between a
    cause element (c) and an effect element (e). This is more general than
    strict physical causation — it covers content-domain (genuine causal),
    epistemic (inferential), and speech-act (illocutionary) dependencies.

    `CausalDynamics` is the content-domain specialization where D is
    modeled by structural equations. For epistemic and speech-act domains,
    the dependency is grounded differently (see `SweetserDomain` in
    `Conditionals/ConditionalType.lean`).

    This structure packages the minimal ingredients needed to evaluate
    any CC-selection predicate. -/
structure CausalDependency where
  /-- The cause element. -/
  cause : Variable
  /-- The effect element. -/
  effect : Variable
  /-- The causal model encoding the dependency. -/
  dynamics : CausalDynamics
  /-- The background situation against which to evaluate. -/
  background : Situation

/-- Evaluate CC-selection on a packaged causal dependency. -/
def CausalDependency.satisfies (dep : CausalDependency)
    (mode : CCSelectionMode) : Bool :=
  ccConstraintSatisfied mode dep.dynamics dep.background dep.cause dep.effect

/-- Check actualization for a dependency. -/
def CausalDependency.actualized (dep : CausalDependency) : Bool :=
  actualizationHolds dep.dynamics dep.background dep.cause dep.effect

end Semantics.Causation.CCSelection
