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
| `CausativeBuilder` | Builder.lean | Derived via `.selectionMode` |
| `CausationType` | ProductionDependence.lean | Derived via `.selectionMode` |
| `CausalProfile` | Core/StructuralEquationModel.lean | Computed by evaluating selection against a model |

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

namespace Causation.CCSelection

open Core.StructuralEquationModel
open NadathurLauer2020.Sufficiency
open NadathurLauer2020.Necessity

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
  causallySufficient dyn background cause effect &&
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
    CCSelectionMode → (CausalDynamics → Situation → Variable → Variable → Bool)
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
    (cause effect : Variable) : Bool :=
  match mode with
  | .memberOfSufficientSet => causeSem dyn bg cause effect
  | .completionOfSufficientSet => completesForEffect dyn bg cause effect

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
    (h : ccConstraintSatisfied .memberOfSufficientSet dyn bg c e = true) :
    ccConstraintSatisfied .completionOfSufficientSet dyn bg c e = true := by
  simp only [ccConstraintSatisfied] at *
  simp only [causeSem, Bool.and_eq_true] at h
  simp only [completesForEffect, Bool.and_eq_true, Bool.not_eq_true']
  obtain ⟨hOccurred, hNec⟩ := h
  constructor
  · exact hOccurred
  · -- Simple but-for: normalDev(bg + c=false) doesn't achieve e=true.
    -- Step 1: Extract from Def 10b that normalDev(bg) doesn't have e=true.
    -- If it did, causallyNecessary would return false (precondition check).
    have hNoE : (normalDevelopment dyn bg).hasValue e true = false := by
      rcases Bool.eq_false_or_eq_true ((normalDevelopment dyn bg).hasValue e true)
        with h | h
      · -- h : ... = true → precondition fails → causallyNecessary = false
        have : causallyNecessary dyn bg c e = false := by
          unfold causallyNecessary
          simp only [h, Bool.or_true, ↓reduceIte]
        rw [this] at hNec; simp at hNec
      · exact h
    -- Step 2: trueLE (bg.extend c false) bg (c=false adds no true content)
    have hLE : Situation.trueLE (bg.extend c false) bg := by
      intro v hv
      by_cases hvc : v = c
      · subst hvc; simp at hv
      · rw [Situation.extend_hasValue_diff hvc] at hv; exact hv
    -- Step 3: Monotonicity → normalDev(bg+c=false) ⊑ normalDev(bg)
    -- Therefore e=true in normalDev(bg+c=false) would imply e=true in normalDev(bg)
    have hMono := normalDevelopment_trueLE_positive dyn _ _ 100 hPos hLE e
    -- Step 4: Contrapositive of hMono + hNoE closes the goal
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
      ccConstraintSatisfied .memberOfSufficientSet dyn bg c e = true ∧
      ccConstraintSatisfied .completionOfSufficientSet dyn bg c e = false := by
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
      ccConstraintSatisfied .completionOfSufficientSet dyn bg c e = true ∧
      ccConstraintSatisfied .memberOfSufficientSet dyn bg c e = false := by
  let c := mkVar "c"
  let m := mkVar "m"
  let e := mkVar "e"
  let dyn := CausalDynamics.causalChain c m e
  use dyn, Situation.empty, c, e
  simp only [ccConstraintSatisfied]
  constructor <;> native_decide

/-- In single-pathway models, completion DOES entail membership.

    With no overdetermination and no intermediate bypass, Def 10b
    and simple but-for coincide. This captures Fodor 1970:
    *Sam opened the door* |= *Sam caused the door to open*. -/
theorem completion_entails_member_single_pathway
    (c e : Variable) :
    let dyn := CausalDynamics.mk [CausalLaw.simple c e]
    ccConstraintSatisfied .completionOfSufficientSet dyn Situation.empty c e = true →
    ccConstraintSatisfied .memberOfSufficientSet dyn Situation.empty c e = true := by
  intro dyn h
  simp only [ccConstraintSatisfied] at *
  simp only [completesForEffect, Bool.and_eq_true] at h
  simp only [causeSem, Bool.and_eq_true]
  constructor
  · exact h.1
  · exact simple_law_necessity c e

/-- Member mode asserts Def 10b necessity. -/
theorem member_asserts_necessity (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) (h : ccConstraintSatisfied .memberOfSufficientSet dyn bg c e = true) :
    causallyNecessary dyn bg c e = true := by
  simp only [ccConstraintSatisfied, causeSem, Bool.and_eq_true] at h
  exact h.2

/-- Completion mode asserts sufficiency. -/
theorem completion_asserts_sufficiency (dyn : CausalDynamics) (bg : Situation)
    (c e : Variable) (h : ccConstraintSatisfied .completionOfSufficientSet dyn bg c e = true) :
    causallySufficient dyn bg c e = true := by
  simp only [ccConstraintSatisfied, completesForEffect, Bool.and_eq_true] at h
  exact h.1

end Causation.CCSelection
