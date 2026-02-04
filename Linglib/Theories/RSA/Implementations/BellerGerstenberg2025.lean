/-
# Beller & Gerstenberg (2025)

"Causation, Meaning, and Communication"
Psychological Review

RSA model for causal expression choice based on three causal aspects from the
Counterfactual Simulation Model (CSM):

| Aspect | Symbol | Definition |
|--------|--------|------------|
| Whether-causation | W | Counterfactual necessity (but-for causation) |
| Sufficient-causation | S | Would have been enough alone |
| How-causation | H | Fine-grained process difference |

## Causal Expressions

The paper analyzes four causal expressions with overlapping semantics:

| Expression | Semantics | Scalar Position |
|------------|-----------|-----------------|
| affected | W ∨ H ∨ S | Weakest |
| enabled | W ∨ S | Middle |
| caused | H ∧ (W ∨ S) | Strongest |
| made_no_difference | ¬W ∧ ¬H ∧ ¬S | Negative |

## Simplifications

This implementation simplifies the causal reasoning machinery from the paper.
We use Boolean aspects (W, H, S) directly rather than computing them from
full structural causal models. This captures the RSA pragmatic reasoning
over causal expressions while avoiding the complexity of CSM counterfactual
computation.

For full causal model integration, see:
- `Core.CausalModel` for structural causal dynamics
- `NadathurLauer2020.Necessity` for causallyNecessary (≈ W)
- `NadathurLauer2020.Sufficiency` for causallySufficient (≈ S)

## References

- Beller, A. & Gerstenberg, T. (2025). Causation, Meaning, and Communication.
  Psychological Review.
- Gerstenberg, T. et al. (2021). A counterfactual simulation model of
  causal judgments for physical events. Psychological Review.
-/

import Linglib.Theories.RSA.Core.Basic
import Mathlib.Data.Rat.Defs

namespace RSA.BellerGerstenberg2025


/--
Causal expressions in English for describing causation.

These form a scalar hierarchy: caused > enabled > affected
-/
inductive CausalExpression
  | affected          -- "X affected Y" - weakest positive
  | enabled           -- "X enabled Y" - middle
  | caused            -- "X caused Y" - strongest
  | madeNoDifference  -- "X made no difference to Y" - negative
  deriving DecidableEq, BEq, Repr, Inhabited, Fintype

/-- FinEnum instance for computable enumeration -/
instance : FinEnum CausalExpression :=
  FinEnum.ofList [.affected, .enabled, .caused, .madeNoDifference]
    (fun x => by cases x <;> simp)

instance : ToString CausalExpression where
  toString
    | .affected => "affected"
    | .enabled => "enabled"
    | .caused => "caused"
    | .madeNoDifference => "made no difference"

/--
A causal world encapsulates the three causal aspects from CSM.

## Simplification Note

This is a simplified representation. In the full paper, these aspects
are computed from structural causal models via counterfactual simulation.
Here we treat them as primitive Boolean features to focus on the
RSA pragmatic reasoning over expression choice.

See `Core.CausalModel` and `NadathurLauer2020` for full causal machinery.
-/
structure CausalWorld where
  /-- Whether-causation: was cause necessary? (but-for test) -/
  whether : Bool
  /-- How-causation: did cause affect *how* outcome occurred? -/
  how : Bool
  /-- Sufficient-causation: was cause sufficient? -/
  sufficient : Bool
  deriving DecidableEq, BEq, Repr, Inhabited

instance : ToString CausalWorld where
  toString cw :=
    let w := if cw.whether then "W" else "¬W"
    let h := if cw.how then "H" else "¬H"
    let s := if cw.sufficient then "S" else "¬S"
    s!"({w}, {h}, {s})"

/-- All 8 possible causal worlds (2³ combinations of W, H, S) -/
def allCausalWorlds : List CausalWorld :=
  [ ⟨false, false, false⟩,
    ⟨false, false, true⟩,
    ⟨false, true, false⟩,
    ⟨false, true, true⟩,
    ⟨true, false, false⟩,
    ⟨true, false, true⟩,
    ⟨true, true, false⟩,
    ⟨true, true, true⟩ ]

instance : Fintype CausalWorld where
  elems := {
    ⟨false, false, false⟩,
    ⟨false, false, true⟩,
    ⟨false, true, false⟩,
    ⟨false, true, true⟩,
    ⟨true, false, false⟩,
    ⟨true, false, true⟩,
    ⟨true, true, false⟩,
    ⟨true, true, true⟩
  }
  complete := by
    intro ⟨w, h, s⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, CausalWorld.mk.injEq]
    cases w <;> cases h <;> cases s <;> simp

/-- FinEnum instance for computable enumeration -/
instance : FinEnum CausalWorld :=
  FinEnum.ofList allCausalWorlds (fun ⟨w, h, s⟩ => by
    simp only [allCausalWorlds, List.mem_cons, CausalWorld.mk.injEq]
    cases w <;> cases h <;> cases s <;> simp)


/--
Semantics of causal expressions in terms of causal aspects.

From Beller & Gerstenberg (2025):
- affected: W ∨ H ∨ S (any causal involvement)
- enabled: W ∨ S (necessity or sufficiency, but not just how)
- caused: H ∧ (W ∨ S) (process + counterfactual dependence)
- made_no_difference: ¬W ∧ ¬H ∧ ¬S (no causal involvement)
-/
def expressionMeaning (cw : CausalWorld) : CausalExpression → Bool
  | .affected => cw.whether || cw.how || cw.sufficient
  | .enabled => cw.whether || cw.sufficient
  | .caused => cw.how && (cw.whether || cw.sufficient)
  | .madeNoDifference => !cw.whether && !cw.how && !cw.sufficient

/-- Truth in a world as rational (for RSA φ function) -/
def expressionMeaningRat (cw : CausalWorld) (u : CausalExpression) : ℚ :=
  boolToRat (expressionMeaning cw u)


/--
RSA scenario for causal expression choice.

The speaker observes a causal world (W, H, S values) and chooses an
expression. The listener hears the expression and infers the world.
-/
def scenario : RSAScenario CausalExpression CausalWorld :=
  RSAScenario.basicBool
    (satisfies := fun cw u => expressionMeaning cw u)
    (prior := fun _ => 1)
    (prior_nonneg := fun _ => le_refl 0 |> fun _ => by norm_num)
    (cost := fun _ => 0)
    (cost_nonneg := fun _ => le_refl 0)
    (utterancePrior := fun _ => 1)
    (utterancePrior_nonneg := fun _ => le_refl 0 |> fun _ => by norm_num)

/-- Default scenario with uniform prior over causal worlds -/
def defaultScenario : RSAScenario CausalExpression CausalWorld := scenario


/-!
## FinEnum-Based Evaluation

With FinEnum instances for CausalExpression and CausalWorld, we can use
the RSA.evalL0/evalS1/evalL1 functions directly. These take explicit type
equalities that are resolved by `rfl` since the scenario is built with basicBool.
-/

/-- L0: Literal listener given expression -/
def runL0 (u : CausalExpression) : List (CausalWorld × ℚ) :=
  scenario.evalL0 u

/-- S1: Pragmatic speaker given world -/
def runS1 (cw : CausalWorld) : List (CausalExpression × ℚ) :=
  scenario.evalS1 cw

/-- L1: Pragmatic listener given expression -/
def runL1 (u : CausalExpression) : List (CausalWorld × ℚ) :=
  scenario.evalL1 u


/--
"caused" implies "enabled": if H ∧ (W ∨ S) then W ∨ S.

This captures the scalar relationship: "caused" is stronger than "enabled".
-/
theorem caused_implies_enabled (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .enabled := by
  simp only [expressionMeaning, Bool.and_eq_true, Bool.or_eq_true]
  intro ⟨_, h_ws⟩
  exact h_ws

/--
"enabled" implies "affected": if W ∨ S then W ∨ H ∨ S.

This captures the scalar relationship: "enabled" is stronger than "affected".
-/
theorem enabled_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .enabled → expressionMeaning cw .affected := by
  simp only [expressionMeaning]
  cases cw.whether <;> cases cw.how <;> cases cw.sufficient <;> decide

/--
Full scalar chain: caused → enabled → affected.
-/
theorem caused_implies_affected (cw : CausalWorld) :
    expressionMeaning cw .caused → expressionMeaning cw .affected :=
  fun h => enabled_implies_affected cw (caused_implies_enabled cw h)

/--
"madeNoDifference" is the negation of "affected".
-/
theorem madeNoDifference_iff_not_affected (cw : CausalWorld) :
    expressionMeaning cw .madeNoDifference ↔ !expressionMeaning cw .affected := by
  simp only [expressionMeaning]
  cases cw.whether <;> cases cw.how <;> cases cw.sufficient <;> decide


/-- World where cause was only necessary (W only) -/
def world_W_only : CausalWorld := ⟨true, false, false⟩

/-- World where cause was only sufficient (S only) -/
def world_S_only : CausalWorld := ⟨false, false, true⟩

/-- World where cause affected how (H only) -/
def world_H_only : CausalWorld := ⟨false, true, false⟩

/-- World with full causation (W, H, S all true) -/
def world_full : CausalWorld := ⟨true, true, true⟩

/-- World with no causal involvement -/
def world_none : CausalWorld := ⟨false, false, false⟩

/-- World where "caused" applies (H and W) -/
def world_caused : CausalWorld := ⟨true, true, false⟩


/-- In W-only world, "enabled" is true but "caused" is false -/
theorem W_only_enabled_not_caused :
    expressionMeaning world_W_only .enabled = true ∧
    expressionMeaning world_W_only .caused = false := by
  simp only [expressionMeaning, world_W_only]
  decide

/-- In H-only world, neither "caused" nor "enabled" applies -/
theorem H_only_affected_only :
    expressionMeaning world_H_only .affected = true ∧
    expressionMeaning world_H_only .enabled = false ∧
    expressionMeaning world_H_only .caused = false := by
  simp only [expressionMeaning, world_H_only]
  decide

/-- In full world, all positive expressions apply -/
theorem full_world_all_true :
    expressionMeaning world_full .affected = true ∧
    expressionMeaning world_full .enabled = true ∧
    expressionMeaning world_full .caused = true ∧
    expressionMeaning world_full .madeNoDifference = false := by
  simp only [expressionMeaning, world_full]
  decide

/-- In none world, only madeNoDifference applies -/
theorem none_world_only_negative :
    expressionMeaning world_none .affected = false ∧
    expressionMeaning world_none .enabled = false ∧
    expressionMeaning world_none .caused = false ∧
    expressionMeaning world_none .madeNoDifference = true := by
  simp only [expressionMeaning, world_none]
  decide


#eval runL0 .caused   -- Worlds where "caused" is literally true
#eval runL0 .enabled  -- Worlds where "enabled" is literally true

#eval runS1 world_full    -- What speaker says in full causation world
#eval runS1 world_W_only  -- What speaker says when only W is true
#eval runS1 world_H_only  -- What speaker says when only H is true

#eval runL1 .caused   -- Listener inference from "caused"
#eval runL1 .enabled  -- Listener inference from "enabled"

-- Summary

/-!
## How RSA Derives Causal Expression Pragmatics

### Literal Semantics (L0)
- "caused" → true in worlds with H ∧ (W ∨ S)
- "enabled" → true in worlds with W ∨ S
- "affected" → true in worlds with W ∨ H ∨ S

### Pragmatic Speaker (S1)
- In world_full (W, H, S all true): prefers "caused" (most informative)
- In world_W_only: "enabled" is more informative than "affected"
- In world_H_only: only "affected" applies

### Pragmatic Listener (L1)
- Hearing "caused": infers H is likely true
- Hearing "enabled" (not "caused"): infers H is likely false
- Hearing "affected" (not "enabled"): infers W and S both likely false

This captures the scalar implicature pattern: stronger expressions
implicate the presence of stronger causal aspects.
-/

end RSA.BellerGerstenberg2025
