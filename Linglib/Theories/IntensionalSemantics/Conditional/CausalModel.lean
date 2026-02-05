/-
# Structural Causal Models

Infrastructure for modeling structural (deterministic) causal dependencies
based on Pearl-style causal models.

## Key Concepts (Nadathur & Lauer 2020)

This module provides types for:
- **Situations**: Partial valuations of variables (Def 9)
- **Causal Laws**: Structural equations (if preconditions hold, effect follows) (Def 10)
- **Normal Causal Development**: Forward propagation to compute consequences (Def 15)

## Distinction from CausalBayesNet

| Aspect | CausalBayesNet (Grusdt et al.) | CausalModel (Nadathur & Lauer) |
|--------|--------------------------------|-------------------------------|
| Type | Probabilistic | Structural/Deterministic |
| Data | WorldState (P(A), P(C), P(AC)) | Situation (Variable → Option Bool) |
| Claim | High P(C\|A) | Counterfactual dependence |
| Use | Pragmatic inference (RSA) | Semantic truth conditions |
| Verbs | "if A then C" (conditionals) | "cause", "make" (causatives) |

The **connection**: Structural causation provides the ground truth that
probabilistic inference approximates. See Integration.lean for the bridge.

## References

- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa.
- Pearl, J. (2000). Causality: Models, Reasoning, and Inference.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

namespace Theories.TruthConditional.Conditional.CausalModel

-- Variables

/--
A variable in a causal model.

Variables are named entities whose values are determined by causal laws.
The paper uses Boolean variables (values in {0, 1}).
-/
structure Variable where
  name : String
  deriving DecidableEq, Hashable, Repr, BEq, Inhabited

instance : ToString Variable where
  toString v := v.name

/-- Create a variable from a string literal -/
def mkVar (name : String) : Variable := ⟨name⟩

-- Situations (Def 9)

/--
**Situation** (Definition 9 from Nadathur & Lauer 2020)

A partial valuation: some variables have known values, others are undetermined.
This models the "background state" before causal propagation.

Key insight: Situations are *partial* functions. This is crucial for:
- Modeling what's "given" vs what's computed
- Counterfactual reasoning (removing a cause = setting it to undetermined or false)
- Normal causal development (only determined preconditions can trigger laws)
-/
structure Situation where
  /-- The partial valuation: Variable → Option Bool -/
  valuation : Variable → Option Bool

namespace Situation

/-- The empty situation: nothing is determined -/
def empty : Situation := ⟨λ _ => none⟩

/-- Create a situation from a list of (variable, value) pairs -/
def ofList (assignments : List (Variable × Bool)) : Situation :=
  ⟨λ v => assignments.find? (λ (v', _) => v' == v) |>.map (·.2)⟩

/-- Get the value of a variable (if determined) -/
def get (s : Situation) (v : Variable) : Option Bool := s.valuation v

/-- Check if a variable is determined in the situation -/
def isDetermined (s : Situation) (v : Variable) : Bool := s.valuation v |>.isSome

/-- Check if a variable has a specific value in the situation -/
def hasValue (s : Situation) (v : Variable) (val : Bool) : Bool :=
  s.valuation v == some val

/--
**Extend** a situation with a new assignment: s ⊕ {v = val}

If the variable was already determined, the new value overwrites.
This is used for:
- Adding causes (to test sufficiency)
- Setting counterfactual values (to test necessity)
-/
def extend (s : Situation) (v : Variable) (val : Bool) : Situation :=
  ⟨λ v' => if v' == v then some val else s.valuation v'⟩

/-- Remove a variable from the situation (set to undetermined) -/
def remove (s : Situation) (v : Variable) : Situation :=
  ⟨λ v' => if v' == v then none else s.valuation v'⟩

/-- Combine two situations (right takes precedence) -/
def merge (s1 s2 : Situation) : Situation :=
  ⟨λ v => s2.valuation v <|> s1.valuation v⟩

/-- Check if situation s1 is subsumed by s2 (s2 agrees with s1 on all determined values) -/
def subsumes (_s1 _s2 : Situation) : Bool :=
  -- For all v where s1 is determined, s2 must have the same value
  true  -- Simplified: would need explicit variable enumeration for real check

instance : Inhabited Situation := ⟨Situation.empty⟩

end Situation

-- Causal Laws (Def 10)

/--
**Causal Law** (Definition 10 from Nadathur & Lauer 2020)

A causal law specifies: if all preconditions hold, the effect follows.

In the paper's notation: ⟨{(v₁, val₁), ..., (vₙ, valₙ)}, (vₑ, valₑ)⟩
means: if v₁ = val₁ ∧ ... ∧ vₙ = valₙ, then vₑ := valₑ

Typically valₑ = true (causes produce effects), but we allow arbitrary values
for generality (e.g., inhibitory causal laws).
-/
structure CausalLaw where
  /-- Preconditions that must all hold -/
  preconditions : List (Variable × Bool)
  /-- The variable affected by this law -/
  effect : Variable
  /-- The value the effect variable gets (default: true) -/
  effectValue : Bool := true
  deriving Repr, Inhabited

namespace CausalLaw

/-- Check if all preconditions of a law are satisfied in a situation -/
def preconditionsMet (law : CausalLaw) (s : Situation) : Bool :=
  law.preconditions.all λ (v, val) => s.hasValue v val

/-- Apply a law to a situation (if preconditions met, set effect) -/
def apply (law : CausalLaw) (s : Situation) : Situation :=
  if law.preconditionsMet s then
    s.extend law.effect law.effectValue
  else
    s

/-- Create a simple law: if v₁ = true, then vₑ = true -/
def simple (cause effect : Variable) : CausalLaw :=
  { preconditions := [(cause, true)], effect := effect }

/-- Create a conjunctive law: if v₁ = true ∧ v₂ = true, then vₑ = true -/
def conjunctive (cause1 cause2 effect : Variable) : CausalLaw :=
  { preconditions := [(cause1, true), (cause2, true)], effect := effect }

end CausalLaw

-- Causal Dynamics

/--
**Causal Dynamics**: A collection of causal laws.

This represents the structural equations of a causal model.
Multiple laws can affect the same variable (disjunctive causation).
-/
structure CausalDynamics where
  /-- The laws governing causal propagation -/
  laws : List CausalLaw
  deriving Repr, Inhabited

namespace CausalDynamics

/-- Empty dynamics (no causal laws) -/
def empty : CausalDynamics := ⟨[]⟩

/-- Create dynamics from a list of laws -/
def ofList (laws : List CausalLaw) : CausalDynamics := ⟨laws⟩

/-- Add a law to the dynamics -/
def addLaw (dyn : CausalDynamics) (law : CausalLaw) : CausalDynamics :=
  ⟨law :: dyn.laws⟩

/-- Get all laws affecting a specific variable -/
def lawsFor (dyn : CausalDynamics) (v : Variable) : List CausalLaw :=
  dyn.laws.filter (·.effect == v)

end CausalDynamics

-- Normal Causal Development (Def 15)

/--
Apply all laws once to a situation.

This is one step of forward propagation: for each law, if its preconditions
are met, set its effect variable.
-/
def applyLawsOnce (dyn : CausalDynamics) (s : Situation) : Situation :=
  dyn.laws.foldl (λ s' law => law.apply s') s

/--
Check if a situation is a fixpoint (no law can change it).

A situation is a fixpoint when applying all laws leaves it unchanged.
-/
def isFixpoint (dyn : CausalDynamics) (s : Situation) : Bool :=
  dyn.laws.all λ law =>
    !law.preconditionsMet s ||  -- Either preconditions not met
    s.hasValue law.effect law.effectValue  -- Or effect already has the value

/--
**Normal Causal Development** (Definition 15)

Iterate forward propagation until fixpoint is reached.

Given an initial situation, compute what necessarily happens by
repeatedly applying causal laws until no more changes occur.

Uses bounded iteration (fuel) to ensure termination.
In practice, convergence is typically fast (O(number of variables)).
-/
def normalDevelopment (dyn : CausalDynamics) (s : Situation)
    (fuel : Nat := 100) : Situation :=
  match fuel with
  | 0 => s  -- Out of fuel: return current state
  | n + 1 =>
    let s' := applyLawsOnce dyn s
    if isFixpoint dyn s' then s'
    else normalDevelopment dyn s' n

-- Fixpoint Theorems

/-- Unfold normalDevelopment one step. -/
@[simp] theorem normalDevelopment_succ (dyn : CausalDynamics) (s : Situation) (n : Nat) :
    normalDevelopment dyn s (n + 1) =
      let s' := applyLawsOnce dyn s
      if isFixpoint dyn s' then s' else normalDevelopment dyn s' n := rfl

/-- If the result of one round of law application is a fixpoint,
    normalDevelopment returns that result. -/
theorem normalDevelopment_fixpoint_after_one (dyn : CausalDynamics) (s : Situation) {fuel : Nat}
    (h : isFixpoint dyn (applyLawsOnce dyn s) = true) :
    normalDevelopment dyn s (fuel + 1) = applyLawsOnce dyn s := by
  simp [h]

/--
Empty dynamics has trivial fixpoint: any situation is a fixpoint.
-/
theorem empty_dynamics_fixpoint (s : Situation) :
    isFixpoint CausalDynamics.empty s = true := by
  simp only [isFixpoint, CausalDynamics.empty, List.all_eq_true]
  intro x hx
  simp at hx

/--
Normal development of empty dynamics returns the input unchanged.
-/
theorem empty_dynamics_unchanged (s : Situation) (fuel : Nat) :
    normalDevelopment CausalDynamics.empty s fuel = s := by
  induction fuel with
  | zero => rfl
  | succ n _ =>
    simp only [normalDevelopment, applyLawsOnce, CausalDynamics.empty, List.foldl_nil,
               isFixpoint, List.all_eq_true]
    simp

/--
If a situation is already a fixpoint, normal development doesn't change it.
-/
theorem fixpoint_unchanged (dyn : CausalDynamics) (s : Situation) (fuel : Nat)
    (h : isFixpoint dyn s = true) :
    normalDevelopment dyn s fuel = s := by
  cases fuel with
  | zero => rfl
  | succ n =>
    simp only [normalDevelopment]
    -- After one step, we reach a fixpoint
    have h' : isFixpoint dyn (applyLawsOnce dyn s) = true := by
      simp only [isFixpoint, List.all_eq_true] at h ⊢
      intro law hlaw
      have := h law hlaw
      simp only [Bool.or_eq_true, Bool.not_eq_true', CausalLaw.preconditionsMet] at this ⊢
      cases this with
      | inl h_not_met =>
        left
        -- If preconditions weren't met in s, need to check in applyLawsOnce dyn s
        sorry  -- Complex: depends on which laws fire
      | inr h_already_has =>
        right
        -- If effect already has value, it still has it after applying laws
        sorry  -- Complex: need to track through foldl
    sorry  -- Full proof requires more machinery

-- Convenience Functions

/--
Get the value of a variable after normal development.
-/
def developedValue (dyn : CausalDynamics) (s : Situation) (v : Variable) : Option Bool :=
  (normalDevelopment dyn s).get v

/--
Check if a variable becomes true after normal development.
-/
def developsToBe (dyn : CausalDynamics) (s : Situation) (v : Variable) (val : Bool) : Bool :=
  (normalDevelopment dyn s).hasValue v val

/--
Check if a variable becomes true after normal development.
-/
def developsToTrue (dyn : CausalDynamics) (s : Situation) (v : Variable) : Bool :=
  developsToBe dyn s v true

/--
Check if an effect occurs given a cause in some background.
-/
def effectOccurs (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Bool :=
  let withCause := background.extend cause true
  developsToTrue dyn withCause effect

-- Common Causal Structures

namespace CausalDynamics

/--
Create dynamics for disjunctive causation: A ∨ B → C

Either cause alone is sufficient for the effect.
Used in overdetermination examples.
-/
def disjunctiveCausation (cause1 cause2 effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.simple cause1 effect, CausalLaw.simple cause2 effect]⟩

/--
Create dynamics for conjunctive causation: A ∧ B → C

Both causes required for the effect.
-/
def conjunctiveCausation (cause1 cause2 effect : Variable) : CausalDynamics :=
  ⟨[CausalLaw.conjunctive cause1 cause2 effect]⟩

/--
Create dynamics for simple causation: A → B → C

Causal chain: A causes B, B causes C.
-/
def causalChain (a b c : Variable) : CausalDynamics :=
  ⟨[CausalLaw.simple a b, CausalLaw.simple b c]⟩

end CausalDynamics

end Theories.TruthConditional.Conditional.CausalModel
