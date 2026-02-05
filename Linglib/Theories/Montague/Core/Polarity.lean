/-
# Grounded Context Polarity

This module provides comprehensive infrastructure for monotonicity/polarity
in semantics and pragmatics.

## Contents

1. ContextPolarity enum - Theory-neutral polarity marker (upward/downward)
2. IsUpwardEntailing/IsDownwardEntailing - Mathlib-based formal definitions
3. Decidable test functions - For verification on finite models
4. GroundedPolarity - Context + polarity + proof
5. Monotonicity theorems - Negation, conditionals, quantifiers

## Integration with Mathlib

We use Mathlib's order-theoretic infrastructure:
- `Monotone f` (from `Mathlib.Order.Monotone.Basic`): `∀ a b, a ≤ b → f a ≤ f b`
- `Antitone f`: `∀ a b, a ≤ b → f b ≤ f a`

For `Prop' = World → Bool`, the ordering is pointwise: `p ≤ q ↔ ∀ w, p w ≤ q w`
where for `Bool`, `false ≤ true`.

Mathlib provides composition lemmas for free:
- `Monotone.comp`: UE ∘ UE = UE
- `Antitone.comp_antitone`: DE ∘ DE = UE (the "double negation" rule!)
- `Monotone.comp_antitone`: UE ∘ DE = DE
- `Antitone.comp`: DE ∘ UE = DE

## References

- van Benthem (1986). Essays in Logical Semantics.
- Ladusaw (1980). Polarity Sensitivity as Inherent Scope Relations.
- Barwise & Cooper (1981). Generalized Quantifiers and Natural Language.
-/

import Mathlib.Order.Monotone.Defs
import Linglib.Theories.Montague.Sentence.Entailment.Basic

namespace Montague.Core.Polarity

open Montague.Sentence.Entailment


/--
Whether a context preserves or reverses entailment direction.

Used by:
- NeoGricean: determines which alternatives count as "stronger"
- RSA: polarity-sensitive inference
- Any theory computing scalar implicatures
-/
inductive ContextPolarity where
  | upward       -- Preserves entailment (stronger alternatives)
  | downward     -- Reverses entailment (weaker alternatives become stronger)
  | nonMonotonic -- Neither (e.g., "exactly n")
  deriving DecidableEq, Repr


/-
For Prop' = World → Bool, we have:
- BooleanAlgebra (World → Bool) via Pi.instBooleanAlgebra + Bool.instBooleanAlgebraBool
- This gives us a lattice ordering: p ≤ q ↔ ∀ w, p w → q w (when lifted from Bool)

We use Mathlib's Monotone/Antitone as the canonical definitions.
-/

/--
IsUpwardEntailing is an abbreviation for `Monotone`.

A context function `f : Prop' → Prop'` is upward entailing if
it preserves the ordering: If p ≤ q, then f(p) ≤ f(q).

Examples: "some", "or", scope of "every"
-/
abbrev IsUpwardEntailing (f : Prop' → Prop') := Monotone f

/--
IsDownwardEntailing is an abbreviation for `Antitone`.

A context function `f : Prop' → Prop'` is downward entailing if
it reverses the ordering: If p ≤ q, then f(q) ≤ f(p).

Examples: "no", "not", restrictor of "every"
-/
abbrev IsDownwardEntailing (f : Prop' → Prop') := Antitone f

-- Shorthand aliases for readability
abbrev IsUE := IsUpwardEntailing
abbrev IsDE := IsDownwardEntailing


/--
Identity is UE: The trivial context preserves entailment.
-/
theorem id_isUpwardEntailing : IsUpwardEntailing (id : Prop' → Prop') :=
  monotone_id

/--
Negation is DE: If P ⊆ Q, then ¬Q ⊆ ¬P.

Uses `Core.Proposition.Decidable.pnot_antitone` for the proof.
-/
theorem pnot_isDownwardEntailing : IsDownwardEntailing pnot := by
  intro p q hpq w
  simp only [pnot, Core.Proposition.Decidable.pnot]
  -- For Bool, p ≤ q at w means: if p w = true then q w = true
  -- We need: !q w ≤ !p w, i.e., if q w = false then p w = false
  have hpq_w := hpq w
  cases hp : p w <;> cases hq : q w <;> simp_all

/--
Double negation is UE: negating twice preserves entailment.

This follows from Mathlib's `Antitone.comp` (DE ∘ DE = UE).
-/
theorem pnot_pnot_isUpwardEntailing : IsUpwardEntailing (pnot ∘ pnot) :=
  pnot_isDownwardEntailing.comp pnot_isDownwardEntailing


/-
Mathlib provides all the composition rules we need:

- `Monotone.comp`: UE ∘ UE = UE
- `Antitone.comp_antitone`: DE ∘ DE = UE
- `Monotone.comp_antitone`: UE ∘ DE = DE
- `Antitone.comp`: DE ∘ UE = DE

These are the polarity composition rules, proven once and for all!
-/

/-- UE ∘ UE = UE (from Mathlib) -/
theorem ue_comp_ue {f g : Prop' → Prop'} (hf : IsUpwardEntailing f) (hg : IsUpwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- DE ∘ DE = UE (from Mathlib - the double negation rule!) -/
theorem de_comp_de {f g : Prop' → Prop'} (hf : IsDownwardEntailing f) (hg : IsDownwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- UE ∘ DE = DE (from Mathlib) -/
theorem ue_comp_de {f g : Prop' → Prop'} (hf : IsUpwardEntailing f) (hg : IsDownwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_antitone hg

/-- DE ∘ UE = DE (from Mathlib) -/
theorem de_comp_ue {f g : Prop' → Prop'} (hf : IsDownwardEntailing f) (hg : IsUpwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_monotone hg


/--
Check if f is upward entailing on given test cases.

This is a decidable approximation: it checks the property on a finite
set of test cases rather than proving it universally.
-/
def isUpwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f p) (f q)

/--
Check if f is downward entailing on given test cases.

This is a decidable approximation: it checks the property on a finite
set of test cases rather than proving it universally.
-/
def isDownwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f q) (f p)


/--
Negation is Downward Entailing.

If P ⊨ Q, then ¬Q ⊨ ¬P

Test: p0 ⊨ p01, so ¬p01 ⊨ ¬p0
-/
theorem negation_is_DE : isDownwardEntailing pnot testCases = true := by
  native_decide

/--
Negation reverses entailment.

p0 ⊨ p01 (true in {w0} entails true in {w0,w1})
¬p01 ⊨ ¬p0 (false in {w0,w1} entails false in {w0})
-/
theorem negation_reverses_example :
    entails p0 p01 = true ∧
    entails (pnot p01) (pnot p0) = true := by
  native_decide

/--
Conjunction (second arg) is Upward Entailing.

If P ⊨ Q, then (R ∧ P) ⊨ (R ∧ Q)
-/
theorem conjunction_second_UE : isUpwardEntailing (pand p01) testCases = true := by
  native_decide

/--
Disjunction (second arg) is Upward Entailing.

If P ⊨ Q, then (R ∨ P) ⊨ (R ∨ Q)
-/
theorem disjunction_second_UE : isUpwardEntailing (por p01) testCases = true := by
  native_decide

/--
Double negation is UE (decidable verification).
-/
theorem double_negation_is_ue : isUpwardEntailing (pnot ∘ pnot) testCases = true := by
  native_decide


/-- Material conditional with fixed consequent: "If _, then c" -/
def materialCond (c : Prop') : Prop' → Prop' :=
  λ p => λ w => !p w || c w

/--
Conditional antecedent is Downward Entailing.

If P ⊨ Q, then "If Q, C" ⊨ "If P, C"

This is the core DE property of conditional antecedents: strengthening the
antecedent weakens the conditional (via contraposition).

Example: "dogs" ⊨ "animals", so "If it's an animal, it barks" ⊨ "If it's a dog, it barks"
-/
theorem conditional_antecedent_DE :
    isDownwardEntailing (materialCond p012) testCases = true := by
  native_decide

/--
Implication second argument is UE.

If P ⊨ Q, then (A → P) ⊨ (A → Q)

The consequent position of a conditional is upward entailing.
-/
theorem implication_consequent_UE : isUpwardEntailing (λ c => materialCond c p01) testCases = true := by
  native_decide

/--
Conditional positions and monotonicity.

- Antecedent position: DE (strengthening weakens the conditional)
- Consequent position: UE (strengthening strengthens the conditional)

This explains scalar implicature patterns:
- "If some passed, happy" - antecedent is DE, so SI blocked (global preferred)
- "If passed, happy about some" - consequent is UE, so SI computed (local available)
-/
theorem conditional_monotonicity_summary :
    isDownwardEntailing (materialCond p012) testCases = true ∧
    isUpwardEntailing (λ c => materialCond c p01) testCases = true := by
  constructor
  · exact conditional_antecedent_DE
  · exact implication_consequent_UE


/--
DE contexts reverse scalar strength.

In UE: all ⊢ some (all is stronger, "some" implicates "not all")
In DE: some ⊢ all (some is stronger, no "not all" implicature)
-/
theorem de_reverses_strength :
    -- In UE context (identity), p0 ⊢ p01 means p0 is stronger
    entails p0 p01 = true ∧
    -- Under negation (DE), the relationship reverses
    entails (pnot p01) (pnot p0) = true := by
  native_decide


/--
A grounded UE polarity carries proof that a context function is monotone.
-/
structure GroundedUE where
  /-- The context function -/
  context : Prop' → Prop'
  /-- Proof of monotonicity (UE) -/
  witness : Monotone context

/--
A grounded DE polarity carries proof that a context function is antitone.
-/
structure GroundedDE where
  /-- The context function -/
  context : Prop' → Prop'
  /-- Proof of antitonicity (DE) -/
  witness : Antitone context

/--
A grounded polarity is either UE or DE, with proof.
-/
inductive GroundedPolarity where
  | ue : GroundedUE → GroundedPolarity
  | de : GroundedDE → GroundedPolarity

/--
Extract the ContextPolarity enum from a grounded polarity.
-/
def GroundedPolarity.toContextPolarity : GroundedPolarity → ContextPolarity
  | .ue _ => .upward
  | .de _ => .downward

/--
Create a grounded UE polarity from a proof.
-/
def mkUpward (ctx : Prop' → Prop') (h : Monotone ctx) : GroundedPolarity :=
  .ue ⟨ctx, h⟩

/--
Create a grounded DE polarity from a proof.
-/
def mkDownward (ctx : Prop' → Prop') (h : Antitone ctx) : GroundedPolarity :=
  .de ⟨ctx, h⟩

/--
The identity context is grounded UE.
-/
def identityPolarity : GroundedPolarity := mkUpward id id_isUpwardEntailing

/--
Negation is grounded DE.
-/
def negationPolarity : GroundedPolarity := mkDownward pnot pnot_isDownwardEntailing


/--
Compose two polarities, with proof that the composition has the right property.

This is the key function for compositional polarity tracking through
derivation trees.
-/
def composePolarity (outer inner : GroundedPolarity) : GroundedPolarity :=
  match outer, inner with
  | .ue ⟨f, hf⟩, .ue ⟨g, hg⟩ =>
    -- UE ∘ UE = UE
    .ue ⟨f ∘ g, ue_comp_ue hf hg⟩
  | .ue ⟨f, hf⟩, .de ⟨g, hg⟩ =>
    -- UE ∘ DE = DE
    .de ⟨f ∘ g, ue_comp_de hf hg⟩
  | .de ⟨f, hf⟩, .ue ⟨g, hg⟩ =>
    -- DE ∘ UE = DE
    .de ⟨f ∘ g, de_comp_ue hf hg⟩
  | .de ⟨f, hf⟩, .de ⟨g, hg⟩ =>
    -- DE ∘ DE = UE (double negation!)
    .ue ⟨f ∘ g, de_comp_de hf hg⟩


/--
Polarity composition table is correct.

| Outer | Inner | Result |
|-------|-------|--------|
| UE    | UE    | UE     |
| UE    | DE    | DE     |
| DE    | UE    | DE     |
| DE    | DE    | UE     |

This is provable because `composePolarity` uses Mathlib's composition proofs.
-/
theorem polarity_composition_table :
    (composePolarity identityPolarity identityPolarity).toContextPolarity = .upward ∧
    (composePolarity identityPolarity negationPolarity).toContextPolarity = .downward ∧
    (composePolarity negationPolarity identityPolarity).toContextPolarity = .downward ∧
    (composePolarity negationPolarity negationPolarity).toContextPolarity = .upward := by
  simp only [composePolarity, identityPolarity, negationPolarity, mkUpward, mkDownward,
             GroundedPolarity.toContextPolarity, and_self]

/--
Double DE gives UE.

This captures the linguistic insight: "It's not the case that no one..."
creates a UE context for the embedded scalar item.
-/
theorem double_de_is_ue_grounded (f g : Prop' → Prop') (hf : Antitone f) (hg : Antitone g) :
    (composePolarity (mkDownward f hf) (mkDownward g hg)).toContextPolarity = .upward := by
  simp only [composePolarity, mkDownward, GroundedPolarity.toContextPolarity]


/--
Scalar implicatures require UE context.

In a DE context, the alternatives reverse, so "not all" doesn't follow
from "some". This function captures that constraint.
-/
def implicatureAllowed (gp : GroundedPolarity) : Prop :=
  gp.toContextPolarity = .upward

/--
Implicature is allowed in identity context.
-/
theorem implicature_allowed_identity : implicatureAllowed identityPolarity := by
  simp [implicatureAllowed, identityPolarity, mkUpward, GroundedPolarity.toContextPolarity]

/--
Implicature is blocked under single negation.
-/
theorem implicature_blocked_negation : ¬implicatureAllowed negationPolarity := by
  simp [implicatureAllowed, negationPolarity, mkDownward, GroundedPolarity.toContextPolarity]

/--
Implicature is allowed under double negation.

"It's not the case that John didn't eat some of the cookies"
→ Can derive "not all" implicature because double DE = UE!
-/
theorem implicature_allowed_double_negation :
    implicatureAllowed (composePolarity negationPolarity negationPolarity) := by
  simp [implicatureAllowed, composePolarity, negationPolarity, mkDownward,
        GroundedPolarity.toContextPolarity]

end Montague.Core.Polarity
