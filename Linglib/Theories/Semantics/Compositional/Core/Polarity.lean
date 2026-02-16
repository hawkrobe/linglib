/-
# Grounded Context Polarity

Semantic grounding for `ContextPolarity` (defined in `Core.NaturalLogic`)
via Mathlib's `Monotone`/`Antitone` infrastructure.

## Contents

1. Re-export of `ContextPolarity` from `Core.NaturalLogic`
2. IsUpwardEntailing/IsDownwardEntailing - Mathlib-based formal definitions
3. Decidable test functions - For verification on finite models
4. GroundedPolarity - Context + polarity + proof
5. Monotonicity theorems - Negation, conditionals, quantifiers

## Integration with Mathlib

We use Mathlib's order-theoretic infrastructure:
- `Monotone f` (from `Mathlib.Order.Monotone.Basic`): `∀ a b, a ≤ b → f a ≤ f b`
- `Antitone f`: `∀ a b, a ≤ b → f b ≤ f a`

For `BProp World = World → Bool`, the ordering is pointwise: `p ≤ q ↔ ∀ w, p w ≤ q w`
where for `Bool`, `false ≤ true`.

Mathlib provides composition lemmas for free:
- `Monotone.comp`: UE ∘ UE = UE
- `Antitone.comp_antitone`: DE ∘ DE = UE (the "double negation" rule!)
- `Monotone.comp_antitone`: UE ∘ DE = DE
- `Antitone.comp`: DE ∘ UE = DE

The polarity composition rules are a homomorphic image of the
`EntailmentSig` monoid — see `EntailmentSig.toContextPolarity_compose`.

## References

- van Benthem (1986). Essays in Logical Semantics.
- Ladusaw (1980). Polarity Sensitivity as Inherent Scope Relations.
- Barwise & Cooper (1981). Generalized Quantifiers and Natural Language.
-/

import Mathlib.Order.Monotone.Defs
import Linglib.Core.NaturalLogic
import Linglib.Theories.Semantics.Entailment.Basic

namespace TruthConditional.Core.Polarity

-- Re-export ContextPolarity so downstream `open TruthConditional.Core.Polarity (ContextPolarity)` works
export Core.NaturalLogic (ContextPolarity)

open TruthConditional.Sentence.Entailment


/-
For BProp World = World → Bool, we have:
- BooleanAlgebra (World → Bool) via Pi.instBooleanAlgebra + Bool.instBooleanAlgebraBool
- This gives us a lattice ordering: p ≤ q ↔ ∀ w, p w → q w (when lifted from Bool)

We use Mathlib's Monotone/Antitone as the canonical definitions.
-/

/--
IsUpwardEntailing is an abbreviation for `Monotone`.

A context function `f : BProp World → BProp World` is upward entailing if
it preserves the ordering: If p ≤ q, then f(p) ≤ f(q).

Examples: "some", "or", scope of "every"
-/
abbrev IsUpwardEntailing (f : BProp World → BProp World) := Monotone f

/--
IsDownwardEntailing is an abbreviation for `Antitone`.

A context function `f : BProp World → BProp World` is downward entailing if
it reverses the ordering: If p ≤ q, then f(q) ≤ f(p).

Examples: "no", "not", restrictor of "every"
-/
abbrev IsDownwardEntailing (f : BProp World → BProp World) := Antitone f

-- Shorthand aliases for readability
abbrev IsUE := IsUpwardEntailing
abbrev IsDE := IsDownwardEntailing


/--
Identity is UE: The trivial context preserves entailment.
-/
theorem id_isUpwardEntailing : IsUpwardEntailing (id : BProp World → BProp World) :=
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
theorem ue_comp_ue {f g : BProp World → BProp World} (hf : IsUpwardEntailing f) (hg : IsUpwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- DE ∘ DE = UE (double negation). -/
theorem de_comp_de {f g : BProp World → BProp World} (hf : IsDownwardEntailing f) (hg : IsDownwardEntailing g) :
    IsUpwardEntailing (f ∘ g) :=
  hf.comp hg

/-- UE ∘ DE = DE (from Mathlib) -/
theorem ue_comp_de {f g : BProp World → BProp World} (hf : IsUpwardEntailing f) (hg : IsDownwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_antitone hg

/-- DE ∘ UE = DE (from Mathlib) -/
theorem de_comp_ue {f g : BProp World → BProp World} (hf : IsDownwardEntailing f) (hg : IsUpwardEntailing g) :
    IsDownwardEntailing (f ∘ g) :=
  hf.comp_monotone hg


/--
Check if f is upward entailing on given test cases.

This is a decidable approximation: it checks the property on a finite
set of test cases rather than proving it universally.
-/
def isUpwardEntailing (f : BProp World → BProp World) (tests : List (BProp World × BProp World)) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f p) (f q)

/--
Check if f is downward entailing on given test cases.

This is a decidable approximation: it checks the property on a finite
set of test cases rather than proving it universally.
-/
def isDownwardEntailing (f : BProp World → BProp World) (tests : List (BProp World × BProp World)) : Bool :=
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
def materialCond (c : BProp World) : BProp World → BProp World :=
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
  context : BProp World → BProp World
  /-- Proof of monotonicity (UE) -/
  witness : Monotone context

/--
A grounded DE polarity carries proof that a context function is antitone.
-/
structure GroundedDE where
  /-- The context function -/
  context : BProp World → BProp World
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
def mkUpward (ctx : BProp World → BProp World) (h : Monotone ctx) : GroundedPolarity :=
  .ue ⟨ctx, h⟩

/--
Create a grounded DE polarity from a proof.
-/
def mkDownward (ctx : BProp World → BProp World) (h : Antitone ctx) : GroundedPolarity :=
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
Compose two grounded polarities, with proof that the composition has the
right property.

The case analysis mirrors `ContextPolarity.compose` (which is derived from the
`EntailmentSig` monoid), but additionally carries Mathlib proof witnesses:
- UE ∘ UE = UE via `Monotone.comp`
- DE ∘ DE = UE via `Antitone.comp_antitone` (double negation!)
- UE ∘ DE = DE via `Monotone.comp_antitone`
- DE ∘ UE = DE via `Antitone.comp_monotone`
-/
def composePolarity (outer inner : GroundedPolarity) : GroundedPolarity :=
  match outer, inner with
  | .ue ⟨f, hf⟩, .ue ⟨g, hg⟩ => .ue ⟨f ∘ g, ue_comp_ue hf hg⟩
  | .ue ⟨f, hf⟩, .de ⟨g, hg⟩ => .de ⟨f ∘ g, ue_comp_de hf hg⟩
  | .de ⟨f, hf⟩, .ue ⟨g, hg⟩ => .de ⟨f ∘ g, de_comp_ue hf hg⟩
  | .de ⟨f, hf⟩, .de ⟨g, hg⟩ => .ue ⟨f ∘ g, de_comp_de hf hg⟩

/--
Grounded polarity composition agrees with `ContextPolarity.compose`.

This connects the proof-carrying system to the algebraic system:
the Mathlib composition lemmas produce the same polarity classification
as the monoid-derived `ContextPolarity.compose`.
-/
theorem composePolarity_agrees (outer inner : GroundedPolarity) :
    (composePolarity outer inner).toContextPolarity =
    outer.toContextPolarity.compose inner.toContextPolarity := by
  cases outer with
  | ue o => cases inner with
    | ue i => rfl
    | de i => rfl
  | de o => cases inner with
    | ue i => rfl
    | de i => rfl

/--
Double DE gives UE (grounded version).

"It's not the case that no one..." creates a UE context.
-/
theorem double_de_is_ue_grounded (f g : BProp World → BProp World) (hf : Antitone f) (hg : Antitone g) :
    (composePolarity (mkDownward f hf) (mkDownward g hg)).toContextPolarity = .upward := by
  rfl


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

end TruthConditional.Core.Polarity
