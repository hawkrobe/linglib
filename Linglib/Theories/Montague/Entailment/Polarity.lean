/-
# Grounded Context Polarity

This module connects `ContextPolarity` to proven monotonicity properties,
following the Mathlib pattern of typeclasses with instances.

## The Problem (Before)

Previously, `ContextPolarity` was just asserted via keyword heuristics:
```
def determinePolarityFromWords (ws : List Word) : ContextPolarity :=
  if ws.any (λ w => w.form == "no") then .downward else .upward
```

This is unsound - it doesn't actually prove the context is DE/UE!

## The Solution (This Module)

We define typeclasses `IsUpwardEntailing` and `IsDownwardEntailing` that
carry semantic proofs. Then:

1. Prove instances for specific operators (negation, quantifiers, etc.)
2. Prove composition rules (DE ∘ DE = UE, etc.)
3. Derive `ContextPolarity` from the proven properties

This follows the Mathlib pattern: properties are typeclasses, specific
constructions prove they satisfy the property, and functions that need
the property take it as a constraint.

## References

- van Benthem (1986). Essays in Logical Semantics.
- Ladusaw (1980). Polarity Sensitivity as Inherent Scope Relations.
- Barwise & Cooper (1981). Generalized Quantifiers and Natural Language.
-/

import Linglib.Theories.Montague.Entailment.Basic
import Linglib.Theories.Montague.Derivation.Basic

namespace Montague.Entailment.Polarity

open Montague.Entailment
open Montague.Derivation (ContextPolarity)

-- ============================================================================
-- PART 1: Monotonicity as Typeclasses
-- ============================================================================

-- Note: Prop' = World → Bool, so we work with Bool-valued functions.
-- We use entails from Basic.lean for the decidable version.

/--
A context function `f : Prop' → Prop'` is **upward entailing** if
it preserves entailment direction.

If P ⊆ Q, then f(P) ⊆ f(Q).

Examples: "some", "or", scope of "every"
-/
class IsUpwardEntailing (f : Prop' → Prop') : Prop where
  preserves : ∀ p q : Prop', entails p q = true → entails (f p) (f q) = true

/--
A context function `f : Prop' → Prop'` is **downward entailing** if
it reverses entailment direction.

If P ⊆ Q, then f(Q) ⊆ f(P).

Examples: "no", "not", restrictor of "every"
-/
class IsDownwardEntailing (f : Prop' → Prop') : Prop where
  reverses : ∀ p q : Prop', entails p q = true → entails (f q) (f p) = true

-- ============================================================================
-- PART 2: Basic Instances
-- ============================================================================

/--
**Identity is UE**: The trivial context preserves entailment.
-/
instance : IsUpwardEntailing (id : Prop' → Prop') where
  preserves := fun _ _ h => h

/--
**Negation is DE**: If P ⊆ Q, then ¬Q ⊆ ¬P.

Proof: entails p q means ∀w, !p w || q w
       entails (pnot q) (pnot p) means ∀w, q w || !p w
       These are logically equivalent by commutativity of ||
-/
instance instPnotDE : IsDownwardEntailing pnot where
  reverses := fun p q hpq => by
    simp only [entails, pnot, Bool.not_not] at hpq ⊢
    simp only [List.all_eq_true] at hpq ⊢
    intro w hw
    have := hpq w hw
    -- !p w || q w = true, need q w || !p w = true
    cases hp : p w <;> cases hq : q w <;> simp_all

/--
**Double negation is UE**: ¬¬ preserves entailment.
-/
instance : IsUpwardEntailing (pnot ∘ pnot) where
  preserves := fun p q hpq => by
    simp only [entails, Function.comp, pnot, Bool.not_not] at hpq ⊢
    exact hpq

-- ============================================================================
-- PART 3: Composition Rules (The Beautiful Part!)
-- ============================================================================

/--
**UE ∘ UE = UE**: Composing two UE contexts gives UE.
-/
instance instUEComposeUE (f g : Prop' → Prop') [hf : IsUpwardEntailing f] [hg : IsUpwardEntailing g] :
    IsUpwardEntailing (f ∘ g) where
  preserves := fun p q hpq =>
    -- p ⊆ q → g p ⊆ g q (by hg) → f(g p) ⊆ f(g q) (by hf)
    hf.preserves (g p) (g q) (hg.preserves p q hpq)

/--
**DE ∘ DE = UE**: Composing two DE contexts gives UE!

This is the "double negation" principle generalized.
-/
instance instDEComposeDE (f g : Prop' → Prop') [hf : IsDownwardEntailing f] [hg : IsDownwardEntailing g] :
    IsUpwardEntailing (f ∘ g) where
  preserves := fun p q hpq =>
    -- p ⊆ q → g q ⊆ g p (by hg, reversed!) → f(g p) ⊆ f(g q) (by hf, reversed again!)
    hf.reverses (g q) (g p) (hg.reverses p q hpq)

/--
**UE ∘ DE = DE**: UE on top of DE gives DE.
-/
instance instUEComposeDE (f g : Prop' → Prop') [hf : IsUpwardEntailing f] [hg : IsDownwardEntailing g] :
    IsDownwardEntailing (f ∘ g) where
  reverses := fun p q hpq =>
    -- p ⊆ q → g q ⊆ g p (by hg) → f(g q) ⊆ f(g p) (by hf, preserves this!)
    hf.preserves (g q) (g p) (hg.reverses p q hpq)

/--
**DE ∘ UE = DE**: DE on top of UE gives DE.
-/
instance instDEComposeUE (f g : Prop' → Prop') [hf : IsDownwardEntailing f] [hg : IsUpwardEntailing g] :
    IsDownwardEntailing (f ∘ g) where
  reverses := fun p q hpq =>
    -- p ⊆ q → g p ⊆ g q (by hg) → f(g q) ⊆ f(g p) (by hf, reverses!)
    hf.reverses (g p) (g q) (hg.preserves p q hpq)

-- ============================================================================
-- PART 4: Extracting ContextPolarity from Proofs
-- ============================================================================

/--
A **grounded UE polarity** carries proof that a context function is UE.
-/
structure GroundedUE where
  /-- The context function -/
  context : Prop' → Prop'
  /-- Proof of UE -/
  witness : IsUpwardEntailing context

/--
A **grounded DE polarity** carries proof that a context function is DE.
-/
structure GroundedDE where
  /-- The context function -/
  context : Prop' → Prop'
  /-- Proof of DE -/
  witness : IsDownwardEntailing context

/--
A **grounded polarity** is either UE or DE, with proof.
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
def mkUpward (ctx : Prop' → Prop') [h : IsUpwardEntailing ctx] : GroundedPolarity :=
  .ue ⟨ctx, h⟩

/--
Create a grounded DE polarity from a proof.
-/
def mkDownward (ctx : Prop' → Prop') [h : IsDownwardEntailing ctx] : GroundedPolarity :=
  .de ⟨ctx, h⟩

/--
The identity context is grounded UE.
-/
def identityPolarity : GroundedPolarity := mkUpward id

/--
Negation is grounded DE.
-/
def negationPolarity : GroundedPolarity := mkDownward pnot

-- ============================================================================
-- PART 5: Compositional Polarity Computation
-- ============================================================================

/--
Compose two polarities, with proof that the composition has the right property.

This is the key function for compositional polarity tracking through
derivation trees.
-/
def composePolarity (outer inner : GroundedPolarity) : GroundedPolarity :=
  match outer, inner with
  | .ue ⟨f, hf⟩, .ue ⟨g, hg⟩ =>
    -- UE ∘ UE = UE
    .ue ⟨f ∘ g, @instUEComposeUE f g hf hg⟩
  | .ue ⟨f, hf⟩, .de ⟨g, hg⟩ =>
    -- UE ∘ DE = DE
    .de ⟨f ∘ g, @instUEComposeDE f g hf hg⟩
  | .de ⟨f, hf⟩, .ue ⟨g, hg⟩ =>
    -- DE ∘ UE = DE
    .de ⟨f ∘ g, @instDEComposeUE f g hf hg⟩
  | .de ⟨f, hf⟩, .de ⟨g, hg⟩ =>
    -- DE ∘ DE = UE (double negation!)
    .ue ⟨f ∘ g, @instDEComposeDE f g hf hg⟩

-- ============================================================================
-- PART 6: Polarity Composition Table (Verified)
-- ============================================================================

/--
**Theorem: Polarity composition table is correct.**

| Outer | Inner | Result |
|-------|-------|--------|
| UE    | UE    | UE     |
| UE    | DE    | DE     |
| DE    | UE    | DE     |
| DE    | DE    | UE     |

This is provable because `composePolarity` uses the instance proofs.
-/
theorem polarity_composition_table :
    (composePolarity (mkUpward id) (mkUpward id)).toContextPolarity = .upward ∧
    (composePolarity (mkUpward id) (mkDownward pnot)).toContextPolarity = .downward ∧
    (composePolarity (mkDownward pnot) (mkUpward id)).toContextPolarity = .downward ∧
    (composePolarity (mkDownward pnot) (mkDownward pnot)).toContextPolarity = .upward := by
  simp only [composePolarity, mkUpward, mkDownward, GroundedPolarity.toContextPolarity, and_self]

/--
**Theorem: Double DE gives UE.**

This captures the linguistic insight: "It's not the case that no one..."
creates a UE context for the embedded scalar item.
-/
theorem double_de_is_ue (f g : Prop' → Prop') [hf : IsDownwardEntailing f] [hg : IsDownwardEntailing g] :
    (composePolarity (mkDownward f) (mkDownward g)).toContextPolarity = .upward := by
  simp only [composePolarity, mkDownward, GroundedPolarity.toContextPolarity]

-- ============================================================================
-- PART 7: Quantifier Instances
-- ============================================================================

-- For full implementation, we'd define quantifier contexts and prove their
-- monotonicity. See Montague.Entailment.Monotonicity for the actual instances
-- with proven theorems (no_scope_DE, every_scope_UE, etc.).

-- ============================================================================
-- PART 8: Connection to Implicature Derivation
-- ============================================================================

/--
**Key Insight**: Scalar implicatures require UE context.

In a DE context, the alternatives reverse, so "not all" doesn't follow
from "some". This function captures that constraint.
-/
def implicatureAllowed (gp : GroundedPolarity) : Prop :=
  gp.toContextPolarity = .upward

/--
**Theorem**: Implicature is allowed in identity context.
-/
theorem implicature_allowed_identity : implicatureAllowed identityPolarity := by
  simp [implicatureAllowed, identityPolarity, mkUpward, GroundedPolarity.toContextPolarity]

/--
**Theorem**: Implicature is blocked under single negation.
-/
theorem implicature_blocked_negation : ¬implicatureAllowed negationPolarity := by
  simp [implicatureAllowed, negationPolarity, mkDownward, GroundedPolarity.toContextPolarity]

/--
**Theorem**: Implicature is allowed under double negation.

"It's not the case that John didn't eat some of the cookies"
→ Can derive "not all" implicature because double DE = UE!
-/
theorem implicature_allowed_double_negation :
    implicatureAllowed (composePolarity negationPolarity negationPolarity) := by
  simp [implicatureAllowed, composePolarity, negationPolarity, mkDownward, GroundedPolarity.toContextPolarity]

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Typeclasses (Mathlib Pattern)
- `IsUpwardEntailing f`: Proof that f preserves entailment
- `IsDownwardEntailing f`: Proof that f reverses entailment

### Basic Instances
- `instance : IsUpwardEntailing id`
- `instance : IsDownwardEntailing pnot`
- `instance : IsUpwardEntailing (pnot ∘ pnot)`

### Composition Instances (The Key!)
- `instUEComposeUE`: UE ∘ UE = UE
- `instDEComposeDE`: DE ∘ DE = UE  (double negation!)
- `instUEComposeDE`: UE ∘ DE = DE
- `instDEComposeUE`: DE ∘ UE = DE

### Grounded Polarity
- `GroundedPolarity`: Context + polarity + proof
- `composePolarity`: Compositional polarity with proof
- `implicatureAllowed`: UE contexts allow implicature

### Verified Properties
- `polarity_composition_table`: The 2×2 table is correct
- `double_de_is_ue`: Double negation gives UE
- `implicature_allowed_double_negation`: SI under ¬¬ is OK

## Connection to Other Modules

This module bridges:
- `Monotonicity.lean`: Test-based monotonicity checking
- `ContextPolarity`: The enum used throughout NeoGricean/
- `FoxSpector2018.lean`: Economy condition uses polarity
- `PottsLU.lean`: LU model's DE/UE predictions

Now `ContextPolarity` can be DERIVED from semantic proofs, not just asserted!
-/

end Montague.Entailment.Polarity
