/-
# Grounded Context Polarity

This module connects `ContextPolarity` to proven monotonicity properties,
using Mathlib's `Monotone`/`Antitone` typeclasses.

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
import Linglib.Theories.Montague.Entailment.Basic
import Linglib.Theories.Montague.Derivation.Basic

namespace Montague.Entailment.Polarity

open Montague.Entailment
open Montague.Derivation (ContextPolarity)

-- ============================================================================
-- PART 1: Monotonicity via Mathlib
-- ============================================================================

/-
For Prop' = World → Bool, we have:
- BooleanAlgebra (World → Bool) via Pi.instBooleanAlgebra + Bool.instBooleanAlgebraBool
- This gives us a lattice ordering: p ≤ q ↔ ∀ w, p w → q w (when lifted from Bool)

We use Mathlib's Monotone/Antitone as the canonical definitions.
-/

/--
**IsUpwardEntailing** is an abbreviation for `Monotone`.

A context function `f : Prop' → Prop'` is upward entailing if
it preserves the ordering: If p ≤ q, then f(p) ≤ f(q).

Examples: "some", "or", scope of "every"
-/
abbrev IsUpwardEntailing (f : Prop' → Prop') := Monotone f

/--
**IsDownwardEntailing** is an abbreviation for `Antitone`.

A context function `f : Prop' → Prop'` is downward entailing if
it reverses the ordering: If p ≤ q, then f(q) ≤ f(p).

Examples: "no", "not", restrictor of "every"
-/
abbrev IsDownwardEntailing (f : Prop' → Prop') := Antitone f

-- ============================================================================
-- PART 2: Basic Instances
-- ============================================================================

/--
**Identity is UE**: The trivial context preserves entailment.
-/
theorem id_isUpwardEntailing : IsUpwardEntailing (id : Prop' → Prop') :=
  monotone_id

/--
**Negation is DE**: If P ⊆ Q, then ¬Q ⊆ ¬P.

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
**Double negation is UE**: ¬¬ preserves entailment.

This follows from Mathlib's `Antitone.comp` (DE ∘ DE = UE).
-/
theorem pnot_pnot_isUpwardEntailing : IsUpwardEntailing (pnot ∘ pnot) :=
  pnot_isDownwardEntailing.comp pnot_isDownwardEntailing

-- ============================================================================
-- PART 3: Composition Rules (From Mathlib - Free!)
-- ============================================================================

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

-- ============================================================================
-- PART 4: Extracting ContextPolarity from Proofs
-- ============================================================================

/--
A **grounded UE polarity** carries proof that a context function is monotone.
-/
structure GroundedUE where
  /-- The context function -/
  context : Prop' → Prop'
  /-- Proof of monotonicity (UE) -/
  witness : Monotone context

/--
A **grounded DE polarity** carries proof that a context function is antitone.
-/
structure GroundedDE where
  /-- The context function -/
  context : Prop' → Prop'
  /-- Proof of antitonicity (DE) -/
  witness : Antitone context

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
**Theorem: Double DE gives UE.**

This captures the linguistic insight: "It's not the case that no one..."
creates a UE context for the embedded scalar item.
-/
theorem double_de_is_ue (f g : Prop' → Prop') (hf : Antitone f) (hg : Antitone g) :
    (composePolarity (mkDownward f hf) (mkDownward g hg)).toContextPolarity = .upward := by
  simp only [composePolarity, mkDownward, GroundedPolarity.toContextPolarity]

-- ============================================================================
-- PART 7: Connection to Implicature Derivation
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
  simp [implicatureAllowed, composePolarity, negationPolarity, mkDownward,
        GroundedPolarity.toContextPolarity]

-- ============================================================================
-- PART 8: Decidable Checking (for compatibility)
-- ============================================================================

/--
Decidable check for upward entailment on test cases.

This is used by Monotonicity.lean for decidable checking.
-/
def checkUpwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f p) (f q)

/--
Decidable check for downward entailment on test cases.

This is used by Monotonicity.lean for decidable checking.
-/
def checkDownwardEntailing (f : Prop' → Prop') (tests : List (Prop' × Prop')) : Bool :=
  tests.all λ (p, q) => !entails p q || entails (f q) (f p)

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Using Mathlib's Monotone/Antitone
- `IsUpwardEntailing f` := `Monotone f` (preserves ordering)
- `IsDownwardEntailing f` := `Antitone f` (reverses ordering)

### Basic Proofs
- `id_isUpwardEntailing` : Identity is monotone
- `pnot_isDownwardEntailing` : Negation is antitone
- `pnot_pnot_isUpwardEntailing` : Double negation is monotone

### Composition Rules (From Mathlib)
- `ue_comp_ue` : UE ∘ UE = UE (`Monotone.comp`)
- `de_comp_de` : DE ∘ DE = UE (`Antitone.comp_antitone`)
- `ue_comp_de` : UE ∘ DE = DE (`Monotone.comp_antitone`)
- `de_comp_ue` : DE ∘ UE = DE (`Antitone.comp`)

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
- `Monotonicity.lean`: Uses decidable checking for test-based verification
- `ContextPolarity`: The enum used throughout NeoGricean/
- `FoxSpector2018.lean`: Economy condition uses polarity
- `PottsLU.lean`: LU model's DE/UE predictions

Now `ContextPolarity` can be DERIVED from Mathlib's Monotone/Antitone proofs!
-/

end Montague.Entailment.Polarity
