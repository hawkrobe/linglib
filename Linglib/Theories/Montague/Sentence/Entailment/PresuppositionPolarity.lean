/-
# Presupposition Projection and Polarity

Connects presupposition projection to the existing polarity infrastructure.

## Key Insight

Context polarity (upward/downward entailing) affects presupposition projection:
- In UE contexts: presuppositions project normally
- In DE contexts: presuppositions may be filtered differently

This parallels how polarity affects scalar implicature:
- UE contexts: stronger alternatives matter (some → not all)
- DE contexts: weaker alternatives matter (polarity reversal)

## Connection to Local Contexts (Schlenker 2009)

Local context theory unifies presupposition projection and implicature:
- Both depend on the "local context" at the embedded position
- Local context is defined by polarity composition
- This module makes that connection explicit via GroundedPolarity

## References

- Schlenker (2009). Local contexts. Semantics & Pragmatics 2:3.
- Heim (1983). On the projection problem for presuppositions.
- Chierchia & McConnell-Ginet (2000). Meaning and Grammar, Ch. 6.
-/

import Linglib.Core.Presupposition
import Linglib.Core.Proposition
import Linglib.Theories.Montague.Core.Polarity

namespace Montague.Sentence.Entailment.PresuppositionPolarity

open Core.Presupposition
open Montague.Core.Polarity
open Core.Proposition (BProp)
open Montague.Core.Polarity

variable {W : Type*}

-- ============================================================================
-- PART 1: Presupposition Projection in Polarized Contexts
-- ============================================================================

/--
The projected presupposition at a given polarity context.

In the simplest case, presupposition projection is polarity-independent:
the presupposition of "not P" is the same as the presupposition of "P".
This function captures that basic behavior.

More complex interactions (e.g., presupposition strengthening under
negation) would require extending this.
-/
def presupProjectsAt (_ctx : ContextPolarity) (p : PrProp W) : BProp W :=
  p.presup

/--
Check if a presupposition is satisfied in a context.

A presupposition is satisfied at world w if it holds at w.
-/
def presupSatisfiedAt (p : PrProp W) (w : W) : Prop :=
  p.presup w = true

-- ============================================================================
-- PART 2: Filtering and Polarity
-- ============================================================================

/--
**Key Theorem**: Filtering is independent of assertion polarity.

When computing presupposition projection for filtering connectives,
the presupposition formula (p.presup && (!p.assertion || q.presup))
doesn't depend on whether we're in a UE or DE context.

The polarity-dependence enters only in which *alternatives* we consider
for exhaustification, not in the projection algorithm itself.
-/
theorem impFilter_presup_polarity_independent (p q : PrProp W) :
    presupProjectsAt .upward (PrProp.impFilter p q) =
    presupProjectsAt .downward (PrProp.impFilter p q) := rfl

/--
Negation preserves presupposition regardless of polarity.
-/
theorem neg_presup_polarity_independent (p : PrProp W) :
    presupProjectsAt .upward (PrProp.neg p) =
    presupProjectsAt .downward (PrProp.neg p) := rfl

-- ============================================================================
-- PART 3: Connection to GroundedPolarity
-- ============================================================================

/--
A presupposition projection context tracks both:
1. The polarity (UE/DE) for implicature computation
2. The accumulated presupposition projection
-/
structure PresupContext (W : Type*) where
  /-- The semantic context function (for computing entailments) -/
  context : Prop' -> Prop'
  /-- Whether the context is UE or DE -/
  polarity : ContextPolarity
  /-- The presupposition accumulated from outer operators -/
  accumulatedPresup : BProp W

/--
Compose two presupposition contexts.

When composing contexts (e.g., "not (if P then Q)"), we compose:
1. The semantic context functions
2. The polarities (using composition rules: DE ∘ DE = UE, etc.)
3. The accumulated presuppositions (conjunction)
-/
def composePresupContext (outer inner : PresupContext W) : PresupContext W :=
  { context := outer.context ∘ inner.context
  , polarity := match outer.polarity, inner.polarity with
      | .upward, .upward => .upward
      | .upward, .downward => .downward
      | .downward, .upward => .downward
      | .downward, .downward => .upward  -- Key: DE ∘ DE = UE!
      | .nonMonotonic, _ => .nonMonotonic
      | _, .nonMonotonic => .nonMonotonic
  , accumulatedPresup := fun w => outer.accumulatedPresup w && inner.accumulatedPresup w
  }

/--
The identity presupposition context.
-/
def identityPresupContext : PresupContext W :=
  { context := id
  , polarity := .upward
  , accumulatedPresup := fun _ => true
  }

/--
Negation context: flips polarity, preserves presupposition.
-/
def negationPresupContext : PresupContext W :=
  { context := pnot
  , polarity := .downward
  , accumulatedPresup := fun _ => true
  }

-- ============================================================================
-- PART 4: Presupposition Under Quantifiers
-- ============================================================================

/--
Presupposition projection behavior varies by quantifier.

Following Heim (1983):
- Universal: "Every F is G" presupposes every F satisfies G's presup
- Existential: "Some F is G" presupposes some F satisfies G's presup (or: at least one F exists)

This is a placeholder for more sophisticated treatment.
-/
inductive QuantifierProjection where
  | universal   -- presup projects universally
  | existential -- presup projects existentially
  | none        -- no projection (presupposition failure)
  deriving DecidableEq, Repr

-- ============================================================================
-- PART 5: Summary
-- ============================================================================

/-
## What This Module Provides

### Basic Functions
- `presupProjectsAt`: Get projected presupposition at a polarity
- `presupSatisfiedAt`: Check if presupposition holds

### Context Composition
- `PresupContext`: Tracks polarity + accumulated presupposition
- `composePresupContext`: Compose contexts
- `identityPresupContext`, `negationPresupContext`: Basic contexts

### Key Theorems
- `impFilter_presup_polarity_independent`: Filtering doesn't depend on polarity
- `neg_presup_polarity_independent`: Negation preserves presupposition

### Connection to Other Modules
- Uses `ContextPolarity` from `Core.Polarity`
- Uses `Prop'`, `pnot` from `Entailment.Polarity`
- Uses `PrProp` from `Core.Presupposition`
- Parallels `GroundedPolarity` for presupposition contexts
-/

end Montague.Sentence.Entailment.PresuppositionPolarity
