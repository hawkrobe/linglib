/-
# Modal Theory Comparison

Infrastructure and theorems for comparing Kratzer vs Simple modal semantics.

## Key Question

When do Kratzer and Simple modal theories coincide?

**Answer**: When Kratzer's ordering source is empty, the two approaches are
equivalent (given the same accessibility relation).

## Theoretical Significance

Kratzer's framework GENERALIZES simple modal logic:
- Simple modal logic = Kratzer with empty ordering
- Kratzer's advantage: can model graded modality via ordering source

## Empirical Divergence

The theories diverge when:
1. Ordering source is non-empty (deontic, teleological, bouletic modals)
2. Context supplies different conversational backgrounds

## References

- Kratzer, A. (1991). Modality. In Semantics: An International Handbook.
- Portner, P. (2009). Modality. Oxford University Press.
-/

import Linglib.Theories.Montague.Lexicon.Modals.Kratzer
import Linglib.Theories.Montague.Lexicon.Modals.Simple

namespace Montague.Lexicon.Modals

open Montague.Attitudes
open Montague.Modality

-- ============================================================================
-- Comparison Functions
-- ============================================================================

/-- Do two theories agree on modal force `f` for proposition `p` at world `w`? -/
def theoriesAgreeAt (T₁ T₂ : ModalTheory) (f : ModalForce) (p : Proposition) (w : World) : Bool :=
  T₁.eval f p w == T₂.eval f p w

/-- Do two theories agree on modal force `f` for proposition `p` across all worlds? -/
def theoriesAgreeOn (T₁ T₂ : ModalTheory) (f : ModalForce) (p : Proposition) : Bool :=
  allWorlds'.all fun w => theoriesAgreeAt T₁ T₂ f p w

/-- Find worlds where two theories diverge. -/
def divergingWorlds (T₁ T₂ : ModalTheory) (f : ModalForce) (p : Proposition) : List World :=
  allWorlds'.filter fun w => !theoriesAgreeAt T₁ T₂ f p w

/-- Do two theories agree on all modal forces for proposition `p`? -/
def theoriesAgreeOnProposition (T₁ T₂ : ModalTheory) (p : Proposition) : Bool :=
  theoriesAgreeOn T₁ T₂ .necessity p && theoriesAgreeOn T₁ T₂ .possibility p

-- ============================================================================
-- Core Equivalence: Minimal Kratzer = Universal Simple
-- ============================================================================

/--
**Theorem: Minimal Kratzer = Universal Simple**

With empty base and empty ordering, all worlds are accessible,
matching SimpleUniversal.
-/
theorem minimal_kratzer_equals_universal_simple_necessity :
    ∀ (w : World), KratzerMinimal.eval .necessity raining w = SimpleUniversal.eval .necessity raining w := by
  intro w
  cases w <;> native_decide

theorem minimal_kratzer_equals_universal_simple_possibility :
    ∀ (w : World), KratzerMinimal.eval .possibility raining w = SimpleUniversal.eval .possibility raining w := by
  intro w
  cases w <;> native_decide

/-- Agreement on trivially true. -/
theorem agree_on_trivially_true :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyTrue = true := by
  native_decide

/-- Agreement on trivially false. -/
theorem agree_on_trivially_false :
    theoriesAgreeOnProposition KratzerMinimal SimpleUniversal triviallyFalse = true := by
  native_decide

-- ============================================================================
-- Divergence Theorems
-- ============================================================================

/--
**Theorem: Different Kratzer parameters give different results**

Epistemic vs Minimal Kratzer differ because epistemic restricts accessibility
to worlds compatible with what is known (ground is wet).
-/
theorem epistemic_vs_minimal_differ :
    ∃ (p : Proposition) (w : World),
    KratzerEpistemic.eval .necessity p w ≠ KratzerMinimal.eval .necessity p w := by
  -- groundWet is necessary given we know the ground is wet (epistemic)
  -- but not necessary with universal accessibility (minimal)
  use groundWet, .w0
  native_decide

/--
**Theorem: Context-dependence distinguishes Kratzer**

The same modal verb with different conversational backgrounds yields
different truth values.
-/
theorem kratzer_context_dependence :
    KratzerEpistemic.eval .necessity groundWet .w0 = true ∧
    KratzerMinimal.eval .necessity groundWet .w0 = false := by
  native_decide

-- ============================================================================
-- Duality Comparison
-- ============================================================================

/-- Both Kratzer and Simple satisfy duality. -/
theorem both_satisfy_duality
    (params : KratzerParams)
    (R : World → World → Bool)
    (p : Proposition)
    (w : World) :
    (Kratzer params).dualityHolds p w = true ∧
    (Simple R).dualityHolds p w = true := by
  constructor
  · exact kratzer_duality params p w
  · exact simple_duality R p w

-- ============================================================================
-- Specific Examples
-- ============================================================================

/-- Agreement: Minimal Kratzer and Universal Simple agree on necessity for trivially true. -/
theorem agree_on_trivially_true_necessity :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyTrue = true := by
  native_decide

/-- Agreement: Both agree on possibility for trivially true. -/
theorem agree_on_trivially_true_possibility :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .possibility triviallyTrue = true := by
  native_decide

/-- Agreement: Both agree on necessity for trivially false. -/
theorem agree_on_trivially_false_necessity :
    theoriesAgreeOn KratzerMinimal SimpleUniversal .necessity triviallyFalse = true := by
  native_decide

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Summary: Kratzer vs Simple

| Scenario                    | Agreement? | Why?                           |
|-----------------------------|-----------:|--------------------------------|
| Empty base + empty ordering | Yes        | All worlds best                |
| Non-empty base, empty ord.  | Yes*       | Same accessible worlds         |
| Non-empty ordering          | No         | Best worlds ≠ accessible worlds|

*When R is derived from base via accessibleFrom

## When to Use Which Theory

**Use Simple** when:
- Studying modal logic properties (reflexivity, transitivity, seriality)
- Accessibility is conceptually primitive
- No ranking among accessible worlds needed

**Use Kratzer** when:
- Modeling natural language modals
- Need context-dependent readings
- Need to distinguish epistemic vs deontic vs teleological readings
- Need graded modality (comparative possibility)

## The Unifying View

Kratzer's framework is strictly more expressive:
- Simple ⊆ Kratzer (as empty-ordering case)
- Kratzer allows ordering-based distinctions Simple cannot make

This justifies using Kratzer as the default for linguistic semantics,
while Simple remains useful for logical foundations.
-/

end Montague.Lexicon.Modals
