/-
# Bilateral Update Semantics (Elliott 2023; Elliott & Sudo 2025)

Bilateral Update Semantics (BUS) is a dynamic semantic framework where
sentences have TWO update dimensions:
- **Positive update** s[φ]⁺: what to retain when asserting φ
- **Negative update** s[φ]⁻: what to retain when denying φ

## Motivation

Standard dynamic semantics struggles with:
1. Double Negation Elimination (DNE): ¬¬φ should entail φ
2. Cross-disjunct anaphora in Free Choice contexts
3. Donkey disjunctions: "Either there's no bathroom, or it's upstairs"

BUS solves these by tracking positive and negative updates separately.

## Key Properties

- **DNE**: ¬¬φ ⊨ φ (negation swaps positive and negative)
- **de Morgan**: ¬(φ ∨ ψ) ⟺ ¬φ ∧ ¬ψ (valid, unlike standard DS)
- **Egli's theorem**: ∃xφ ∧ ψ ⊨ ∃x[φ ∧ ψ]
- **LNC failure**: φ ∧ ¬φ can be satisfiable (mixed scenarios)
- **Modified FC**: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)

## Logical Foundation

The connectives are derived from Strong Kleene three-valued logic:
- Positive update = union of verification paths (+ cells)
- Negative update = union of falsification paths (- cells)
- Presupposition failure = neither verified nor falsified (? cells)

## Architecture

This module re-exports the core bilateral infrastructure from
`Theories.DynamicSemantics.Core.Bilateral` and adds BUS-specific
extensions. `FreeChoice.lean` applies BUS to derive Free Choice
inferences with anaphora.

## References

- Elliott, P. (2023). Donkey disjunctions and overlapping updates. SALT 33: 666-685.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. Semantics & Pragmatics 18.
- Krahmer, E. & Muskens, R. (1995). Negation and disjunction in DRT.
- Champollion, L., Bumford, D. & Henderson, R. (2019). Donkeys under discussion. S&P 12.
-/

import Linglib.Theories.DynamicSemantics.Core.Bilateral

namespace Theories.DynamicSemantics.BUS

open Theories.DynamicSemantics.Core

-- Re-export core bilateral types
export BilateralDen (atom neg conj disj exists_ existsFull forall_ pred1 pred2
  supports entails toPair ofPair toUnilateral)

-- ============================================================================
-- PART 1: BUS-Specific Extensions
-- ============================================================================

/--
BUS denotation is a bilateral denotation specialized for a particular
world and entity type.

This is just a type alias making the BUS usage clear.
-/
abbrev BUSDen (W : Type*) (E : Type*) := BilateralDen W E

namespace BUSDen

variable {W E : Type*}

/--
The truth-value gap (presupposition failure).

In BUS, some sentences may have presuppositions that aren't met in certain
contexts. The gap represents this third possibility beyond truth and falsity.
-/
def hasGap (φ : BUSDen W E) (s : InfoState W E) : Prop :=
  φ.positive s ∪ φ.negative s ⊂ s

/--
Sentence is defined (no presupposition failure).
-/
def defined (φ : BUSDen W E) (s : InfoState W E) : Prop :=
  φ.positive s ∪ φ.negative s = s

-- ============================================================================
-- PART 2: BUS-specific Connectives
-- ============================================================================

/--
Strong Kleene conjunction in BUS.

The standard conjunction already follows Strong Kleene for the positive
dimension (sequencing). This makes it explicit.
-/
def skConj (φ ψ : BUSDen W E) : BUSDen W E := BilateralDen.conj φ ψ

/--
Presupposition-preserving conjunction.

In some contexts, we want conjunction that preserves presupposition gaps
rather than treating them as falsity.
-/
def pConj (φ ψ : BUSDen W E) : BUSDen W E :=
  { positive := fun s => ψ.positive (φ.positive s)
  , negative := fun s =>
      -- Gap from φ is preserved, plus cases where φ holds but ψ fails
      φ.negative s ∪ (s \ (φ.positive s ∪ φ.negative s)) ∪
        (φ.positive s ∩ ψ.negative (φ.positive s)) }

-- ============================================================================
-- PART 3: BUS Entailment Relations
-- ============================================================================

/--
Strawson entailment: φ entails ψ if whenever φ is defined and true, ψ is true.

This is a weaker entailment that allows for presupposition failure.
-/
def strawsonEntails (φ ψ : BUSDen W E) : Prop :=
  ∀ s : InfoState W E,
    defined φ s →
    (φ.positive s).consistent →
    (φ.positive s) ⊆ ψ.positive (φ.positive s)

/--
Strong entailment: φ entails ψ with no presupposition failure.
-/
def strongEntails (φ ψ : BUSDen W E) : Prop :=
  ∀ s : InfoState W E,
    (φ.positive s).consistent →
    defined ψ (φ.positive s) ∧
    (φ.positive s) ⊆ ψ.positive (φ.positive s)

-- ============================================================================
-- PART 4: Update Algebra Properties
-- ============================================================================

/--
Negation swaps positive and negative.
-/
theorem neg_positive_eq_negative (φ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.neg φ).positive s = φ.negative s := rfl

theorem neg_negative_eq_positive (φ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.neg φ).negative s = φ.positive s := rfl

/--
De Morgan for disjunction.
-/
theorem de_morgan_disj_negative (φ ψ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.disj φ ψ).negative s = φ.negative s ∩ ψ.negative s := rfl

/--
Conjunction negative is union of failure cases.
-/
theorem conj_negative (φ ψ : BUSDen W E) (s : InfoState W E) :
    (BilateralDen.conj φ ψ).negative s =
    φ.negative s ∪ (φ.positive s ∩ ψ.negative (φ.positive s)) := rfl

end BUSDen

-- ============================================================================
-- PART 5: Backward Compatibility
-- ============================================================================

-- For files that still import the old location
namespace Compat

/-- Alias for backward compatibility with old BilateralUpdateSemantics imports -/
abbrev BilateralDen := Theories.DynamicSemantics.Core.BilateralDen

end Compat

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-!
## What This Module Provides

### Core Type (re-exported)
- `BUSDen W E`: Bilateral denotation = `BilateralDen W E`

### BUS-specific Features
- `hasGap`: Sentence has presupposition failure
- `defined`: Sentence is defined (no gap)
- `pConj`: Presupposition-preserving conjunction
- `strawsonEntails`: Entailment allowing presupposition failure
- `strongEntails`: Entailment requiring no failure

### Re-exported from Core
- `atom`, `neg`, `conj`, `disj`, `exists_`, `forall_`
- `pred1`, `pred2`: Entity predicates
- `supports`, `entails`: Semantic relations

### Key Theorems
- `neg_neg`: DNE (from Core)
- `neg_positive_eq_negative`, `neg_negative_eq_positive`: Negation structure
- `de_morgan_disj_negative`: De Morgan
- `conj_negative`: Conjunction failure cases

## Architecture

This module builds on `Theories.DynamicSemantics.Core.Bilateral`:
- Core provides the `BilateralDen` structure and basic operations
- This module adds BUS-specific concepts (gaps, presuppositions)
- `FreeChoice.lean` applies BUS to derive FC inferences
-/

end Theories.DynamicSemantics.BUS
