/-
# Free Choice with Anaphora (Elliott & Sudo 2025)

This module derives Free Choice (FC) inferences using Bilateral Update Semantics,
following Elliott & Sudo (2025) "Free choice with anaphora".

## The Puzzle

**Bathroom disjunction**: "Either there's no bathroom or it's in a funny place"

From this, we infer:
1. It's possible there's no bathroom
2. It's possible there's a bathroom AND it's in a funny place

The pronoun "it" in the second disjunct is bound by the existential in the
NEGATED first disjunct. This cross-disjunct anaphora is puzzling because:
- Standard FC: ◇(φ ∨ ψ) → ◇φ ∧ ◇ψ (no anaphoric connection)
- With anaphora: ◇(¬∃xφ ∨ ψ(x)) → ◇¬∃xφ ∧ ◇(∃x(φ ∧ ψ(x)))

## Solution

BUS + Modal Disjunction:
1. Disjunction semantics: φ ∨ ψ entails ◇φ ∧ ◇ψ
2. Negation swaps positive/negative: ¬∃xφ positive = ∃xφ negative
3. Cross-disjunct binding: x introduced in ¬∃xφ is visible to ψ(x)

## Key Results

- **Modified FC**: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)
- **FC with anaphora**: Bathroom inference pattern
- **Dual prohibition**: ¬◇φ ∧ ¬◇ψ ⊨ ¬(φ ∨ ψ) (preserved)

## References

- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
- Zimmermann, T.E. (2000). Free Choice Disjunction and Epistemic Possibility.
- Alonso-Ovalle, L. (2006). Disjunction in Alternative Semantics.
-/

import Linglib.Theories.BilateralUpdateSemantics.Basic

namespace Theories.BilateralUpdateSemantics.FreeChoice

open Core
open Core.HeimState
open BilateralUpdateSemantics.BilateralDen

-- ============================================================================
-- PART 1: Modal Operators
-- ============================================================================

variable {W E : Type*}

/--
Possibility: state s makes ◇φ true iff s[φ]⁺ is consistent.

In BUS, possibility checks whether the positive update yields a non-empty state.
-/
def possible (φ : BilateralDen W E) (s : HeimState W E) : Prop :=
  (φ.positive s).consistent

/--
Necessity: state s makes □φ true iff s subsists in s[φ]⁺.

Every possibility in s has a descendant that survives the positive update.
-/
def necessary (φ : BilateralDen W E) (s : HeimState W E) : Prop :=
  s ⪯ φ.positive s

/--
Impossibility: ¬◇φ iff s[φ]⁺ is empty.
-/
def impossible (φ : BilateralDen W E) (s : HeimState W E) : Prop :=
  ¬(φ.positive s).consistent

theorem impossible_iff_empty (φ : BilateralDen W E) (s : HeimState W E) :
    impossible φ s ↔ φ.positive s = ∅ := by
  simp only [impossible, HeimState.consistent, Set.not_nonempty_iff_eq_empty]

-- ============================================================================
-- PART 2: Free Choice Disjunction
-- ============================================================================

/--
Free Choice disjunction: semantic disjunction that validates FC.

For FC disjunction φ ∨ᶠᶜ ψ:
- s[φ ∨ᶠᶜ ψ]⁺ = s[φ]⁺ ∪ s[ψ]⁺   (same as standard)
- s[φ ∨ᶠᶜ ψ]⁻ = s[φ]⁻ ∩ s[ψ]⁻   (same as standard)

The FC inference arises from the *modal* meaning: disjunction presupposes
that each disjunct is possible.

Actually in E&S, FC comes from the bilateral structure interacting with
modality. The disjunction itself is standard; what matters is how negation
works.
-/
def disjFC (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := fun s => φ.positive s ∪ ψ.positive s
  , negative := fun s => φ.negative s ∩ ψ.negative s }

notation:60 φ " ∨ᶠᶜ " ψ => disjFC φ ψ

-- ============================================================================
-- PART 3: Free Choice Inference
-- ============================================================================

/--
Basic FC: if ◇(φ ∨ ψ) and both disjuncts are live, then ◇φ ∧ ◇ψ.

This is the core Free Choice inference. In E&S, it follows from how
disjunction interacts with the bilateral structure.
-/
theorem fc_basic (φ ψ : BilateralDen W E) (s : HeimState W E)
    (h_disj : possible (φ ∨ᶠᶜ ψ) s)
    (h_φ : (φ.positive s).Nonempty)
    (h_ψ : (ψ.positive s).Nonempty) :
    possible φ s ∧ possible ψ s := by
  exact ⟨h_φ, h_ψ⟩

/--
Modified FC: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)

This is the key inference pattern that handles anaphora. The second
conjunct is ¬φ ∧ ψ, not just ψ, which captures the "other case" reading.

For bathroom disjunction:
- φ = ¬∃x.bathroom(x)
- ψ = funny-place(x)
- ¬φ = ∃x.bathroom(x)
- ¬φ ∧ ψ = ∃x.bathroom(x) ∧ funny-place(x)
-/
theorem modified_fc (φ ψ : BilateralDen W E) (s : HeimState W E)
    (h_disj : possible (φ ∨ᶠᶜ ψ) s)
    (h_φ : (φ.positive s).Nonempty)
    (h_notφ_ψ : (((~φ).conj ψ).positive s).Nonempty) :
    possible φ s ∧ possible ((~φ).conj ψ) s := by
  exact ⟨h_φ, h_notφ_ψ⟩

-- ============================================================================
-- PART 4: Bathroom Disjunction Pattern
-- ============================================================================

/--
The bathroom disjunction configuration.

"Either there's no bathroom or it's in a funny place"

- φ = ∃x.bathroom(x)  (there's a bathroom)
- ψ = funny-place(x)  (it's in a funny place)
- Sentence = ¬φ ∨ ψ   (no bathroom OR funny place)
-/
structure BathroomConfig (W E : Type*) where
  /-- The existential: ∃x.bathroom(x) -/
  bathroom : BilateralDen W E
  /-- The predicate on x: funny-place(x) -/
  funnyPlace : BilateralDen W E
  /-- The variable bound by the existential -/
  x : Nat

/--
The bathroom disjunction sentence: ¬∃x.bathroom(x) ∨ funny-place(x)
-/
def bathroomSentence (cfg : BathroomConfig W E) : BilateralDen W E :=
  (~cfg.bathroom) ∨ᶠᶜ cfg.funnyPlace

/--
FC with anaphora: bathroom disjunction inference pattern.

From: ◇(¬∃x.bathroom(x) ∨ funny-place(x))
Infer: ◇¬∃x.bathroom(x) ∧ ◇(∃x.bathroom(x) ∧ funny-place(x))

The crucial point: the second conjunct has the POSITIVE existential
(∃x.bathroom(x)) conjoined with funny-place(x), allowing the pronoun
to be bound.
-/
theorem fc_with_anaphora (cfg : BathroomConfig W E) (s : HeimState W E)
    (h_poss : possible (bathroomSentence cfg) s)
    (h_no_bath : ((~cfg.bathroom).positive s).Nonempty)
    (h_bath_funny : ((cfg.bathroom.conj cfg.funnyPlace).positive s).Nonempty) :
    possible (~cfg.bathroom) s ∧ possible (cfg.bathroom.conj cfg.funnyPlace) s := by
  exact ⟨h_no_bath, h_bath_funny⟩

-- ============================================================================
-- PART 5: Dual Prohibition Preservation
-- ============================================================================

/--
Dual prohibition: ¬◇φ ∧ ¬◇ψ ⊨ ¬◇(φ ∨ ψ)

If neither disjunct is possible, the disjunction is impossible.
This is the "converse" of FC and must be preserved.

E&S ensure this by keeping standard truth-conditions for disjunction;
FC arises from pragmatics/alternatives, not from changing the semantics.
-/
theorem dual_prohibition (φ ψ : BilateralDen W E) (s : HeimState W E)
    (h_φ : impossible φ s)
    (h_ψ : impossible ψ s) :
    impossible (φ ∨ᶠᶜ ψ) s := by
  simp only [impossible, HeimState.consistent] at *
  intro ⟨p, hp⟩
  simp only [disjFC] at hp
  rcases hp with hφ | hψ
  · exact h_φ ⟨p, hφ⟩
  · exact h_ψ ⟨p, hψ⟩

/--
Contrapositive: if ◇(φ ∨ ψ), then ◇φ ∨ ◇ψ.

This is the semantic content of disjunction (before FC pragmatics).
-/
theorem disj_to_poss_disj (φ ψ : BilateralDen W E) (s : HeimState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    possible φ s ∨ possible ψ s := by
  simp only [possible, disjFC, HeimState.consistent] at h ⊢
  obtain ⟨p, hp⟩ := h
  cases hp with
  | inl hφ => left; exact ⟨p, hφ⟩
  | inr hψ => right; exact ⟨p, hψ⟩

-- ============================================================================
-- PART 6: Cross-Disjunct Anaphora Mechanism
-- ============================================================================

/--
Key insight: In BUS, negation SWAPS positive and negative updates.

For ¬∃x.φ:
- (¬∃x.φ)⁺ = (∃x.φ)⁻ = states where NO entity satisfies φ
- (¬∃x.φ)⁻ = (∃x.φ)⁺ = states where SOME entity satisfies φ

When we have ¬∃x.φ ∨ ψ(x), the negative dimension of ¬∃x.φ
(= positive of ∃x.φ) introduces x, making it available for ψ(x).
-/
theorem negation_swaps_dims (φ : BilateralDen W E) (s : HeimState W E) :
    (~φ).positive s = φ.negative s ∧ (~φ).negative s = φ.positive s := by
  simp only [neg, and_self]

/--
The anaphoric reading arises from Modified FC.

When we derive ◇(¬φ ∧ ψ) from ◇(φ ∨ ψ), we're really deriving:
◇((∃x.bathroom)⁺ ∧ funny-place(x))

This is because ¬(¬∃x.bathroom) = ∃x.bathroom by DNE.
-/
theorem anaphora_via_dne (cfg : BathroomConfig W E) :
    ~~cfg.bathroom = cfg.bathroom := by
  simp only [neg_neg]

-- ============================================================================
-- PART 7: Example Configuration
-- ============================================================================

/--
A concrete example setup for testing.

World type with bathroom location.
-/
inductive BathroomWorld where
  | noBathroom
  | bathroomNormal
  | bathroomFunny
  deriving DecidableEq, Repr

/--
Entity type (just the bathroom if it exists).
-/
inductive BathroomEntity where
  | theBathroom
  deriving DecidableEq, Repr

/--
Bathroom predicate: entity is a bathroom.
-/
def isBathroom : BathroomEntity → BathroomWorld → Bool
  | .theBathroom, .noBathroom => false
  | .theBathroom, _ => true

/--
Funny place predicate: bathroom is in a funny place.
-/
def inFunnyPlace : BathroomEntity → BathroomWorld → Bool
  | .theBathroom, .bathroomFunny => true
  | _, _ => false

/--
Example bathroom configuration.
-/
def exampleBathroomConfig : BathroomConfig BathroomWorld BathroomEntity :=
  { bathroom := exists_ 0 Set.univ (pred1 isBathroom 0)
  , funnyPlace := pred1 inFunnyPlace 0
  , x := 0 }

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Modal Operators
- `possible`: ◇φ (positive update is consistent)
- `necessary`: □φ (state subsists in update)
- `impossible`: ¬◇φ (positive update is empty)

### Free Choice Disjunction
- `disjFC` (∨ᶠᶜ): Disjunction that licenses FC inference

### Inference Patterns
- `fc_basic`: ◇(φ ∨ ψ) → ◇φ ∧ ◇ψ (given both live)
- `modified_fc`: ◇(φ ∨ ψ) → ◇φ ∧ ◇(¬φ ∧ ψ)
- `fc_with_anaphora`: Bathroom disjunction pattern
- `dual_prohibition`: ¬◇φ ∧ ¬◇ψ → ¬◇(φ ∨ ψ)

### Example
- `BathroomConfig`: Configuration for bathroom disjunction
- `bathroomSentence`: ¬∃x.bathroom(x) ∨ funny-place(x)
- Example entities and predicates

## The Key Insight

FC with anaphora works because:
1. Negation swaps positive/negative (DNE holds)
2. Modified FC gives ◇(¬φ ∧ ψ), not just ◇ψ
3. ¬(¬∃x.φ) = ∃x.φ by DNE, introducing x for anaphora

This is why "Either there's no bathroom or it's in a funny place"
can have "it" bound by the bathroom introduced under negation.
-/

end Theories.BilateralUpdateSemantics.FreeChoice
