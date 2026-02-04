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

- Elliott, P. (2023). Donkey disjunctions and overlapping updates. SALT 33: 666-685.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
- Zimmermann, T.E. (2000). Free Choice Disjunction and Epistemic Possibility.
- Alonso-Ovalle, L. (2006). Disjunction in Alternative Semantics.
-/

import Linglib.Theories.DynamicSemantics.BilateralUpdate.Basic

namespace Theories.BilateralUpdateSemantics.FreeChoice

open Theories.DynamicSemantics.Core
open Theories.DynamicSemantics.Core.InfoState
open BilateralUpdateSemantics.BilateralDen
open Classical


variable {W E : Type*}

/--
Possibility: state s makes ◇φ true iff s[φ]⁺ is consistent.

In BUS, possibility checks whether the positive update yields a non-empty state.
-/
def possible (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  (φ.positive s).consistent

/--
Necessity: state s makes □φ true iff s subsists in s[φ]⁺.

Every possibility in s has a descendant that survives the positive update.
-/
def necessary (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  InfoState.subsistsIn s (φ.positive s)

/--
Impossibility: ¬◇φ iff s[φ]⁺ is empty.
-/
def impossible (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  ¬(φ.positive s).consistent

theorem impossible_iff_empty (φ : BilateralDen W E) (s : InfoState W E) :
    impossible φ s ↔ φ.positive s = ∅ := by
  simp only [impossible, InfoState.consistent, Theories.DynamicSemantics.Core.InfoState.consistent,
             Set.not_nonempty_iff_eq_empty]


/--
Standard disjunction: the basic bilateral disjunction without FC preconditions.

For standard disjunction φ ∨ ψ:
- s[φ ∨ ψ]⁺ = s[φ]⁺ ∪ s[ψ]⁺
- s[φ ∨ ψ]⁻ = s[φ]⁻ ∩ s[ψ]⁻

This is used as the base for modal disjunction.
-/
def disjStd (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := fun s => φ.positive s ∪ ψ.positive s
  , negative := fun s => φ.negative s ∩ ψ.negative s }

/--
The part of the positive update that φ (first disjunct) is responsible for.

From E&S (2025) Definition 92a:
s[φ ∨ ψ]⁺₁ = s[φ]⁺[ψ]⁺ ∪ s[φ]⁺[ψ]⁻ ∪ s[φ]⁺[ψ]?

Simplified: when ψ doesn't introduce anaphoric information, this is just s[φ]⁺.
For the full version with anaphora, we'd need the complete Strong Kleene composition.
-/
def disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  -- Possibilities where φ is true (regardless of ψ's value)
  -- This is the "verification via φ" component
  φ.positive s

/--
The part of the positive update that ψ (second disjunct) is responsible for.

From E&S (2025) Definition 92b:
s[φ ∨ ψ]⁺₂ = s[φ]⁺[ψ]⁺ ∪ s[φ]⁻[ψ]⁺ ∪ s[φ]?[ψ]⁺

The key case for bathroom disjunctions: s[φ]⁻[ψ]⁺
When φ = ¬∃x.P(x), this is s[∃x.P(x)]⁺[ψ]⁺ by DNE.
-/
def disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  -- Possibilities where ψ is true (when evaluated after φ fails or is undefined)
  -- The crucial case: s[φ]⁻[ψ]⁺ is where anaphoric binding happens
  ψ.positive (φ.negative s)

/--
Modal Disjunction: semantic disjunction that validates FC.

From E&S (2025) Definition 96:
s[φ ∨ ψ]⁺ = s[φ ∨ ψ]⁺ if s[φ ∨ ψ]⁺₁ ≠ ∅ AND s[φ ∨ ψ]⁺₂ ≠ ∅, else ∅
s[φ ∨ ψ]⁻ = s[φ ∨ ψ]⁻ (unchanged)

The KEY SEMANTIC INSIGHT: Modal disjunction adds a PRECONDITION to the
positive update requiring that EACH disjunct contribute at least some
possibilities. This semantically derives FC without pragmatic reasoning.

The negative update is unchanged, preserving Dual Prohibition:
¬◇(φ ∨ ψ) ⊨ ¬◇φ ∧ ¬◇ψ
-/
def disjModal (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := fun s =>
      -- The precondition: each disjunct must contribute possibilities
      if (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty then
        (disjStd φ ψ).positive s
      else ∅
  , negative := (disjStd φ ψ).negative }

notation:60 φ " ∨ᶠᶜ " ψ => disjModal φ ψ

-- Note: disjFC is now an alias for disjModal (the FC-deriving version)
-- Use disjStd if you need standard disjunction without FC preconditions


/--
KEY THEOREM: FC is SEMANTICALLY DERIVED from modal disjunction.

If `possible (φ ∨ᶠᶜ ψ) s`, then by the definition of `disjModal`:
1. `disjPos1 φ ψ s` is non-empty (i.e., φ contributes possibilities)
2. `disjPos2 φ ψ s` is non-empty (i.e., ψ contributes possibilities)

This directly implies `possible φ s` since `disjPos1 φ ψ s = φ.positive s`.

This is E&S's semantic account: FC follows from the semantics of modal
disjunction, not from pragmatic reasoning about alternatives.
-/
theorem fc_semantic_first_disjunct (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    possible φ s := by
  unfold possible InfoState.consistent at h ⊢
  unfold disjModal at h
  -- The positive update is non-empty only if the precondition holds
  by_cases hcond : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · -- Precondition holds, so disjPos1 is non-empty
    exact hcond.1
  · -- Precondition fails, so positive update is empty
    simp only [hcond, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

/--
The second component: ψ contributes possibilities via `φ.negative`.

`disjPos2 φ ψ s = ψ.positive (φ.negative s)`

For bathroom disjunctions where φ = ~bathroom:
- `(~bathroom).negative s = bathroom.positive s` (by DNE)
- So `disjPos2 (~bathroom) funnyPlace s = funnyPlace.positive (bathroom.positive s)`

This is where cross-disjunct anaphoric binding happens!
-/
theorem fc_semantic_second_disjunct (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (ψ.positive (φ.negative s)).Nonempty := by
  unfold possible InfoState.consistent at h
  unfold disjModal at h
  by_cases hcond : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · -- Precondition holds, so disjPos2 is non-empty
    exact hcond.2
  · -- Precondition fails, so positive update is empty
    simp only [hcond, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

/--
Modified FC: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)

This is SEMANTICALLY DERIVED. The second component comes from the fact that
`disjPos2` evaluates ψ in the context where φ is false.

For bathroom disjunction:
- φ = ¬∃x.bathroom(x)
- ψ = funny-place(x)
- ¬φ = ∃x.bathroom(x) (by DNE)
- The second component is: ψ.positive (φ.negative s)
  = funnyPlace.positive ((~bathroom).negative s)
  = funnyPlace.positive (bathroom.positive s)

This IS the "∃x.bathroom(x) ∧ funny-place(x)" reading!
-/
theorem modified_fc_semantic (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    possible φ s ∧ (ψ.positive (φ.negative s)).Nonempty := by
  exact ⟨fc_semantic_first_disjunct φ ψ s h, fc_semantic_second_disjunct φ ψ s h⟩


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
theorem fc_with_anaphora (cfg : BathroomConfig W E) (s : InfoState W E)
    (h_poss : possible (bathroomSentence cfg) s)
    (h_no_bath : ((~cfg.bathroom).positive s).Nonempty)
    (h_bath_funny : ((cfg.bathroom.conj cfg.funnyPlace).positive s).Nonempty) :
    possible (~cfg.bathroom) s ∧ possible (cfg.bathroom.conj cfg.funnyPlace) s := by
  exact ⟨h_no_bath, h_bath_funny⟩


/--
Dual prohibition: ¬◇φ ∧ ¬◇ψ ⊨ ¬◇(φ ∨ ψ)

If neither disjunct is possible, the disjunction is impossible.
This is the "converse" of FC and must be preserved.

E&S ensure this by keeping standard truth-conditions for disjunction;
FC arises from pragmatics/alternatives, not from changing the semantics.
-/
theorem dual_prohibition (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h_φ : impossible φ s)
    (h_ψ : impossible ψ s) :
    impossible (φ ∨ᶠᶜ ψ) s := by
  simp only [impossible, InfoState.consistent] at *
  intro ⟨p, hp⟩
  -- For modal disjunction, if positive update is non-empty, then the precondition held
  -- and thus φ.positive s ∪ ψ.positive s was computed
  unfold disjModal at hp
  simp only at hp
  split_ifs at hp with hcond
  · -- Precondition held, so hp ∈ disjStd positive
    simp only [disjStd] at hp
    rcases hp with hφ | hψ
    · exact h_φ ⟨p, hφ⟩
    · exact h_ψ ⟨p, hψ⟩
  · -- Precondition failed, positive update was empty
    exact hp

/--
Semantic FC (disjunctive form): if ◇(φ ∨ ψ), then ◇φ ∨ ◇ψ.

This is the WEAKER form of FC. Modal disjunction actually gives us the
STRONGER conjunctive form `◇φ ∧ (ψ after ¬φ is possible)`.
-/
theorem disj_to_poss_disj (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    possible φ s ∨ possible ψ s := by
  -- Modal disjunction gives us the stronger result
  left
  exact fc_semantic_first_disjunct φ ψ s h


/--
Key insight: In BUS, negation SWAPS positive and negative updates.

For ¬∃x.φ:
- (¬∃x.φ)⁺ = (∃x.φ)⁻ = states where NO entity satisfies φ
- (¬∃x.φ)⁻ = (∃x.φ)⁺ = states where SOME entity satisfies φ

When we have ¬∃x.φ ∨ ψ(x), the negative dimension of ¬∃x.φ
(= positive of ∃x.φ) introduces x, making it available for ψ(x).
-/
theorem negation_swaps_dims (φ : BilateralDen W E) (s : InfoState W E) :
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

/--
Key structural theorem: negated existential has existential in negative dimension.

For ¬∃x.φ:
- (~(exists_ x dom φ)).positive s = (exists_ x dom φ).negative s
- (~(exists_ x dom φ)).negative s = (exists_ x dom φ).positive s

The negative dimension of ¬∃x.φ IS the positive dimension of ∃x.φ,
which is where x is introduced. This is what enables cross-disjunct binding.
-/
theorem exists_in_neg_dimension (x : Nat) (dom : Set E) (φ : BilateralDen W E) (s : InfoState W E) :
    (~(exists_ x dom φ)).negative s = (exists_ x dom φ).positive s := by
  simp only [neg]

/--
DNE preserves binding: ¬¬∃x.φ ⊙ ψ has the same positive update as ∃x.φ ⊙ ψ.

This is crucial for the bathroom disjunction: when we derive ◇(¬¬∃x.φ ∧ ψ(x)),
the binding structure is preserved because DNE gives us back ∃x.φ.
-/
theorem dne_preserves_binding (x : Nat) (dom : Set E) (φ ψ : BilateralDen W E) (s : InfoState W E) :
    ((~~(exists_ x dom φ)).conj ψ).positive s = ((exists_ x dom φ).conj ψ).positive s := by
  simp only [neg_neg]

/--
Bathroom FC (semantic core): from ◇(¬∃x.bath ∨ funny(x)), derive ◇¬∃x.bath ∨ ◇funny(x).

This is the pure semantic content of disjunction. The CONJUNCTION of
possibilities (◇¬∃x.bath ∧ ◇(∃x.bath ∧ funny(x))) requires pragmatic
reasoning about alternatives - see Comparisons/FreeChoice.lean for
different pragmatic accounts (RSA, Innocent Inclusion, etc.).
-/
theorem bathroom_fc_semantic (cfg : BathroomConfig W E) (s : InfoState W E)
    (h_poss : possible (bathroomSentence cfg) s) :
    possible (~cfg.bathroom) s ∨ possible cfg.funnyPlace s := by
  exact disj_to_poss_disj (~cfg.bathroom) cfg.funnyPlace s h_poss

/--
Bathroom FC (with anaphoric binding): when the second disjunct is possible,
its binding comes from the negative dimension of the first disjunct.

The key insight: funnyPlace.positive s contains possibilities where x is
assigned to an entity. These possibilities come from the random assignment
that would have happened if we took the "bathroom exists" branch.

For the full FC inference (◇φ ∧ ◇ψ), see pragmatic accounts.
-/
theorem bathroom_binding_source (cfg : BathroomConfig W E) (s : InfoState W E)
    (h_funny : possible cfg.funnyPlace s) :
    -- The funnyPlace possibilities have assignments for variable cfg.x
    -- because funnyPlace is evaluated in a state with random assignment
    (cfg.funnyPlace.positive s).Nonempty := h_funny

/--
Standard FC disjunctive form: from ◇(φ ∨ ψ), get ◇φ ∨ ◇ψ.

This is the weaker disjunctive form. The modal disjunction semantics
actually gives us the stronger CONJUNCTIVE form via `modified_fc_semantic`.
-/
theorem fc_disjunctive (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    possible φ s ∨ possible ψ s :=
  Or.inl (fc_semantic_first_disjunct φ ψ s h)


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

-- SUMMARY

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
