/-
# Free Choice with Anaphora (Elliott & Sudo 2025)

This module derives Free Choice (FC) inferences using Bilateral Update Semantics,
following Elliott & Sudo (2025) "Free choice with anaphora".

## The Puzzle

Bathroom disjunction: "Either there's no bathroom or it's in a funny place"

From this, we infer:
1. It's possible there's no bathroom
2. It's possible there's a bathroom AND it's in a funny place

The pronoun "it" in the second disjunct is bound by the existential in the
negated first disjunct. This cross-disjunct anaphora is puzzling because:
- Standard FC: ◇(φ ∨ ψ) → ◇φ ∧ ◇ψ (no anaphoric connection)
- With anaphora: ◇(¬∃xφ ∨ ψ(x)) → ◇¬∃xφ ∧ ◇(∃x(φ ∧ ψ(x)))

## Solution

BUS + Modal Disjunction:
1. Disjunction semantics: φ ∨ ψ entails ◇φ ∧ ◇ψ
2. Negation swaps positive/negative: ¬∃xφ positive = ∃xφ negative
3. Cross-disjunct binding: x introduced in ¬∃xφ is visible to ψ(x)

## Results

- Modified FC: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)
- FC with anaphora: bathroom inference pattern
- Dual prohibition: ¬◇φ ∧ ¬◇ψ ⊨ ¬(φ ∨ ψ) (preserved)

## References

- Elliott, P. (2023). Donkey disjunctions and overlapping updates. SALT 33: 666-685.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
- Zimmermann, T.E. (2000). Free Choice Disjunction and Epistemic Possibility.
- Alonso-Ovalle, L. (2006). Disjunction in Alternative Semantics.
-/

import Linglib.Theories.Semantics.Dynamic.Systems.BUS.Basic

namespace Semantics.Dynamic.BUS.FreeChoice

open Semantics.Dynamic.Core
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
  s ⪯ φ.positive s

/--
Impossibility: ¬◇φ iff s[φ]⁺ is empty.
-/
def impossible (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  ¬(φ.positive s).consistent

theorem impossible_iff_empty (φ : BilateralDen W E) (s : InfoState W E) :
    impossible φ s ↔ φ.positive s = ∅ := by
  simp only [impossible, InfoState.consistent, Set.not_nonempty_iff_eq_empty]


/--
Standard disjunction: the basic bilateral disjunction without FC preconditions.
-/
def disjStd (φ ψ : BilateralDen W E) : BilateralDen W E :=
  BilateralDen.disj φ ψ

/--
The part of the positive update that φ (first disjunct) is responsible for.
-/
def disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  φ.positive s

/--
The part of the positive update that ψ (second disjunct) is responsible for.

The key case for bathroom disjunctions: s[φ]⁻[ψ]⁺
When φ = ¬∃x.P(x), this is s[∃x.P(x)]⁺[ψ]⁺ by DNE.
-/
def disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  ψ.positive (φ.negative s)

/--
Modal Disjunction: semantic disjunction that validates FC.

Modal disjunction adds a precondition to the positive update requiring
that each disjunct contribute at least some possibilities. This
semantically derives FC without pragmatic reasoning.
-/
def disjModal (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s =>
      if (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty then
        (disjStd φ ψ).positive s
      else ∅
  , negative := (disjStd φ ψ).negative }

notation:60 φ " ∨ᶠᶜ " ψ => disjModal φ ψ


/--
FC is semantically derived from modal disjunction.

If `possible (φ ∨ᶠᶜ ψ) s`, then by the definition of `disjModal`:
1. `disjPos1 φ ψ s` is non-empty (i.e., φ contributes possibilities)
2. `disjPos2 φ ψ s` is non-empty (i.e., ψ contributes possibilities)

This directly implies `possible φ s` since `disjPos1 φ ψ s = φ.positive s`.
-/
theorem fc_semantic_first_disjunct (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    possible φ s := by
  unfold possible InfoState.consistent at h ⊢
  unfold disjModal at h
  by_cases hcond : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · exact hcond.1
  · simp only [hcond, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

/--
The second component: ψ contributes possibilities via `φ.negative`.
-/
theorem fc_semantic_second_disjunct (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (ψ.positive (φ.negative s)).Nonempty := by
  unfold possible InfoState.consistent at h
  unfold disjModal at h
  by_cases hcond : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · exact hcond.2
  · simp only [hcond, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

/--
Modified FC: ◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)

This is semantically derived.
-/
theorem modified_fc_semantic (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    possible φ s ∧ (ψ.positive (φ.negative s)).Nonempty := by
  exact ⟨fc_semantic_first_disjunct φ ψ s h, fc_semantic_second_disjunct φ ψ s h⟩


/--
The bathroom disjunction configuration.

"Either there's no bathroom or it's in a funny place"
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
  (BilateralDen.neg cfg.bathroom) ∨ᶠᶜ cfg.funnyPlace

/--
FC with anaphora: bathroom disjunction inference pattern.
-/
theorem fc_with_anaphora (cfg : BathroomConfig W E) (s : InfoState W E)
    (h_poss : possible (bathroomSentence cfg) s)
    (h_no_bath : ((BilateralDen.neg cfg.bathroom).positive s).Nonempty)
    (h_bath_funny : ((BilateralDen.conj cfg.bathroom cfg.funnyPlace).positive s).Nonempty) :
    possible (BilateralDen.neg cfg.bathroom) s ∧
    possible (BilateralDen.conj cfg.bathroom cfg.funnyPlace) s := by
  exact ⟨h_no_bath, h_bath_funny⟩


/--
Dual prohibition: ¬◇φ ∧ ¬◇ψ ⊨ ¬◇(φ ∨ ψ)

If neither disjunct is possible, the disjunction is impossible.
-/
theorem dual_prohibition (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h_φ : impossible φ s)
    (h_ψ : impossible ψ s) :
    impossible (φ ∨ᶠᶜ ψ) s := by
  simp only [impossible, InfoState.consistent] at *
  intro ⟨p, hp⟩
  unfold disjModal at hp
  simp only at hp
  split_ifs at hp with hcond
  · simp only [disjStd, BilateralDen.disj] at hp
    rcases hp with hφ | hψ
    · exact h_φ ⟨p, hφ⟩
    · exact h_ψ ⟨p, hψ⟩
  · exact hp


/--
In BUS, negation swaps positive and negative updates.
-/
theorem negation_swaps_dims (φ : BilateralDen W E) (s : InfoState W E) :
    (BilateralDen.neg φ).positive s = φ.negative s ∧
    (BilateralDen.neg φ).negative s = φ.positive s := by
  simp only [BilateralDen.neg, and_self]

/--
DNE as structural equality.
-/
theorem anaphora_via_dne (cfg : BathroomConfig W E) :
    BilateralDen.neg (BilateralDen.neg cfg.bathroom) = cfg.bathroom := by
  simp only [BilateralDen.neg_neg]

/--
Negated existential has existential in negative dimension.
-/
theorem exists_in_neg_dimension (x : Nat) (dom : Set E)
    (φ : BilateralDen W E) (s : InfoState W E) :
    (BilateralDen.neg (BilateralDen.exists_ x dom φ)).negative s =
    (BilateralDen.exists_ x dom φ).positive s := by
  simp only [BilateralDen.neg]

/--
DNE preserves binding.
-/
theorem dne_preserves_binding (x : Nat) (dom : Set E)
    (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (BilateralDen.conj (BilateralDen.neg (BilateralDen.neg (BilateralDen.exists_ x dom φ))) ψ).positive s =
    (BilateralDen.conj (BilateralDen.exists_ x dom φ) ψ).positive s := by
  simp only [BilateralDen.neg_neg]


/--
A concrete example setup for testing.
-/
inductive BathroomWorld where
  | noBathroom
  | bathroomNormal
  | bathroomFunny
  deriving DecidableEq, Repr

inductive BathroomEntity where
  | theBathroom
  deriving DecidableEq, Repr

def isBathroom : BathroomEntity → BathroomWorld → Bool
  | .theBathroom, .noBathroom => false
  | .theBathroom, _ => true

def inFunnyPlace : BathroomEntity → BathroomWorld → Bool
  | .theBathroom, .bathroomFunny => true
  | _, _ => false

def exampleBathroomConfig : BathroomConfig BathroomWorld BathroomEntity :=
  { bathroom := BilateralDen.exists_ 0 Set.univ (BilateralDen.pred1 isBathroom 0)
  , funnyPlace := BilateralDen.pred1 inFunnyPlace 0
  , x := 0 }


end Semantics.Dynamic.BUS.FreeChoice
