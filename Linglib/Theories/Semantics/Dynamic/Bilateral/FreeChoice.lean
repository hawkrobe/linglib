/-
# Free Choice with Anaphora
@cite{elliott-sudo-2025}

This module derives Free Choice (FC) inferences using Bilateral Update Semantics,
following @cite{elliott-sudo-2025} "Free choice with anaphora".

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

-/

import Linglib.Theories.Semantics.Dynamic.Bilateral.BUS

namespace Semantics.Dynamic.BUS.FreeChoice

open Semantics.Dynamic.Core
open Classical


variable {W E : Type*}

-- ============================================================================
-- Section 1: Modality concepts
-- ============================================================================

/--
Possibility: state s makes ◇φ true iff s[φ]⁺ is consistent.
Equivalent to checking `(BUSDen.diamond φ).positive s` is non-empty.
-/
def possible (φ : BilateralDen W E) (s : InfoState W E) : Prop :=
  (φ.positive s).consistent

/--
Necessity: state s makes □φ true iff s subsists in s[φ]⁺.
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

/-- Diamond positive = s when φ is possible, ∅ otherwise. -/
theorem diamond_positive_eq (φ : BilateralDen W E) (s : InfoState W E) :
    (BUS.BUSDen.diamond φ).positive s =
    if possible φ s then s else ∅ := by
  simp only [possible, BUS.BUSDen.diamond]

-- ============================================================================
-- Section 2: Modal disjunction (anaphora-sensitive, eq. 96)
-- ============================================================================

/--
Standard disjunction: the basic bilateral disjunction without FC preconditions.
-/
def disjStd (φ ψ : BilateralDen W E) : BilateralDen W E :=
  BilateralDen.disj φ ψ

/--
The part of the standard disjunction positive update that the first disjunct
is responsible for: the (1,*) row of the Strong Kleene truth table.

`s[φ ∨ ψ]₁⁺ = s[φ]⁺[ψ]⁺ ∪ s[φ]⁺[ψ]⁻ ∪ s[φ]⁺[ψ]?`

Every possibility in `s[φ]⁺` is verified by φ, and then classified by ψ
into one of three truth values.

Equation (92a) of @cite{elliott-sudo-2025}.
-/
def disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  ψ.positive (φ.positive s)
  ∪ ψ.negative (φ.positive s)
  ∪ ψ.unknownUpdate (φ.positive s)

/--
The part of the standard disjunction positive update that the second disjunct
is responsible for: the (*,1) column of the Strong Kleene truth table.

`s[φ ∨ ψ]₂⁺ = s[φ]⁺[ψ]⁺ ∪ s[φ]⁻[ψ]⁺ ∪ s[φ]?[ψ]⁺`

The key term for cross-disjunct anaphora is `s[φ]⁻[ψ]⁺`: when
`φ = ¬∃x.P(x)`, `s[φ]⁻ = s[∃x.P(x)]⁺` by DNE, introducing the
discourse referent for binding across disjuncts.

Equation (92b) of @cite{elliott-sudo-2025}.
-/
def disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  ψ.positive (φ.positive s)
  ∪ ψ.positive (φ.negative s)
  ∪ ψ.positive (φ.unknownUpdate s)

/--
Modal Disjunction (anaphora-sensitive version): semantic disjunction that
validates FC with anaphora.

Modal disjunction adds a precondition to the positive update requiring
that each disjunct contribute at least some possibilities. This
semantically derives FC without pragmatic reasoning.

Equation (96) of @cite{elliott-sudo-2025}.
-/
def disjModal (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s =>
      if (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty then
        (disjStd φ ψ).positive s
      else ∅
  , negative := (disjStd φ ψ).negative }

notation:60 φ " ∨ᶠᶜ " ψ => disjModal φ ψ

-- ============================================================================
-- Section 3: Structural properties of disjPos1 / disjPos2
-- ============================================================================

/--
The partition property guarantees that `φ.positive s ⊆ disjPos1 φ ψ s`:
every possibility verified by φ ends up in disjPos1 (classified by ψ as
true, false, or unknown).
-/
theorem subset_disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E) :
    φ.positive s ⊆ disjPos1 φ ψ s := by
  intro p hp
  unfold disjPos1
  exact BilateralDen.partition ψ (φ.positive s) hp

/--
Similarly, `φ.negative s ⊆ disjPos2 φ ψ s` via the middle term.
-/
theorem neg_subset_disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E) :
    ψ.positive (φ.negative s) ⊆ disjPos2 φ ψ s := by
  intro p hp
  exact Set.mem_union_left _ (Set.mem_union_right _ hp)

-- ============================================================================
-- Section 4: FC theorems (general)
-- ============================================================================

/--
FC preconditions: if the modal disjunction is possible, both disjuncts
contribute possibilities.

This is the general result from eq. 96. The study-specific bathroom
inference derives `possible φ s` and `(ψ.positive (φ.negative s)).Nonempty`
from these preconditions under assertability conditions.
-/
theorem fc_preconditions (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty := by
  unfold possible InfoState.consistent at h
  unfold disjModal at h
  by_cases hcond : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · exact hcond
  · simp only [hcond, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

/-- Extract disjPos1 nonemptiness from FC possibility. -/
theorem fc_disjPos1_nonempty (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos1 φ ψ s).Nonempty :=
  (fc_preconditions φ ψ s h).1

/-- Extract disjPos2 nonemptiness from FC possibility. -/
theorem fc_disjPos2_nonempty (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos2 φ ψ s).Nonempty :=
  (fc_preconditions φ ψ s h).2

-- ============================================================================
-- Section 5: Dual prohibition
-- ============================================================================

/--
Dual prohibition via disjPos1: if disjPos1 is empty (first disjunct
contributes nothing), modal disjunction is impossible.
-/
theorem dual_prohibition_disjPos1 (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : ¬(disjPos1 φ ψ s).Nonempty) :
    impossible (φ ∨ᶠᶜ ψ) s := by
  intro hc
  have ⟨h1, _⟩ := fc_preconditions φ ψ s hc
  exact absurd h1 h

/--
Dual prohibition via disjPos2: if disjPos2 is empty (second disjunct
contributes nothing), modal disjunction is impossible.
-/
theorem dual_prohibition_disjPos2 (φ ψ : BilateralDen W E) (s : InfoState W E)
    (h : ¬(disjPos2 φ ψ s).Nonempty) :
    impossible (φ ∨ᶠᶜ ψ) s := by
  intro hc
  have ⟨_, h2⟩ := fc_preconditions φ ψ s hc
  exact absurd h2 h

-- ============================================================================
-- Section 6: Structural results (DNE, negation, binding)
-- ============================================================================

/--
In BUS, negation swaps positive and negative updates.
-/
theorem negation_swaps_dims (φ : BilateralDen W E) (s : InfoState W E) :
    (BilateralDen.neg φ).positive s = φ.negative s ∧
    (BilateralDen.neg φ).negative s = φ.positive s := by
  simp only [BilateralDen.neg, and_self]

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
Egli's theorem (positive): `(∃x.φ) ∧ ψ ⊆ ∃x(φ ∧ ψ)` for positive updates.

The positive direction holds because conjunction sequences through the
existential's positive update.
-/
theorem egli_positive (x : Nat) (domain : Set E) (φ ψ : BilateralDen W E) (s : InfoState W E) :
    ((BilateralDen.exists_ x domain φ) ⊙ ψ).positive s ⊆
    (BilateralDen.exists_ x domain (φ ⊙ ψ)).positive s := by
  intro p hp
  exact hp

end Semantics.Dynamic.BUS.FreeChoice
