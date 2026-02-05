/-
# Bilateral Update Semantics

Bilateral update semantics with positive and negative update dimensions enabling DNE and cross-disjunct anaphora.

## Main definitions

- `BilateralDen`: positive and negative update functions
- `atom`, `neg`, `conj`, `disj`, `exists_`, `forall_`
- `supports`, `entails`

## References

- Elliott, P. (2023). Towards a dynamics of ellipsis identity.
- Elliott, P. & Sudo, Y. (2025). Free choice with anaphora. S&P 18.
-/

import Linglib.Theories.DynamicSemantics.Core.Basic
import Linglib.Theories.DynamicSemantics.Core.Update
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Defs

namespace Theories.BilateralUpdateSemantics

open Theories.DynamicSemantics.Core


/-- Bilateral denotation: positive and negative update functions. -/
structure BilateralDen (W : Type*) (E : Type*) where
  /-- Positive update: result of asserting the sentence -/
  positive : InfoState W E → InfoState W E
  /-- Negative update: result of denying the sentence -/
  negative : InfoState W E → InfoState W E

@[ext]
theorem BilateralDen.ext {W E : Type*} {φ ψ : BilateralDen W E}
    (hp : φ.positive = ψ.positive) (hn : φ.negative = ψ.negative) : φ = ψ := by
  cases φ; cases ψ
  simp only [mk.injEq]
  exact ⟨hp, hn⟩

namespace BilateralDen

variable {W E : Type*}


/-- Lift atomic proposition to bilateral form. -/
def atom (pred : W → Bool) : BilateralDen W E :=
  { positive := λ s => s.update pred
  , negative := λ s => s.update (λ w => !pred w) }

/-- Atomic positive and negative updates are complementary. -/
theorem atom_complementary (pred : W → Bool) (s : InfoState W E) :
    (atom pred).positive s ∪ (atom pred).negative s = s := by
  ext p
  simp only [atom, InfoState.update, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    cases hp : pred p.world
    · right; exact ⟨h, by simp [hp]⟩
    · left; exact ⟨h, hp⟩


/-- Negation swaps positive and negative updates. -/
def neg (φ : BilateralDen W E) : BilateralDen W E :=
  { positive := φ.negative
  , negative := φ.positive }

/-- Double negation elimination. -/
@[simp]
theorem neg_neg (φ : BilateralDen W E) : φ.neg.neg = φ := rfl

/-- DNE for positive updates. -/
theorem dne_positive (φ : BilateralDen W E) (s : InfoState W E) :
    φ.neg.neg.positive s = φ.positive s := rfl

/-- DNE for negative updates. -/
theorem dne_negative (φ : BilateralDen W E) (s : InfoState W E) :
    φ.neg.neg.negative s = φ.negative s := rfl


/-- Conjunction sequences positive updates and combines negative updates. -/
def conj (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => ψ.positive (φ.positive s)
  , negative := λ s => φ.negative s ∪ (φ.positive s ∩ ψ.negative (φ.positive s)) }

/-- Conjunction associates for positive updates. -/
theorem conj_assoc_positive (φ ψ χ : BilateralDen W E) (s : InfoState W E) :
    ((φ.conj ψ).conj χ).positive s = (φ.conj (ψ.conj χ)).positive s := by
  simp only [conj]


/-- Standard disjunction: union of positive updates, intersection of negative. -/
def disj (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => φ.positive s ∪ ψ.positive s
  , negative := λ s => φ.negative s ∩ ψ.negative s }

/-- De Morgan for disjunction. -/
theorem disj_neg_positive (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (φ.disj ψ).neg.positive s = φ.negative s ∩ ψ.negative s := by
  simp only [neg, disj]


/-- Existential quantification introduces a discourse referent. -/
def exists_ (x : Nat) (domain : Set E) (φ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => φ.positive (s.randomAssign x domain)
  , negative := λ s =>
      { p ∈ s | ∀ e ∈ domain,
        (p.extend x e) ∉ φ.positive (s.randomAssign x domain) } }

/-- Existential with full domain. -/
def existsFull (x : Nat) (φ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => φ.positive (s.randomAssignFull x)
  , negative := λ s =>
      { p ∈ s | ∀ e : E, (p.extend x e) ∉ φ.positive (s.randomAssignFull x) } }


/-- Universal quantification via de Morgan: ∀x.φ = ¬∃x.¬φ. -/
def forall_ (x : Nat) (domain : Set E) (φ : BilateralDen W E) : BilateralDen W E :=
  (exists_ x domain φ.neg).neg


/-- Bilateral support: state s supports φ iff positive update is non-empty and s subsists in s[φ]⁺. -/
def supports (s : InfoState W E) (φ : BilateralDen W E) : Prop :=
  InfoState.consistent (φ.positive s) ∧ InfoState.subsistsIn s (φ.positive s)

/-- Bilateral entailment: φ entails ψ iff s[φ]⁺ supports ψ for all consistent states. -/
def entails (φ ψ : BilateralDen W E) : Prop :=
  ∀ s : InfoState W E, InfoState.consistent (φ.positive s) →
    supports (φ.positive s) ψ

notation:50 φ " ⊨ᵇ " ψ => entails φ ψ

/-- DNE: ¬¬φ and φ have identical positive updates. -/
theorem dne_positive_eq (φ : BilateralDen W E) (s : InfoState W E) :
    φ.neg.neg.positive s = φ.positive s := by
  simp only [neg]


/-- Egli's theorem: ∃x.φ ∧ ψ ⊨ ∃x[φ ∧ ψ]. -/
theorem egli (x : Nat) (domain : Set E) (φ ψ : BilateralDen W E) (s : InfoState W E) :
    ((exists_ x domain φ).conj ψ).positive s ⊆
    (exists_ x domain (φ.conj ψ)).positive s := by
  intro p hp
  -- hp : p ∈ ψ.positive (φ.positive (s.randomAssign x domain))
  -- goal: p ∈ (φ.conj ψ).positive (s.randomAssign x domain)
  -- These are definitionally equal due to how conj and exists_ are defined
  exact hp


/-- DNE as update equality: ¬¬φ and φ have identical positive and negative updates. -/
theorem dne_update_eq (φ : BilateralDen W E) (s : InfoState W E) :
    (φ.neg.neg).positive s = φ.positive s ∧ (φ.neg.neg).negative s = φ.negative s := by
  simp only [neg_neg, and_self]

/-- DNE preserves consistency. -/
theorem dne_consistent_iff (φ : BilateralDen W E) (s : InfoState W E) :
    ((φ.neg.neg).positive s).consistent ↔ (φ.positive s).consistent := by
  simp only [neg_neg]


/-- Notation for negation -/
prefix:max "~" => neg

/-- Notation for conjunction -/
infixl:65 " ⊙ " => conj

/-- Notation for disjunction -/
infixl:60 " ⊕ " => disj

/-- Create bilateral from predicate over entities -/
def pred1 (p : E → W → Bool) (t : Nat) : BilateralDen W E :=
  { positive := λ s => { poss ∈ s | p (poss.assignment t) poss.world }
  , negative := λ s => { poss ∈ s | !p (poss.assignment t) poss.world } }

/-- Create bilateral from binary predicate -/
def pred2 (p : E → E → W → Bool) (t₁ t₂ : Nat) : BilateralDen W E :=
  { positive := λ s => { poss ∈ s | p (poss.assignment t₁) (poss.assignment t₂) poss.world }
  , negative := λ s => { poss ∈ s | !p (poss.assignment t₁) (poss.assignment t₂) poss.world } }

end BilateralDen


namespace BilateralDen

variable {W E : Type*}

/-- Negation is involutive: ~~φ = φ. -/
theorem neg_involutive : Function.Involutive (neg : BilateralDen W E → BilateralDen W E) :=
  λ φ => neg_neg φ

-- De Morgan laws
theorem neg_conj_positive (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (~(φ.conj ψ)).positive s = (φ.conj ψ).negative s := rfl

theorem neg_disj_positive (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (~(φ.disj ψ)).positive s = (φ.disj ψ).negative s := rfl

theorem disj_negative_eq_inter (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (φ.disj ψ).negative s = φ.negative s ∩ ψ.negative s := rfl

theorem disj_positive_eq_union (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (φ.disj ψ).positive s = φ.positive s ∪ ψ.positive s := rfl

-- Boolean Algebra Connection

/-- For atoms, positive and negative are disjoint. -/
theorem atom_disjoint' (pred : W → Bool) (s : InfoState W E) :
    (atom pred).positive s ∩ (atom pred).negative s = ∅ := by
  ext p
  constructor
  · intro ⟨⟨_, hp⟩, ⟨_, hnp⟩⟩
    simp only [atom, InfoState.update, Set.mem_setOf_eq, Bool.not_eq_true] at hp hnp
    simp_all
  · intro h; exact h.elim

/-- Negation swaps positive and negative. -/
theorem neg_positive_eq_negative (φ : BilateralDen W E) (s : InfoState W E) :
    (~φ).positive s = φ.negative s := rfl

theorem neg_negative_eq_positive (φ : BilateralDen W E) (s : InfoState W E) :
    (~φ).negative s = φ.positive s := rfl

-- Pair Isomorphism: Bilateral ≃ Unilateral × Unilateral

/-- Unilateral denotation: single update function. -/
def UnilateralDen (W : Type*) (E : Type*) := InfoState W E → InfoState W E

/-- View bilateral as pair of updates. -/
def toPair (φ : BilateralDen W E) : (InfoState W E → InfoState W E) × (InfoState W E → InfoState W E) :=
  (φ.positive, φ.negative)

/-- Construct bilateral from pair. -/
def ofPair (p : (InfoState W E → InfoState W E) × (InfoState W E → InfoState W E)) : BilateralDen W E :=
  { positive := p.1, negative := p.2 }

theorem toPair_ofPair (p : (InfoState W E → InfoState W E) × (InfoState W E → InfoState W E)) :
    toPair (ofPair p) = p := rfl

theorem ofPair_toPair (φ : BilateralDen W E) : ofPair (toPair φ) = φ := rfl

/-- Negation = swap on pairs. -/
theorem neg_eq_swap (φ : BilateralDen W E) :
    toPair (~φ) = Prod.swap (toPair φ) := rfl

/-- DNE follows from swap ∘ swap = id. -/
theorem dne_from_swap (φ : BilateralDen W E) :
    toPair (~~φ) = toPair φ := by simp [neg_eq_swap, Prod.swap_swap]

/-- Unilateral negation via set difference (not involutive). -/
def unilateralNeg (φ : UnilateralDen W E) : UnilateralDen W E :=
  λ s => s.diff (φ s)

/-- Projection: bilateral → unilateral (forgets negative). -/
def toUnilateral (φ : BilateralDen W E) : UnilateralDen W E := φ.positive

-- ℤ/2ℤ Symmetry

/-- Negation generates ℤ/2ℤ action: neg² = id. -/
theorem neg_generates_z2 (φ : BilateralDen W E) :
    neg (neg φ) = (id ∘ id) φ := by simp [neg_neg]

/-- Bilateral = twisted product: swap relates positive to negative. -/
theorem bilateral_symmetry (φ : BilateralDen W E) :
    toPair (~φ) = (φ.negative, φ.positive) ∧
    toPair (~~φ) = (φ.positive, φ.negative) := by
  constructor
  · rfl
  · simp [toPair, neg_neg]

-- Mathlib Connection

instance : InvolutiveNeg (BilateralDen W E) where
  neg := neg
  neg_neg := neg_neg

end BilateralDen

end Theories.BilateralUpdateSemantics
