/-
# Bilateral Denotations

The bilateral denotation structure for dynamic semantics. Bilateral semantics
tracks both positive and negative update dimensions, enabling Double Negation
Elimination (DNE) and proper treatment of cross-disjunct anaphora.

## Insight

Standard dynamic semantics struggles with:
1. Double Negation Elimination (DNE): ¬¬φ should entail φ
2. Cross-disjunct anaphora in Free Choice contexts
3. Donkey disjunctions: "Either there's no bathroom, or it's upstairs"

Bilateral semantics solves these by tracking positive and negative updates
separately. Negation simply swaps the two dimensions.

## The Core Structure

```
BilateralDen W E = {
  positive : InfoState W E → InfoState W E  -- What survives assertion
  negative : InfoState W E → InfoState W E  -- What survives denial
}
```

## Key Properties

- DNE: ¬¬φ = φ (definitional - negation swaps, swap twice = identity)
- de Morgan: ¬(φ ∨ ψ) ⟺ ¬φ ∧ ¬ψ (valid, unlike standard DS)

-/

import Linglib.Theories.Semantics.Dynamic.Core.Update
import Mathlib.Algebra.Group.Defs

namespace Semantics.Dynamic.Core


/--
A bilateral denotation: positive and negative update functions.

In bilateral semantics, a sentence φ denotes a pair of update functions:
- `positive`: s[φ]⁺ - the result of asserting φ in state s
- `negative`: s[φ]⁻ - the result of denying φ in state s

Standard dynamic semantics only has positive updates. The negative dimension
is what enables DNE and proper treatment of cross-disjunct anaphora.
-/
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


/--
Atomic proposition: lift a classical proposition to bilateral form.

For an atomic proposition p:
- s[p]⁺ = { w ∈ s | p(w) } (keep worlds where p holds)
- s[p]⁻ = { w ∈ s | ¬p(w) } (keep worlds where p fails)
-/
def atom (pred : W → Bool) : BilateralDen W E :=
  { positive := λ s => s.update pred
  , negative := λ s => s.update (λ w => !pred w) }

/-- Atomic positive and negative are complementary -/
theorem atom_complementary (pred : W → Bool) (s : InfoState W E) :
    (atom pred).positive s ∪ (atom pred).negative s = s := by
  ext p
  simp only [atom, InfoState.update, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    cases hp : pred p.world
    · right; exact ⟨h, by simp [hp]⟩
    · left; exact ⟨h, by simp [hp]⟩

/-- Atomic positive and negative are disjoint -/
theorem atom_disjoint (pred : W → Bool) (s : InfoState W E) :
    (atom pred).positive s ∩ (atom pred).negative s = ∅ := by
  ext p
  constructor
  · intro ⟨⟨_, hp⟩, ⟨_, hnp⟩⟩
    simp only [atom, InfoState.update, Set.mem_setOf_eq, Bool.not_eq_true] at hp hnp
    simp_all
  · intro h; exact h.elim


/--
Negation: swap positive and negative updates.

This is the key insight of bilateral semantics. Negation doesn't "push in" -
it simply swaps which update is positive and which is negative.

s[¬φ]⁺ = s[φ]⁻
s[¬φ]⁻ = s[φ]⁺
-/
def neg (φ : BilateralDen W E) : BilateralDen W E :=
  { positive := φ.negative
  , negative := φ.positive }

/-- Notation for negation -/
prefix:max "~" => neg

/-- Double negation is identity (DNE). -/
@[simp]
theorem neg_neg (φ : BilateralDen W E) : ~~φ = φ := rfl

/-- DNE for positive updates -/
theorem dne_positive (φ : BilateralDen W E) (s : InfoState W E) :
    (~~φ).positive s = φ.positive s := rfl

/-- DNE for negative updates -/
theorem dne_negative (φ : BilateralDen W E) (s : InfoState W E) :
    (~~φ).negative s = φ.negative s := rfl

/-- Negation is involutive -/
theorem neg_involutive : Function.Involutive (neg : BilateralDen W E → BilateralDen W E) :=
  λ φ => neg_neg φ


/--
Conjunction: sequence positive updates, combine negative updates.

For conjunction φ ∧ ψ:
- s[φ ∧ ψ]⁺ = s[φ]⁺[ψ]⁺ (sequence: first assert φ, then ψ)
- s[φ ∧ ψ]⁻ = s[φ]⁻ ∪ (s[φ]⁺ ∩ s[ψ]⁻) (fail if φ fails OR φ succeeds but ψ fails)

The negative update reflects: a conjunction is denied if either conjunct
could be denied.
-/
def conj (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => ψ.positive (φ.positive s)
  , negative := λ s => φ.negative s ∪ (φ.positive s ∩ ψ.negative (φ.positive s)) }

/-- Notation for conjunction -/
infixl:65 " ⊙ " => conj

/-- Conjunction associates (for positive updates) -/
theorem conj_assoc_positive (φ ψ χ : BilateralDen W E) (s : InfoState W E) :
    ((φ ⊙ ψ) ⊙ χ).positive s = (φ ⊙ (ψ ⊙ χ)).positive s := by
  simp only [conj]


/--
Standard disjunction: choice between updates.

For standard disjunction φ ∨ ψ:
- s[φ ∨ ψ]⁺ = s[φ]⁺ ∪ s[ψ]⁺ (either disjunct holds)
- s[φ ∨ ψ]⁻ = s[φ]⁻ ∩ s[ψ]⁻ (both must fail to deny)
-/
def disj (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => φ.positive s ∪ ψ.positive s
  , negative := λ s => φ.negative s ∩ ψ.negative s }

/-- Notation for disjunction -/
infixl:60 " ⊕ " => disj

/-- De Morgan: negated disjunction swaps to conjunction of negations -/
theorem de_morgan_disj (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (~(φ ⊕ ψ)).positive s = φ.negative s ∩ ψ.negative s := by
  simp only [neg, disj]


/--
Existential quantification: introduce a discourse referent.

For ∃x.φ:
- s[∃x.φ]⁺ = s[x:=?][φ]⁺ (introduce x, then assert φ)
- s[∃x.φ]⁻ = { p ∈ s | ∀e, p[x↦e] ∉ s[x:=?][φ]⁺ } (no witness makes φ true)
-/
def exists_ (x : Nat) (domain : Set E) (φ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => φ.positive (s.randomAssign x domain)
  , negative := λ s =>
      { p ∈ s | ∀ e ∈ domain,
        (p.extend x e) ∉ φ.positive (s.randomAssign x domain) } }

/-- Existential with full domain -/
def existsFull (x : Nat) (φ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => φ.positive (s.randomAssignFull x)
  , negative := λ s =>
      { p ∈ s | ∀ e : E, (p.extend x e) ∉ φ.positive (s.randomAssignFull x) } }


/--
Universal quantification: ∀x.φ = ¬∃x.¬φ

In bilateral semantics, universal quantification is defined via de Morgan duality.
This ensures proper interaction with negation.
-/
def forall_ (x : Nat) (domain : Set E) (φ : BilateralDen W E) : BilateralDen W E :=
  ~(exists_ x domain (~φ))


/--
Bilateral support: state s supports φ iff positive update is non-empty
and s subsists in s[φ]⁺.
-/
def supports (s : InfoState W E) (φ : BilateralDen W E) : Prop :=
  (φ.positive s).consistent ∧ s ⪯ φ.positive s

/--
Bilateral entailment: φ entails ψ iff for all consistent states s,
s[φ]⁺ supports ψ.
-/
def entails (φ ψ : BilateralDen W E) : Prop :=
  ∀ s : InfoState W E, (φ.positive s).consistent →
    supports (φ.positive s) ψ

notation:50 φ " ⊨ᵇ " ψ => entails φ ψ


/--
Egli's theorem: ∃x.φ ∧ ψ ⊨ ∃x[φ ∧ ψ]

When an existential takes wide scope over conjunction, the variable it
introduces is accessible in the second conjunct. This is the key property
for cross-sentential anaphora.

In bilateral semantics, this follows from the sequencing of updates.
-/
theorem egli (x : Nat) (domain : Set E) (φ ψ : BilateralDen W E) (s : InfoState W E) :
    ((exists_ x domain φ) ⊙ ψ).positive s ⊆
    (exists_ x domain (φ ⊙ ψ)).positive s := by
  intro p hp
  -- These are definitionally equal due to how conj and exists_ are defined
  exact hp


/-- Create bilateral from predicate over entities -/
def pred1 (p : E → W → Bool) (t : Nat) : BilateralDen W E :=
  { positive := λ s => { poss ∈ s | p (poss.assignment t) poss.world }
  , negative := λ s => { poss ∈ s | !p (poss.assignment t) poss.world } }

/-- Create bilateral from binary predicate -/
def pred2 (p : E → E → W → Bool) (t₁ t₂ : Nat) : BilateralDen W E :=
  { positive := λ s => { poss ∈ s | p (poss.assignment t₁) (poss.assignment t₂) poss.world }
  , negative := λ s => { poss ∈ s | !p (poss.assignment t₁) (poss.assignment t₂) poss.world } }


/-- Unilateral denotation: single update function -/
def UnilateralDen (W : Type*) (E : Type*) := InfoState W E → InfoState W E

/-- View bilateral as pair of updates -/
def toPair (φ : BilateralDen W E) : (InfoState W E → InfoState W E) × (InfoState W E → InfoState W E) :=
  (φ.positive, φ.negative)

/-- Construct bilateral from pair -/
def ofPair (p : (InfoState W E → InfoState W E) × (InfoState W E → InfoState W E)) : BilateralDen W E :=
  { positive := p.1, negative := p.2 }

theorem toPair_ofPair (p : (InfoState W E → InfoState W E) × (InfoState W E → InfoState W E)) :
    toPair (ofPair p) = p := rfl

theorem ofPair_toPair (φ : BilateralDen W E) : ofPair (toPair φ) = φ := rfl

/-- Negation = swap on pairs -/
theorem neg_eq_swap (φ : BilateralDen W E) :
    toPair (~φ) = Prod.swap (toPair φ) := rfl

/-- DNE follows from swap ∘ swap = id -/
theorem dne_from_swap (φ : BilateralDen W E) :
    toPair (~~φ) = toPair φ := by simp [neg_eq_swap, Prod.swap_swap]

/-- Projection: bilateral → unilateral (forgets negative) -/
def toUnilateral (φ : BilateralDen W E) : UnilateralDen W E := φ.positive


instance : InvolutiveNeg (BilateralDen W E) where
  neg := neg
  neg_neg := neg_neg

end BilateralDen


end Semantics.Dynamic.Core
