import Linglib.Semantics.Dynamic.Core.Update
import Linglib.Core.Logic.Bilateral.Defs
import Mathlib.Algebra.Group.Defs

/-!
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
  positive : InfoState W E → InfoState W E -- What survives assertion
  negative : InfoState W E → InfoState W E -- What survives denial
}
```

## Key Properties

- DNE: ¬¬φ = φ (definitional - negation swaps, swap twice = identity)
- de Morgan: ¬(φ ∨ ψ) ⟺ ¬φ ∧ ¬ψ (valid, unlike standard DS)

## Cross-cutting pointers

This is the BUS / bilateral DNE strategy listed in `Dynamic/Connectives/Defs.lean`'s
"three incompatible DNE solutions" table. The empirical comparison
against full ICDRT (which solves disagreement, modal
subordination, and three-way veridicality on top of DNE + bathroom) is in
`Studies/Hofmann2025.lean §7`. The empirical comparison
against PLA (which lacks DNE for anaphora and fails on the bathroom
sentence) is in `Studies/Dekker2012.lean`.
-/

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
def atom (pred : W → Prop) : BilateralDen W E :=
  { positive := λ s => s.update pred
  , negative := λ s => s.update (λ w => ¬ pred w) }

/-- Atomic positive and negative are complementary -/
theorem atom_complementary (pred : W → Prop) (s : InfoState W E) :
    (atom pred).positive s ∪ (atom pred).negative s = s := by
  ext p
  simp only [atom, InfoState.update, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases hp : pred p.world
    · left; exact ⟨h, hp⟩
    · right; exact ⟨h, hp⟩

/-- Atomic positive and negative are disjoint -/
theorem atom_disjoint (pred : W → Prop) (s : InfoState W E) :
    (atom pred).positive s ∩ (atom pred).negative s = ∅ := by
  ext p
  constructor
  · intro ⟨⟨_, hp⟩, ⟨_, hnp⟩⟩
    exact absurd hp hnp
  · intro h; exact h.elim

/-- Atomic positive update is monotone. -/
theorem atom_positive_monotone (pred : W → Prop) :
    Monotone (atom pred).positive (α := InfoState W E) :=
  sep_monotone _

/-- Atomic negative update is monotone. -/
theorem atom_negative_monotone (pred : W → Prop) :
    Monotone (atom pred).negative (α := InfoState W E) :=
  sep_monotone _

/-- Atomic positive update is eliminative. -/
theorem atom_positive_eliminative (pred : W → Prop) :
    IsEliminative (atom pred).positive (P := Possibility W E) :=
  sep_eliminative _

/-- Atomic negative update is eliminative. -/
theorem atom_negative_eliminative (pred : W → Prop) :
    IsEliminative (atom pred).negative (P := Possibility W E) :=
  sep_eliminative _


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
Unknown update: possibilities in s that subsist in neither the positive
nor the negative update.

This is the dynamic analog of the third truth value (#) in Strong Kleene
logic. For atomic propositions, the unknown update is always empty.
For existential statements, it captures possibilities where variable
definedness introduces a gap.

Equation (53) of [elliott-sudo-2025].
-/
def unknownUpdate (φ : BilateralDen W E) (s : InfoState W E) : InfoState W E :=
  { p ∈ s | p ∉ φ.positive s ∧ p ∉ φ.negative s }

/-- The unknown update of a negation equals the unknown update of the original. -/
theorem unknownUpdate_neg (φ : BilateralDen W E) (s : InfoState W E) :
    unknownUpdate (~φ) s = unknownUpdate φ s := by
  ext p
  simp only [unknownUpdate, neg, Set.mem_setOf_eq, and_comm (a := p ∉ φ.negative s)]

/-- For atomic propositions, the unknown update is empty. -/
theorem unknownUpdate_atom (pred : W → Prop) (s : InfoState W E) :
    unknownUpdate (atom pred) s = ∅ := by
  ext p
  simp only [unknownUpdate, atom, InfoState.update, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hpos hneg
  by_cases h : pred p.world
  · exact hpos hp h
  · exact hneg hp h

/--
Assertability condition: φ is assertable at context c iff the unknown
update is empty — every possibility is accounted for by either the
positive or negative update.

Definition (54) of [elliott-sudo-2025].
-/
def assertable (φ : BilateralDen W E) (c : InfoState W E) : Prop :=
  unknownUpdate φ c = ∅

/-- Every possibility in s is either verified, falsified, or unknown.
    This is the partition property of the Strong Kleene truth table. -/
theorem partition (φ : BilateralDen W E) (s : InfoState W E) :
    s ⊆ φ.positive s ∪ φ.negative s ∪ unknownUpdate φ s := by
  intro p hp
  by_cases h1 : p ∈ φ.positive s
  · exact Set.mem_union_left _ (Set.mem_union_left _ h1)
  · by_cases h2 : p ∈ φ.negative s
    · exact Set.mem_union_left _ (Set.mem_union_right _ h2)
    · exact Set.mem_union_right _ ⟨hp, h1, h2⟩

/-- Assertability implies the positive and negative updates cover the state. -/
theorem partition_assertable (φ : BilateralDen W E) (s : InfoState W E)
    (h : assertable φ s) : s ⊆ φ.positive s ∪ φ.negative s := by
  intro p hp
  have hmem := partition φ s hp
  rcases hmem with (hp' | hp') | hp'
  · exact Set.mem_union_left _ hp'
  · exact Set.mem_union_right _ hp'
  · exfalso
    have hempty : unknownUpdate φ s = ∅ := h
    rw [hempty] at hp'
    exact hp'


/--
Conjunction: sequence positive updates, combine negative updates
following the Strong Kleene truth table.

For conjunction φ ∧ ψ:
- s[φ ∧ ψ]⁺ = s[φ]⁺[ψ]⁺ (the (1,1) cell: both verified)
- s[φ ∧ ψ]⁻ = s[φ]⁻                    (the (0,*) row: φ falsified)
             ∪ s[φ]⁺[ψ]⁻              (the (1,0) cell: φ verified, ψ falsified)
             ∪ s[φ]?[ψ]⁻              (the (#,0) cell: φ unknown, ψ falsified)

Equation (61) of [elliott-sudo-2025].
-/
def conj (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s => ψ.positive (φ.positive s)
  , negative := λ s => φ.negative s
      ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative (φ.unknownUpdate s) }

/-- Notation for conjunction -/
infixl:65 " ⊙ " => conj

/-- Conjunction associates (for positive updates) -/
theorem conj_assoc_positive (φ ψ χ : BilateralDen W E) (s : InfoState W E) :
    ((φ ⊙ ψ) ⊙ χ).positive s = (φ ⊙ (ψ ⊙ χ)).positive s := by
  simp only [conj]


/--
Standard disjunction: dynamic Strong Kleene semantics.

For disjunction φ ∨ ψ, the positive update covers two verification routes:

- **Verification via φ**: s[φ]⁺ (φ is true, ψ is anything)
- **Verification via ψ**: s[φ]⁻[ψ]⁺ ∪ s[φ]?[ψ]⁺ (φ is false or unknown, ψ is true)

The negative update is sequential: s[φ ∨ ψ]⁻ = s[φ]⁻[ψ]⁻ (both must be
denied in sequence, passing state dynamically).

The dynamic state-passing in the positive update is what makes bathroom
disjunctions work: s[¬∃xP(x)]⁻[Q(x)]⁺ = s[∃xP(x)]⁺[Q(x)]⁺ (by DNE),
introducing the discourse referent x for cross-disjunct anaphora.

Equations (64)/(67) of [elliott-sudo-2025].
-/
def disj (φ ψ : BilateralDen W E) : BilateralDen W E :=
  { positive := λ s =>
      φ.positive s                           -- verification via φ
      ∪ ψ.positive (φ.negative s)            -- verification via ψ (φ false)
      ∪ ψ.positive (φ.unknownUpdate s)       -- verification via ψ (φ unknown)
  , negative := λ s =>
      ψ.negative (φ.negative s)              -- sequential denial
  }

/-- Notation for disjunction -/
infixl:60 " ⊕ " => disj

/-- De Morgan: ¬(φ ∨ ψ) = ¬φ ∧ ¬ψ (positive dimension). -/
theorem de_morgan_disj (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (~(φ ⊕ ψ)).positive s = (conj (~φ) (~ψ)).positive s := by
  simp only [neg, disj, conj]

/-- De Morgan: ¬(φ ∧ ψ) = ¬φ ∨ ¬ψ (positive dimension). -/
theorem de_morgan_conj (φ ψ : BilateralDen W E) (s : InfoState W E) :
    (~(φ ⊙ ψ)).positive s = (disj (~φ) (~ψ)).positive s := by
  unfold neg conj disj unknownUpdate
  congr 1; congr 1
  ext p; simp only [and_comm]


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


/-- Create bilateral from predicate over entities.

The predicate is `Prop`-valued (with per-point `Decidable`), following the
project-wide migration of propositional positions from `Bool` to `Prop`. -/
def pred1 (p : E → W → Prop) [∀ e w, Decidable (p e w)] (t : Nat) : BilateralDen W E :=
  { positive := λ s => { poss ∈ s | p (poss.assignment t) poss.world }
  , negative := λ s => { poss ∈ s | ¬ p (poss.assignment t) poss.world } }

/-- Create bilateral from binary predicate. -/
def pred2 (p : E → E → W → Prop) [∀ e₁ e₂ w, Decidable (p e₁ e₂ w)] (t₁ t₂ : Nat) :
    BilateralDen W E :=
  { positive := λ s => { poss ∈ s | p (poss.assignment t₁) (poss.assignment t₂) poss.world }
  , negative := λ s => { poss ∈ s | ¬ p (poss.assignment t₁) (poss.assignment t₂) poss.world } }

/-- pred1 positive update is monotone. -/
theorem pred1_positive_monotone (p : E → W → Prop) [∀ e w, Decidable (p e w)] (t : Nat) :
    Monotone (pred1 p t).positive (α := InfoState W E) :=
  sep_monotone _

/-- pred1 negative update is monotone. -/
theorem pred1_negative_monotone (p : E → W → Prop) [∀ e w, Decidable (p e w)] (t : Nat) :
    Monotone (pred1 p t).negative (α := InfoState W E) :=
  sep_monotone _

/-- pred1 positive update is eliminative. -/
theorem pred1_positive_eliminative (p : E → W → Prop) [∀ e w, Decidable (p e w)] (t : Nat) :
    IsEliminative (pred1 p t).positive (P := Possibility W E) :=
  sep_eliminative _

/-- pred1 negative update is eliminative. -/
theorem pred1_negative_eliminative (p : E → W → Prop) [∀ e w, Decidable (p e w)] (t : Nat) :
    IsEliminative (pred1 p t).negative (P := Possibility W E) :=
  sep_eliminative _

/-- pred2 positive update is monotone. -/
theorem pred2_positive_monotone (p : E → E → W → Prop) [∀ e₁ e₂ w, Decidable (p e₁ e₂ w)]
    (t₁ t₂ : Nat) :
    Monotone (pred2 p t₁ t₂).positive (α := InfoState W E) :=
  sep_monotone _

/-- pred2 negative update is monotone. -/
theorem pred2_negative_monotone (p : E → E → W → Prop) [∀ e₁ e₂ w, Decidable (p e₁ e₂ w)]
    (t₁ t₂ : Nat) :
    Monotone (pred2 p t₁ t₂).negative (α := InfoState W E) :=
  sep_monotone _

/-- pred2 positive update is eliminative. -/
theorem pred2_positive_eliminative (p : E → E → W → Prop) [∀ e₁ e₂ w, Decidable (p e₁ e₂ w)]
    (t₁ t₂ : Nat) :
    IsEliminative (pred2 p t₁ t₂).positive (P := Possibility W E) :=
  sep_eliminative _

/-- pred2 negative update is eliminative. -/
theorem pred2_negative_eliminative (p : E → E → W → Prop) [∀ e₁ e₂ w, Decidable (p e₁ e₂ w)]
    (t₁ t₂ : Nat) :
    IsEliminative (pred2 p t₁ t₂).negative (P := Possibility W E) :=
  sep_eliminative _


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
    toPair (~~φ) = toPair φ := rfl

/-- Projection: bilateral → unilateral (forgets negative) -/
def toUnilateral (φ : BilateralDen W E) : UnilateralDen W E := φ.positive


instance : InvolutiveNeg (BilateralDen W E) where
  neg := neg
  neg_neg := neg_neg

/-- BUS's `BilateralDen` is itself a paraconsistent bilateral logic
    (`Core.Logic.Bilateral.IsBilateral`): the BilateralDen *value* IS the
    formula; `positive` and `negative` are the field projections; `neg`
    swaps them by definition. Both axioms reduce to `rfl`. -/
theorem isBilateral :
    Core.Logic.Bilateral.IsBilateral
      (Form := BilateralDen W E)
      (Result := InfoState W E → InfoState W E)
      (·.positive) (·.negative) neg where
  positive_negate _ := rfl
  negative_negate _ := rfl


-- ============================================================================
-- Order-theoretic structure
-- ============================================================================

/--
Pointwise partial order on bilateral denotations: φ ≤ ψ iff both
`φ.positive s ⊆ ψ.positive s` and `φ.negative s ⊆ ψ.negative s` for all s.
-/
instance : PartialOrder (BilateralDen W E) where
  le φ ψ := (∀ s, φ.positive s ≤ ψ.positive s) ∧ (∀ s, φ.negative s ≤ ψ.negative s)
  le_refl _ := ⟨λ _ => le_refl _, λ _ => le_refl _⟩
  le_trans _ _ _ h1 h2 :=
    ⟨λ s => le_trans (h1.1 s) (h2.1 s), λ s => le_trans (h1.2 s) (h2.2 s)⟩
  le_antisymm _ _ h1 h2 := BilateralDen.ext
    (funext λ s => le_antisymm (h1.1 s) (h2.1 s))
    (funext λ s => le_antisymm (h1.2 s) (h2.2 s))

/-- Negation is monotone: swapping dimensions preserves the pointwise order.
    `~φ ≤ ~ψ ↔ φ ≤ ψ` because the pointwise order checks both components
    independently, and swap just rearranges them. -/
theorem neg_monotone : Monotone (neg : BilateralDen W E → BilateralDen W E) := by
  intro φ ψ ⟨hp, hn⟩
  show (∀ s, φ.negative s ≤ ψ.negative s) ∧ (∀ s, φ.positive s ≤ ψ.positive s)
  exact ⟨hn, hp⟩

/-- Negation reflects and preserves order: ~φ ≤ ~ψ ↔ φ ≤ ψ. -/
theorem neg_le_neg_iff (φ ψ : BilateralDen W E) : ~φ ≤ ~ψ ↔ φ ≤ ψ := by
  constructor
  · intro h
    show (∀ s, φ.positive s ≤ ψ.positive s) ∧ (∀ s, φ.negative s ≤ ψ.negative s)
    exact ⟨h.2, h.1⟩
  · intro ⟨hp, hn⟩
    show (∀ s, φ.negative s ≤ ψ.negative s) ∧ (∀ s, φ.positive s ≤ ψ.positive s)
    exact ⟨hn, hp⟩

end BilateralDen


end Semantics.Dynamic.Core
