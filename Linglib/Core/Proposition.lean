/-
# Propositions as World-Dependent Truth Values

Theory-neutral infrastructure for modeling propositions in formal semantics.

## Two Flavors

1. **Prop' W** — Propositions as sets of worlds (W → Prop)
   - Standard in formal semantics literature (Montague, Heim & Kratzer)
   - Natural for existential/universal statements in proofs
   - Use for: NeoGricean exhaustivity, theoretical semantics

2. **BProp W** — Decidable propositions (W → Bool)
   - Needed for computation (probability, enumeration)
   - Works with `native_decide`, `DecidableEq`
   - Use for: RSA, decidable entailment checking

## Coercion

BProp coerces to Prop' via `p w = true`, so you can use decidable
propositions wherever classical ones are expected.

## References

- Montague (1973). The proper treatment of quantification in ordinary English.
- Lewis (1986). On the Plurality of Worlds.
- Heim & Kratzer (1998). Semantics in Generative Grammar.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Monotone.Basic

namespace Core.Proposition

-- ============================================================================
-- The Two Proposition Types
-- ============================================================================

/-- Classical propositions: sets of worlds (standard formal semantics)

In the formal semantics tradition, a proposition is identified with the
set of possible worlds where it is true. This type captures that:
`Prop' W` is a function assigning to each world `w : W` a truth value
(as a Lean `Prop`).
-/
abbrev Prop' (W : Type*) := W → Prop

/-- Decidable propositions: for computation

Like `Prop'`, but with `Bool` instead of `Prop`. This enables:
- Decidable equality and entailment checking
- Use with `native_decide`
- Probability computations (RSA)
-/
abbrev BProp (W : Type*) := W → Bool

/-- Coercion from decidable to classical propositions -/
instance bpropToProp' (W : Type*) : Coe (BProp W) (Prop' W) where
  coe p := λ w => p w = true

-- ============================================================================
-- Operations on Prop' (Classical)
-- ============================================================================

namespace Classical

/-- Propositional negation -/
def pnot (W : Type*) (p : Prop' W) : Prop' W := λ w => ¬(p w)

/-- Propositional conjunction -/
def pand (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w ∧ q w

/-- Propositional disjunction -/
def por (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w ∨ q w

/-- Propositional implication -/
def pimp (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w → q w

/-- Semantic entailment: p entails q iff q is true whenever p is true -/
def entails (W : Type*) (p q : Prop' W) : Prop := ∀ w, p w → q w

/-- Propositional equivalence -/
def equiv (W : Type*) (p q : Prop' W) : Prop := entails W p q ∧ entails W q p

/-- Grand conjunction: true at w iff all propositions in X are true at w -/
def bigConj (W : Type*) (X : Set (Prop' W)) : Prop' W := λ w => ∀ φ ∈ X, φ w

/-- Grand disjunction: true at w iff some proposition in X is true at w -/
def bigDisj (W : Type*) (X : Set (Prop' W)) : Prop' W := λ w => ∃ φ ∈ X, φ w

/-- Consistency: some world satisfies all propositions in X -/
def consistent (W : Type*) (X : Set (Prop' W)) : Prop := ∃ w, ∀ φ ∈ X, φ w

/-- The always-true proposition -/
def top (W : Type*) : Prop' W := λ _ => True

/-- The always-false proposition -/
def bot (W : Type*) : Prop' W := λ _ => False

-- Basic theorems

theorem entails_refl (W : Type*) (p : Prop' W) : entails W p p := λ_ h => h

theorem entails_trans (W : Type*) (p q r : Prop' W)
    (hpq : entails W p q) (hqr : entails W q r) : entails W p r :=
  λw hp => hqr w (hpq w hp)

theorem equiv_refl (W : Type*) (p : Prop' W) : equiv W p p :=
  ⟨entails_refl W p, entails_refl W p⟩

theorem equiv_symm (W : Type*) (p q : Prop' W) (h : equiv W p q) : equiv W q p :=
  ⟨h.2, h.1⟩

theorem pnot_pnot (W : Type*) (p : Prop' W) : entails W p (pnot W (pnot W p)) :=
  λ_ hp hnp => hnp hp

-- ============================================================================
-- BooleanAlgebra Correspondence
-- ============================================================================

/-
Prop' W = W → Prop inherits BooleanAlgebra from Mathlib's Pi instance:
  Pi.instBooleanAlgebra + Prop.instBooleanAlgebraProp

Our operations correspond exactly to the algebraic operations:
  pand  ↔  ⊓ (inf)
  por   ↔  ⊔ (sup)
  pnot  ↔  ᶜ (compl)
  entails ↔ ≤
-/

/-- Conjunction equals infimum in the lattice -/
theorem pand_eq_inf (W : Type*) (p q : Prop' W) : pand W p q = p ⊓ q := rfl

/-- Disjunction equals supremum in the lattice -/
theorem por_eq_sup (W : Type*) (p q : Prop' W) : por W p q = p ⊔ q := rfl

/-- Negation equals complement in the Boolean algebra -/
theorem pnot_eq_compl (W : Type*) (p : Prop' W) : pnot W p = pᶜ := rfl

/-- Entailment equals the lattice ordering -/
theorem entails_eq_le (W : Type*) (p q : Prop' W) : entails W p q ↔ p ≤ q := Iff.rfl

/-- Top equals lattice top -/
theorem top_eq_latticeTop (W : Type*) : top W = (⊤ : Prop' W) := rfl

/-- Bot equals lattice bot -/
theorem bot_eq_latticeBot (W : Type*) : bot W = (⊥ : Prop' W) := rfl

end Classical

-- ============================================================================
-- Operations on BProp (Decidable)
-- ============================================================================

namespace Decidable

/-- Propositional negation -/
def pnot (W : Type*) (p : BProp W) : BProp W := λ w => !p w

/-- Propositional conjunction -/
def pand (W : Type*) (p q : BProp W) : BProp W := λ w => p w && q w

/-- Propositional disjunction -/
def por (W : Type*) (p q : BProp W) : BProp W := λ w => p w || q w

/-- The always-true proposition -/
def top (W : Type*) : BProp W := λ _ => true

/-- The always-false proposition -/
def bot (W : Type*) : BProp W := λ _ => false

/-- Decidable entailment given explicit world enumeration -/
def entails (W : Type*) (worlds : List W) (p q : BProp W) : Bool :=
  worlds.all λ w => !p w || q w

/-- Decidable equivalence given explicit world enumeration -/
def equiv (W : Type*) (worlds : List W) (p q : BProp W) : Bool :=
  entails W worlds p q && entails W worlds q p

/-- Decidable consistency: is there a world satisfying all propositions? -/
def consistent (W : Type*) (worlds : List W) (ps : List (BProp W)) : Bool :=
  worlds.any λ w => ps.all λp => p w

/-- Count worlds satisfying a proposition -/
def count (W : Type*) (worlds : List W) (p : BProp W) : Nat :=
  worlds.filter p |>.length

/-- Get all worlds satisfying a proposition -/
def filter (W : Type*) (worlds : List W) (p : BProp W) : List W :=
  worlds.filter p

-- ============================================================================
-- BooleanAlgebra Correspondence for Bool
-- ============================================================================

/-
BProp W = W → Bool also inherits BooleanAlgebra from:
  Pi.instBooleanAlgebra + Bool.instBooleanAlgebraBool
-/

/-- Conjunction equals infimum in the Bool lattice -/
theorem pand_eq_inf (W : Type*) (p q : BProp W) : pand W p q = p ⊓ q := rfl

/-- Disjunction equals supremum in the Bool lattice -/
theorem por_eq_sup (W : Type*) (p q : BProp W) : por W p q = p ⊔ q := rfl

/-- Negation equals complement in the Bool Boolean algebra -/
theorem pnot_eq_compl (W : Type*) (p : BProp W) : pnot W p = pᶜ := rfl

/-- Top equals lattice top -/
theorem top_eq_latticeTop (W : Type*) : top W = (⊤ : BProp W) := rfl

/-- Bot equals lattice bot -/
theorem bot_eq_latticeBot (W : Type*) : bot W = (⊥ : BProp W) := rfl

end Decidable

-- ============================================================================
-- Notation
-- ============================================================================

-- We use scoped notation so users can choose which to import
-- Note: notation needs to work without explicit W parameter

namespace ClassicalNotation
  scoped prefix:75 "∼" => λp => Classical.pnot _ p
  scoped infixl:65 " ∧ₚ " => λp q => Classical.pand _ p q
  scoped infixl:60 " ∨ₚ " => λp q => Classical.por _ p q
  scoped infixr:55 " →ₚ " => λp q => Classical.pimp _ p q
  scoped notation:50 p " ⊆ₚ " q => Classical.entails _ p q
  scoped notation:50 p " ≡ₚ " q => Classical.equiv _ p q
  scoped notation "⋀" => λX => Classical.bigConj _ X
  scoped notation "⋁" => λX => Classical.bigDisj _ X
end ClassicalNotation

namespace DecidableNotation
  scoped prefix:75 "∼ᵇ" => λp => Decidable.pnot _ p
  scoped infixl:65 " ∧ᵇ " => λp q => Decidable.pand _ p q
  scoped infixl:60 " ∨ᵇ " => λp q => Decidable.por _ p q
end DecidableNotation

-- ============================================================================
-- Finite Worlds Typeclass
-- ============================================================================

/-- Typeclass for types with a complete enumeration of all elements.

This enables decidable operations on propositions without
explicitly passing the world list everywhere.
-/
class FiniteWorlds (W : Type*) where
  /-- List of all worlds -/
  worlds : List W
  /-- The list is complete -/
  complete : ∀ w : W, w ∈ worlds

namespace FiniteWorlds

/-- Decidable entailment using the FiniteWorlds instance -/
def entails (W : Type*) [FiniteWorlds W] (p q : BProp W) : Bool :=
  Decidable.entails W (FiniteWorlds.worlds) p q

/-- Decidable equivalence using the FiniteWorlds instance -/
def equiv (W : Type*) [FiniteWorlds W] (p q : BProp W) : Bool :=
  Decidable.equiv W (FiniteWorlds.worlds) p q

/-- Decidable consistency using the FiniteWorlds instance -/
def consistent (W : Type*) [FiniteWorlds W] (ps : List (BProp W)) : Bool :=
  Decidable.consistent W (FiniteWorlds.worlds) ps

/-- Count satisfying worlds -/
def count (W : Type*) [FiniteWorlds W] (p : BProp W) : Nat :=
  Decidable.count W (FiniteWorlds.worlds) p

/-- Filter satisfying worlds -/
def filter (W : Type*) [FiniteWorlds W] (p : BProp W) : List W :=
  Decidable.filter W (FiniteWorlds.worlds) p

end FiniteWorlds

-- ============================================================================
-- Soundness: Decidable operations agree with Classical
-- ============================================================================

/-- Decidable entailment is sound w.r.t. classical entailment -/
theorem entails_sound (W : Type*) [FiniteWorlds W] (p q : BProp W) :
    FiniteWorlds.entails W p q = true → Classical.entails W (↑p : Prop' W) ↑q := by
  intro h w hp
  simp only [FiniteWorlds.entails, Decidable.entails, List.all_eq_true] at h
  have hw := FiniteWorlds.complete w
  have := h w hw
  simp only [Bool.not_eq_true', Bool.or_eq_true] at this
  cases this with
  | inl hpf => simp_all
  | inr hqt => exact hqt

-- ============================================================================
-- Common World Types
-- ============================================================================

/-- A simple 4-world type for basic examples -/
inductive World4 where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr, Inhabited

instance : FiniteWorlds World4 where
  worlds := [.w0, .w1, .w2, .w3]
  complete := λ w => by cases w <;> simp

/-- A simple 2-world type (true/false worlds) -/
inductive World2 where
  | wT | wF
  deriving DecidableEq, BEq, Repr, Inhabited

instance : FiniteWorlds World2 where
  worlds := [.wT, .wF]
  complete := λ w => by cases w <;> simp

end Core.Proposition
