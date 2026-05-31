import Linglib.Syntax.CCG.Basic
import Linglib.Syntax.CCG.Interface
import Linglib.Core.Logic.Intensional.Frame

/-!
# Semantic Equivalence and Spurious Ambiguity

CCG derivations fall into equivalence classes: multiple derivations yield identical
interpretations due to the associativity of functional composition. This is sometimes
called "spurious ambiguity" — but it's not really ambiguity, since all derivations in an
equivalence class have the same meaning.

## Key concepts

1. **Semantic equivalence** — two derivations are equivalent iff they have the same
   category and the same meaning.
2. **Source of equivalence** — the `B` combinator is associative
   (`B (B f g) h = B f (B g h)`), so `(f ∘ g) ∘ h = f ∘ (g ∘ h)` in the semantics.
3. **Equivalence classes** — for a string of `n` words there are `Catalan(n-1)` binary
   bracketings, all yielding the same meaning if built purely from composition.
4. **Processing** — a parser need only find one derivation per equivalence class.
-/

namespace CCG.Equivalence

open CCG
open Combinator (B T)
open Core.Logic.Intensional

-- Semantic Equivalence

/--
Two derivations are semantically equivalent iff they span the same substring,
have the same category, and have the same meaning.

This defines equivalence for "spurious ambiguity" analysis.
-/
structure DerivEquiv (F : Frame) where
  /-- First derivation's category -/
  cat : Cat
  /-- First derivation's meaning -/
  meaning₁ : F.Denot (catToTy cat)
  /-- Second derivation's meaning -/
  meaning₂ : F.Denot (catToTy cat)
  /-- The meanings are equal -/
  meanings_eq : meaning₁ = meaning₂

/--
Semantic equivalence for category-meaning pairs.
-/
def semanticallyEquivalent {F : Frame} (cm₁ cm₂ : Σ c : Cat, F.Denot (catToTy c)) : Prop :=
  ∃ (h : cm₁.1 = cm₂.1), h ▸ cm₁.2 = cm₂.2

/--
Semantic equivalence is reflexive.
-/
theorem sem_equiv_refl {F : Frame} (cm : Σ c : Cat, F.Denot (catToTy c)) :
    semanticallyEquivalent cm cm := by
  use rfl

/--
Semantic equivalence is symmetric.
-/
theorem sem_equiv_symm {F : Frame} (cm₁ cm₂ : Σ c : Cat, F.Denot (catToTy c)) :
    semanticallyEquivalent cm₁ cm₂ → semanticallyEquivalent cm₂ cm₁ := λ ⟨h, eq⟩ =>
  match cm₁, cm₂, h, eq with
  | ⟨_c, _m₁⟩, ⟨_, _m₂⟩, rfl, eq => ⟨rfl, eq.symm⟩

/--
Semantic equivalence is transitive.
-/
theorem sem_equiv_trans {F : Frame} (cm₁ cm₂ cm₃ : Σ c : Cat, F.Denot (catToTy c)) :
    semanticallyEquivalent cm₁ cm₂ → semanticallyEquivalent cm₂ cm₃ →
    semanticallyEquivalent cm₁ cm₃ := λ ⟨h₁, eq₁⟩ ⟨h₂, eq₂⟩ =>
  match cm₁, cm₂, cm₃, h₁, eq₁, h₂, eq₂ with
  | ⟨_c, _m₁⟩, ⟨_, _m₂⟩, ⟨_, _m₃⟩, rfl, eq₁, rfl, eq₂ => ⟨rfl, eq₁.trans eq₂⟩

-- Associativity of Composition: The Source of Spurious Ambiguity

/-
The B combinator (composition) is associative:

  B (B f g) h = B f (B g h)

Proof:
  B (B f g) h x = (B f g) (h x) = f (g (h x))
  B f (B g h) x = f ((B g h) x) = f (g (h x))

This means that different derivation trees built purely from composition
will have the same semantic result.
-/

/--
B (composition) is associative: (f ∘ g) ∘ h = f ∘ (g ∘ h)
-/
theorem B_assoc {α β γ δ : Type} (f : γ → δ) (g : β → γ) (h : α → β) :
    B (B f g) h = B f (B g h) := by
  ext x
  rfl

/--
Associativity stated pointwise.
-/
theorem B_assoc_apply {α β γ δ : Type} (f : γ → δ) (g : β → γ) (h : α → β) (x : α) :
    B (B f g) h x = B f (B g h) x := rfl

/--
Consequence: Two ways of composing three functions yield the same result.

This is why "Harry thinks that Anna married" can be derived by:
  1. (Harry ∘ thinks) ∘ (that ∘ (Anna ∘ married))
  2. Harry ∘ (thinks ∘ that) ∘ (Anna ∘ married)
  3. Harry ∘ (thinks ∘ (that ∘ Anna)) ∘ married
... etc.

All yield the same predicate-argument structure.
-/
theorem composition_order_irrelevant {α β γ δ : Type}
    (f : γ → δ) (g : β → γ) (h : α → β) (x : α) :
    f (g (h x)) = B f (B g h) x := rfl


-- Equivalence Classes and Normal Forms

/-
## Normal Form Parsing

To avoid computing redundant derivations, parsers can use "normal forms":
derivation strategies that select exactly one representative from each
equivalence class.

Common approaches:
1. Leftmost composition: Always compose left-to-right
2. Eisner normal form: Constraints on when composition applies

If only one derivation per equivalence class is needed, constraints can
eliminate the others without losing coverage.
-/

-- Matching Entry Test

/-
## Chart Parsing with Equivalence Check

In chart parsing for CCG, when we build a new constituent, we check if an
equivalent entry already exists in the chart. If so, we don't add it.

@cite{karttunen-1989} proposes a subsumption strategy: every potential new edge
is tested against existing chart entries spanning the same region.
@cite{pareschi-steedman-1987} propose a "lazy chart parser" that avoids computing
equivalent analyses by adopting a reduce-first parsing strategy.

The matching entry test checks:
1. Same span (positions i, j in the string)
2. Same category
3. Same predicate-argument structure (meaning)

Checking (3) requires unification or equality testing on semantic structures.
-/

/--
A chart entry: category + meaning for a span.
-/
structure ChartEntry (F : Frame) where
  leftPos : Nat
  rightPos : Nat
  cat : Cat
  meaning : F.Denot (catToTy cat)

/--
Two chart entries match if they have the same span, category, and meaning.
-/
def chartEntriesMatch {F : Frame} (e₁ e₂ : ChartEntry F) : Prop :=
  e₁.leftPos = e₂.leftPos ∧
  e₁.rightPos = e₂.rightPos ∧
  ∃ (h : e₁.cat = e₂.cat), h ▸ e₁.meaning = e₂.meaning

/--
The matching relation is decidable for categories (not meanings in general).
-/
def chartEntriesSameCat {F : Frame} (e₁ e₂ : ChartEntry F) : Bool :=
  e₁.leftPos == e₂.leftPos &&
  e₁.rightPos == e₂.rightPos &&
  e₁.cat == e₂.cat

-- Why "Spurious" Ambiguity Isn't Ambiguity

/-
## Spurious vs Real Ambiguity

Spurious ambiguity: Different derivations, same meaning
  - "Harry thinks Anna married Manny" has many derivations
  - All yield: thinks'(married'(manny')(anna'))(harry')

Real ambiguity: Different derivations, different meanings
  - "Flying planes can be dangerous" has two readings
  - Gerund: Being the pilot of planes is dangerous
  - Adjective: Planes that are flying are dangerous

Only real ambiguity matters for interpretation. Spurious ambiguity is a
parsing problem, not a semantic one.

CCG's flexibility in derivation does not increase semantic ambiguity;
it provides more paths to the same meanings.
-/

/--
An equivalence class of derivations: all have the same meaning.
-/
structure EquivalenceClass (F : Frame) where
  cat : Cat
  meaning : F.Denot (catToTy cat)
  -- In a full implementation, would track the set of derivations

/--
Real ambiguity: multiple equivalence classes for the same string.
-/
def reallyAmbiguous {F : Frame} (classes : List (EquivalenceClass F)) : Prop :=
  classes.length > 1

/--
Spuriously ambiguous: multiple derivations but only one equivalence class.
-/
def spuriouslyAmbiguous {F : Frame} (derivCount : Nat) (classes : List (EquivalenceClass F)) : Prop :=
  derivCount > 1 ∧ classes.length = 1

end CCG.Equivalence
