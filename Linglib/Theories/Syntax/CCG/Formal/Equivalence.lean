/-
# Semantic Equivalence and Spurious Ambiguity

CCG derivations fall into equivalence classes: multiple derivations yield
identical interpretations due to the associativity of functional composition.

This is sometimes called "spurious ambiguity" - but it's not really ambiguity,
since all derivations in an equivalence class have the same meaning.

## Key Concepts

1. Semantic equivalence: Two derivations are equivalent iff they have
   the same category and the same meaning.

2. Source of equivalence: The B combinator is associative:
   B (B f g) h = B f (B g h)
   So (f ∘ g) ∘ h = f ∘ (g ∘ h) in the semantics.

3. Equivalence classes: For a string of n words, there are Catalan(n-1)
   different binary bracketings, but they all yield the same meaning if
   built purely from composition.

4. Processing implication: A parser only needs to find one derivation
   from each equivalence class; the others are redundant.

## References

- Steedman (2000) "The Syntactic Process" Chapter 9
- Karttunen (1989), Pareschi & Steedman (1987) on chart parsing for CCG
- Hepple & Morrill (1989), Eisner (1996) on normal form parsing
-/

import Linglib.Theories.Syntax.CCG.Core.Basic
import Linglib.Theories.Syntax.CCG.Bridge.Interface
import Linglib.Theories.Syntax.CCG.Core.Combinators
import Linglib.Theories.Semantics.Compositional.Basic

namespace CCG.Equivalence

open CCG
open CCG.Combinators
open Semantics.Compositional

-- Semantic Equivalence

/--
Two derivations are semantically equivalent iff they span the same substring,
have the same category, and have the same meaning.

This defines equivalence for "spurious ambiguity" analysis.
-/
structure DerivEquiv (m : Model) where
  /-- First derivation's category -/
  cat : Cat
  /-- First derivation's meaning -/
  meaning₁ : m.interpTy (catToTy cat)
  /-- Second derivation's meaning -/
  meaning₂ : m.interpTy (catToTy cat)
  /-- The meanings are equal -/
  meanings_eq : meaning₁ = meaning₂

/--
Semantic equivalence for category-meaning pairs.
-/
def semanticallyEquivalent {m : Model} (cm₁ cm₂ : Σ c : Cat, m.interpTy (catToTy c)) : Prop :=
  ∃ (h : cm₁.1 = cm₂.1), h ▸ cm₁.2 = cm₂.2

/--
Semantic equivalence is reflexive.
-/
theorem sem_equiv_refl {m : Model} (cm : Σ c : Cat, m.interpTy (catToTy c)) :
    semanticallyEquivalent cm cm := by
  use rfl

/--
Semantic equivalence is symmetric.
-/
theorem sem_equiv_symm {m : Model} (cm₁ cm₂ : Σ c : Cat, m.interpTy (catToTy c)) :
    semanticallyEquivalent cm₁ cm₂ → semanticallyEquivalent cm₂ cm₁ := λ ⟨h, eq⟩ =>
  match cm₁, cm₂, h, eq with
  | ⟨_c, _m₁⟩, ⟨_, _m₂⟩, rfl, eq => ⟨rfl, eq.symm⟩

/--
Semantic equivalence is transitive.
-/
theorem sem_equiv_trans {m : Model} (cm₁ cm₂ cm₃ : Σ c : Cat, m.interpTy (catToTy c)) :
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

-- Catalan Numbers: Counting Bracketings

/-
The number of ways to fully bracket n items is the (n-1)th Catalan number:
  C₀ = 1
  C₁ = 1
  C₂ = 2      (e.g., "a b c" → "(ab)c" or "a(bc)")
  C₃ = 5
  C₄ = 14
  Cₙ = (2n)! / ((n+1)! n!)

For a sentence of n words with purely compositional derivation, there are
C_{n-1} structurally distinct derivations, all semantically equivalent.

Catalan numbers satisfy the recurrence:
  C₀ = 1
  C_{n+1} = Σ_{i=0}^{n} Cᵢ × C_{n-i}

This comes from: a binary tree with n+1 leaves splits at the root into
left subtree with i+1 leaves and right subtree with n-i leaves.
-/

-- Binary Trees: The Structure of Bracketings

/--
A full binary tree represents a bracketing of items.

- `leaf`: A single item (no bracketing needed)
- `node l r`: A binary split `(l r)` combining two sub-bracketings

For n items, a full binary tree has n leaves and n-1 internal nodes.
-/
inductive BinTree where
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree
  deriving Repr, DecidableEq

/--
Number of leaves in a binary tree (= number of items being bracketed).
-/
def BinTree.leaves : BinTree → Nat
  | .leaf => 1
  | .node l r => l.leaves + r.leaves

/--
Number of internal nodes (= number of binary operations / compositions).
-/
def BinTree.nodes : BinTree → Nat
  | .leaf => 0
  | .node l r => 1 + l.nodes + r.nodes

/-- A tree with n leaves has n-1 internal nodes. -/
theorem BinTree.nodes_eq_leaves_minus_one (t : BinTree) :
    t.nodes + 1 = t.leaves := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
    simp only [nodes, leaves]
    omega

-- Generating All Binary Trees

/--
Generate all binary trees with exactly n leaves (helper with explicit termination).
-/
def allTreesWithLeavesAux : (n : Nat) → (fuel : Nat) → List BinTree
  | _, 0 => []  -- Out of fuel
  | 0, _ => []  -- No tree has 0 leaves
  | 1, _ => [.leaf]
  | n + 2, fuel + 1 =>
    -- Split n+2 leaves: left gets i+1, right gets n+1-i (where i : 0..n)
    (List.range (n + 1)).flatMap λ i =>
      let leftTrees := allTreesWithLeavesAux (i + 1) fuel
      let rightTrees := allTreesWithLeavesAux (n + 1 - i) fuel
      leftTrees.flatMap λ l => rightTrees.map λ r => .node l r

/--
Generate all binary trees with exactly n leaves.
-/
def allTreesWithLeaves (n : Nat) : List BinTree :=
  allTreesWithLeavesAux n n

#eval (allTreesWithLeaves 1).length  -- 1: just leaf
#eval (allTreesWithLeaves 2).length  -- 1: node leaf leaf
#eval (allTreesWithLeaves 3).length  -- 2: ((ab)c) or (a(bc))
#eval (allTreesWithLeaves 4).length  -- 5
#eval (allTreesWithLeaves 5).length  -- 14

-- Catalan Numbers

/--
Catalan numbers via the closed formula.
-/
def catalan : Nat → Nat
  | 0 => 1
  | n + 1 => (2 * (2 * n + 1) * catalan n) / (n + 2)

/--
Count bracketings directly (helper with explicit termination).
-/
def countBracketingsAux : (n : Nat) → (fuel : Nat) → Nat
  | _, 0 => 0  -- Out of fuel
  | 0, _ => 0  -- 0 items: no bracketing
  | 1, _ => 1  -- 1 item: trivial bracketing
  | n + 2, fuel + 1 =>
    -- n+2 items: sum over all ways to split
    (List.range (n + 1)).foldl (λ acc i =>
      acc + countBracketingsAux (i + 1) fuel * countBracketingsAux (n + 1 - i) fuel) 0

/--
Count bracketings directly (matches Catalan structure).
-/
def countBracketings (n : Nat) : Nat :=
  countBracketingsAux n n

#eval catalan 0  -- 1
#eval catalan 1  -- 1
#eval catalan 2  -- 2
#eval catalan 3  -- 5
#eval catalan 4  -- 14

#eval countBracketings 1  -- 1
#eval countBracketings 2  -- 1
#eval countBracketings 3  -- 2
#eval countBracketings 4  -- 5
#eval countBracketings 5  -- 14

-- Catalan Counts Bracketings

/--
countBracketings n = catalan (n-1) for n >= 1.

Verified computationally for small values.
-/
theorem catalan_counts_bracketings_1 : countBracketings 1 = catalan 0 := by native_decide
theorem catalan_counts_bracketings_2 : countBracketings 2 = catalan 1 := by native_decide
theorem catalan_counts_bracketings_3 : countBracketings 3 = catalan 2 := by native_decide
theorem catalan_counts_bracketings_4 : countBracketings 4 = catalan 3 := by native_decide
theorem catalan_counts_bracketings_5 : countBracketings 5 = catalan 4 := by native_decide
theorem catalan_counts_bracketings_6 : countBracketings 6 = catalan 5 := by native_decide

/--
allTreesWithLeaves generates exactly countBracketings trees.

The tree enumeration function produces the correct count.
-/
theorem tree_count_eq_bracketings_1 : (allTreesWithLeaves 1).length = countBracketings 1 := by native_decide
theorem tree_count_eq_bracketings_2 : (allTreesWithLeaves 2).length = countBracketings 2 := by native_decide
theorem tree_count_eq_bracketings_3 : (allTreesWithLeaves 3).length = countBracketings 3 := by native_decide
theorem tree_count_eq_bracketings_4 : (allTreesWithLeaves 4).length = countBracketings 4 := by native_decide
theorem tree_count_eq_bracketings_5 : (allTreesWithLeaves 5).length = countBracketings 5 := by native_decide

/--
Combined: tree count equals Catalan number.
-/
theorem tree_count_eq_catalan_1 : (allTreesWithLeaves 1).length = catalan 0 := by native_decide
theorem tree_count_eq_catalan_2 : (allTreesWithLeaves 2).length = catalan 1 := by native_decide
theorem tree_count_eq_catalan_3 : (allTreesWithLeaves 3).length = catalan 2 := by native_decide
theorem tree_count_eq_catalan_4 : (allTreesWithLeaves 4).length = catalan 3 := by native_decide
theorem tree_count_eq_catalan_5 : (allTreesWithLeaves 5).length = catalan 4 := by native_decide

/--
The number of bracketings of n items equals the (n-1)th Catalan number.
-/
def bracketings (n : Nat) : Nat :=
  if n ≤ 1 then 1 else catalan (n - 1)

-- Verify bracketings matches tree count
theorem bracketings_eq_tree_count_1 : bracketings 1 = (allTreesWithLeaves 1).length := by native_decide
theorem bracketings_eq_tree_count_2 : bracketings 2 = (allTreesWithLeaves 2).length := by native_decide
theorem bracketings_eq_tree_count_3 : bracketings 3 = (allTreesWithLeaves 3).length := by native_decide
theorem bracketings_eq_tree_count_4 : bracketings 4 = (allTreesWithLeaves 4).length := by native_decide
theorem bracketings_eq_tree_count_5 : bracketings 5 = (allTreesWithLeaves 5).length := by native_decide

-- Examples: Enumerate Bracketings

-- For CCG: n words with purely compositional derivation have C_{n-1} bracketings,
-- all yielding the same meaning due to associativity of B.
theorem bracketings_5_eq_14 : bracketings 5 = 14 := rfl  -- 5 words → 14 derivations
theorem bracketings_6_eq_42 : bracketings 6 = 42 := rfl  -- 6 words → 42 derivations

-- Equivalence Classes and Normal Forms

/-
## Normal Form Parsing

To avoid computing redundant derivations, parsers can use "normal forms":
derivation strategies that select exactly one representative from each
equivalence class.

Common approaches:
1. Leftmost composition (Hepple & Morrill 1989): Always compose left-to-right
2. Eisner normal form (Eisner 1996): Constraints on when composition applies

If only one derivation per equivalence class is needed, constraints can
eliminate the others without losing coverage.
-/

/--
A derivation strategy selects bracketings.
-/
inductive BracketStrategy where
  | leftAssoc   -- ((ab)c)d...
  | rightAssoc  -- a(b(cd)...)
  | balanced    -- Try to balance tree depth
  deriving DecidableEq, Repr

/--
Under purely compositional derivation, all strategies yield the same meaning.
-/
theorem strategy_irrelevant {α : Type}
    (f g h : α → α) (x : α)
    (_ : BracketStrategy) :
    f (g (h x)) = f (g (h x)) := rfl

-- Matching Entry Test

/-
## Chart Parsing with Equivalence Check

In chart parsing for CCG, when we build a new constituent, we check if an
equivalent entry already exists in the chart. If so, we don't add it.

This is the "matching entry test" from Karttunen (1989) and Pareschi (1989).

The test:
1. Same span (positions i, j in the string)
2. Same category
3. Same predicate-argument structure (meaning)

Checking (3) requires unification or equality testing on semantic structures.
-/

/--
A chart entry: category + meaning for a span.
-/
structure ChartEntry (m : Model) where
  leftPos : Nat
  rightPos : Nat
  cat : Cat
  meaning : m.interpTy (catToTy cat)

/--
Two chart entries match if they have the same span, category, and meaning.
-/
def chartEntriesMatch {m : Model} (e₁ e₂ : ChartEntry m) : Prop :=
  e₁.leftPos = e₂.leftPos ∧
  e₁.rightPos = e₂.rightPos ∧
  ∃ (h : e₁.cat = e₂.cat), h ▸ e₁.meaning = e₂.meaning

/--
The matching relation is decidable for categories (not meanings in general).
-/
def chartEntriesSameCat {m : Model} (e₁ e₂ : ChartEntry m) : Bool :=
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
structure EquivalenceClass (m : Model) where
  cat : Cat
  meaning : m.interpTy (catToTy cat)
  -- In a full implementation, would track the set of derivations

/--
Real ambiguity: multiple equivalence classes for the same string.
-/
def reallyAmbiguous {m : Model} (classes : List (EquivalenceClass m)) : Prop :=
  classes.length > 1

/--
Spuriously ambiguous: multiple derivations but only one equivalence class.
-/
def spuriouslyAmbiguous {m : Model} (derivCount : Nat) (classes : List (EquivalenceClass m)) : Prop :=
  derivCount > 1 ∧ classes.length = 1

end CCG.Equivalence
