import Linglib.Theories.Semantics.Comparison.Metalinguistic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

/-!
# Metalinguistic Degrees
@cite{rudolph-kocurek-2024}

Degree-theoretic formulation of metalinguistic gradability (Supplement §C).
The revised semantics (`evalRevised`) induces a degree structure on
sentences: the **metalinguistic degree** of a sentence A (relative to
an index ⟨≤, i, w⟩) is the equivalence class of its denotation set
⟦A⟧_i = {j ≤ i | ⟦A⟧^{j,w} = 1} under a matching relation ∼.

## Key Results

- **∼ is an equivalence relation** (Fact 8): reflexive, symmetric, transitive
- **⊐ is a linear order on degrees** (Fact 12): irreflexive, transitive, total
- **A ≈ B iff deg(A) = deg(B)** (Fact 9): ME = same metalinguistic degree
- **A ≻ B iff deg(A) ⊐ deg(B)** (Fact 10): revised MC = degree ordering

This connects the expressivist framework to a proper algebraic structure
backed by Mathlib's `Setoid`, `Quotient`, and order theory. The metalinguistic
degree construction parallels @cite{klein-1980}'s emergent degrees
(see `Hierarchy.lean:nondistinct_iff_equal_measure`), but operates on
*interpretations* rather than *entities*.
-/

namespace Semantics.Comparison.MetalinguisticDegree

open Semantics.Comparison.Metalinguistic


-- ════════════════════════════════════════════════════════════════
-- § 0. Bridge: SemanticOrdering → Mathlib Preorder
-- ════════════════════════════════════════════════════════════════

/-- Convert a `SemanticOrdering` to a Mathlib `Preorder`.

Wraps the Bool-valued `le` as a Prop-valued `≤`, following the
`QUD.toSetoid` pattern. A `def` (not an instance) to avoid global
instance pollution — use `letI := ord.toPreorder` locally. -/
def SemanticOrdering.toPreorder {I : Type} (ord : SemanticOrdering I) :
    Preorder I where
  le i j := ord.le i j = true
  le_refl i := ord.le_refl i
  le_trans i j k hij hjk := ord.le_trans i j k hij hjk

/-- The semantic ordering is total. -/
theorem SemanticOrdering.isTotal {I : Type} (ord : SemanticOrdering I) :
    ∀ (i j : I), ord.le i j = true ∨ ord.le j i = true :=
  ord.le_total


-- ════════════════════════════════════════════════════════════════
-- § 1. Field and Denotation Sets
-- ════════════════════════════════════════════════════════════════

/-- The field I_i: the set of interpretations ranked at or below i. -/
def field {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) : Finset I :=
  Finset.univ.filter (λ j => ord.le j i)

/-- The denotation of a formula: the set of interpretations in I_i
where the formula is true (under the revised semantics). -/
def denotation {I W Pred Entity : Type} [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) : Finset I :=
  (field ord i).filter (λ j => evalRevised interpFn φ ord j w)

/-- The complement of a set relative to the field I_i. -/
def fieldComplement {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) : Finset I :=
  field ord i \ X


-- ════════════════════════════════════════════════════════════════
-- § 2. The ∼ Equivalence Relation (Supplement §C, p. 9)
-- ════════════════════════════════════════════════════════════════

/-- Condition (i) of the ∼ equivalence: every element of X\Y is
matched by an element of Y\X at least as high, and vice versa.

This is the same as the basic ME matching condition applied to
interpretation sets rather than formulas. -/
def equivCond1 {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  (∀ i' ∈ X \ Y, ∃ i'' ∈ Y \ X, ord.le i' i'' = true) ∧
  (∀ i' ∈ Y \ X, ∃ i'' ∈ X \ Y, ord.le i' i'' = true)

/-- Condition (ii) of the ∼ equivalence: every element of the
symmetric difference (X ∪ Y) \ (X ∩ Y) is dominated by both
an element of X ∩ Y and an element of X̄ ∩ Ȳ (relative to I_i).

This handles the "Figure 1" situation where A ↔ ¬B always holds
at top-ranked interpretations: if every A-or-B-but-not-both
interpretation is matched by both an A∧B and a ¬A∧¬B interpretation. -/
def equivCond2 {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  ∀ i' ∈ (X ∪ Y) \ (X ∩ Y),
    (∃ i'' ∈ X ∩ Y, ord.le i' i'' = true) ∧
    (∃ i'' ∈ field ord i \ (X ∪ Y), ord.le i' i'' = true)

/-- Metalinguistic degree equivalence: X ∼_i Y.

Two interpretation sets have the same metalinguistic degree iff
either (i) their symmetric difference elements are pairwise matched
in rank, or (ii) every unmatched element is dominated by both an
element in the overlap and an element outside both sets.

This mirrors the revised ME truth conditions (Supplement §B) applied
to sets rather than formulas. -/
def degreeEquiv {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  equivCond1 ord i X Y ∨ equivCond2 ord i X Y

/-- Bool-valued decidable version of equivCond1. -/
def equivCond1B {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  decide (∀ i' ∈ X \ Y, ∃ i'' ∈ Y \ X, ord.le i' i'' = true) &&
  decide (∀ i' ∈ Y \ X, ∃ i'' ∈ X \ Y, ord.le i' i'' = true)

/-- Bool-valued decidable version of equivCond2. -/
def equivCond2B {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  decide (∀ i' ∈ (X ∪ Y) \ (X ∩ Y),
    (∃ i'' ∈ X ∩ Y, ord.le i' i'' = true) ∧
    (∃ i'' ∈ field ord i \ (X ∪ Y), ord.le i' i'' = true))

/-- Bool-valued decidable version of degreeEquiv. -/
def degreeEquivB {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  equivCond1B ord i X Y || equivCond2B ord i X Y


-- ════════════════════════════════════════════════════════════════
-- § 3. Fact 8: ∼ is an Equivalence Relation
-- ════════════════════════════════════════════════════════════════

/-- Fact 8a: ∼ is reflexive.
X \ X = ∅, so all conditions are vacuously satisfied. -/
theorem degreeEquiv_refl {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    degreeEquiv ord i X X := by
  left
  constructor <;> intro i' h <;> simp at h

/-- Fact 8b: ∼ is symmetric.
Both conditions are symmetric in X and Y: condition (i) swaps the
two conjuncts, and condition (ii) is invariant under X ↔ Y since
X ∩ Y = Y ∩ X and X ∪ Y = Y ∪ X. -/
theorem degreeEquiv_symm {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y X := by
  intro h
  rcases h with h1 | h2
  · left; exact ⟨h1.2, h1.1⟩
  · right
    intro i' hi'
    have hi'swap : i' ∈ (X ∪ Y) \ (X ∩ Y) := by
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hi' ⊢
      exact ⟨Or.symm hi'.1, λ ⟨h1, h2⟩ => hi'.2 ⟨h2, h1⟩⟩
    obtain ⟨h2a, h2b⟩ := h2 i' hi'swap
    constructor
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2a
      exact ⟨i'', by rwa [Finset.inter_comm] at hi''mem, hi''le⟩
    · obtain ⟨i'', hi''mem, hi''le⟩ := h2b
      exact ⟨i'', by rwa [Finset.union_comm] at hi''mem, hi''le⟩

/-- Fact 8c: ∼ is transitive.
TODO: This requires a nontrivial case analysis paralleling the
proof of Fact 6 (ME transitivity) in Supplement §B. The key idea:
given X ∼ Y (via condition c₁) and Y ∼ Z (via condition c₂), one
shows X ∼ Z by choosing witnesses from the appropriate matching
condition (c₁ or c₂) depending on which applies. -/
theorem degreeEquiv_trans {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I) :
    degreeEquiv ord i X Y → degreeEquiv ord i Y Z →
    degreeEquiv ord i X Z := by
  sorry

/-- The metalinguistic setoid: ∼ as a Mathlib `Setoid` on `Finset I`. -/
def metalinguisticSetoid {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) : Setoid (Finset I) where
  r := degreeEquiv ord i
  iseqv := {
    refl := degreeEquiv_refl ord i
    symm := degreeEquiv_symm ord i _ _
    trans := degreeEquiv_trans ord i _ _ _
  }


-- ════════════════════════════════════════════════════════════════
-- § 4. Metalinguistic Degree Type
-- ════════════════════════════════════════════════════════════════

/-- The type of metalinguistic degrees: equivalence classes of
interpretation sets under ∼.

A metalinguistic degree is a *set of sets of interpretations* —
all the interpretation sets that are "ranked as high" as each other.
The degree of a sentence A is `deg(⟦A⟧_i)`. -/
def MetaDegree (I : Type) [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) :=
  Quotient (metalinguisticSetoid ord i)

/-- Compute the metalinguistic degree of an interpretation set. -/
def deg {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    MetaDegree I ord i :=
  Quotient.mk (metalinguisticSetoid ord i) X

/-- The metalinguistic degree of a formula's denotation. -/
def formulaDeg {I W Pred Entity : Type} [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (φ : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    MetaDegree I ord i :=
  deg ord i (denotation interpFn φ ord i w)


-- ════════════════════════════════════════════════════════════════
-- § 5. The ⊐ Ordering on Sets (Supplement §C, p. 10)
-- ════════════════════════════════════════════════════════════════

/-- X ⊐ Y: interpretation set X is strictly better than Y.

Mirrors the revised MC truth conditions (Supplement §B):
∃ i' ∈ I_i such that i' ∈ X \ Y and either
(a) all elements of X ∩ Y are strictly below i', or
(b) all elements of I_i \ (X ∪ Y) are strictly below i',
and in both cases all elements of Y \ X are strictly below i'. -/
def strictlyBetter {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Prop :=
  ∃ i' ∈ X \ Y,
    i' ∈ field ord i ∧
    (∀ i'' ∈ Y \ X, ord.lt i'' i' = true) ∧
    ((∀ i'' ∈ X ∩ Y, ord.lt i'' i' = true) ∨
     (∀ i'' ∈ field ord i \ (X ∪ Y), ord.lt i'' i' = true))

/-- Bool-valued decidable version of strictlyBetter. -/
def strictlyBetterB {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I)
    (X Y : Finset I) : Bool :=
  decide (∃ i' ∈ X \ Y,
    i' ∈ field ord i ∧
    (∀ i'' ∈ Y \ X, ord.lt i'' i' = true) ∧
    ((∀ i'' ∈ X ∩ Y, ord.lt i'' i' = true) ∨
     (∀ i'' ∈ field ord i \ (X ∪ Y), ord.lt i'' i' = true)))


-- ════════════════════════════════════════════════════════════════
-- § 6. Facts 11–12: ⊐ on Degrees
-- ════════════════════════════════════════════════════════════════

/-- Fact 12a: ⊐ is irreflexive on sets.
i' ∈ X \ X is impossible, so no witness exists. -/
theorem strictlyBetter_irrefl {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I) :
    ¬ strictlyBetter ord i X X := by
  intro ⟨i', hi', _, _, _⟩
  simp at hi'

/-- Fact 11: ⊐ respects ∼ on the right.
TODO: If X ⊐ Y and Y ∼ Z, then X ⊐ Z. Needed for lifting ⊐ to the
quotient via `Quotient.lift₂`. -/
theorem strictlyBetter_respects_right {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I) :
    strictlyBetter ord i X Y → degreeEquiv ord i Y Z →
    strictlyBetter ord i X Z := by
  sorry

/-- Fact 11: ⊐ respects ∼ on the left. -/
theorem strictlyBetter_respects_left {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I) :
    strictlyBetter ord i X Y → degreeEquiv ord i X Z →
    strictlyBetter ord i Z Y := by
  sorry

/-- Fact 12b: ⊐ is transitive on sets.
TODO: Parallels the transitivity proof for the revised MC (Fact 4). -/
theorem strictlyBetter_trans {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y Z : Finset I) :
    strictlyBetter ord i X Y → strictlyBetter ord i Y Z →
    strictlyBetter ord i X Z := by
  sorry

/-- Fact 12c: ⊐ is total on nonequivalent sets.
TODO: For any X, Y ⊆ I_i, either X ∼ Y or X ⊐ Y or Y ⊐ X. -/
theorem strictlyBetter_total {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X Y : Finset I)
    (hX : X ⊆ field ord i) (hY : Y ⊆ field ord i) :
    degreeEquiv ord i X Y ∨ strictlyBetter ord i X Y ∨
    strictlyBetter ord i Y X := by
  sorry


-- ════════════════════════════════════════════════════════════════
-- § 7. Facts 9–10: Correspondence with Revised Semantics
-- ════════════════════════════════════════════════════════════════

/-- Fact 9: ME holds iff denotations have the same degree.
TODO: ⟦A ≈ B⟧^{≤,i,w}_revised = 1 iff ⟦A⟧_i ∼ ⟦B⟧_i.
This connects the Boolean evaluation function `evalRevised` to the
algebraic degree structure. -/
theorem me_iff_same_degree {I W Pred Entity : Type}
    [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    evalRevised interpFn (A.me B) ord i w = true ↔
    degreeEquiv ord i (denotation interpFn A ord i w)
      (denotation interpFn B ord i w) := by
  sorry

/-- Fact 10: revised MC holds iff denotation of A ⊐ denotation of B.
TODO: ⟦A ≻ B⟧^{≤,i,w}_revised = 1 iff ⟦A⟧_i ⊐ ⟦B⟧_i. -/
theorem mc_iff_degree_gt {I W Pred Entity : Type}
    [Fintype I] [DecidableEq I]
    (interpFn : I → Interpretation W Pred Entity)
    (A B : MFormula Pred Entity)
    (ord : SemanticOrdering I) (i : I) (w : W) :
    evalRevised interpFn (.mc A B) ord i w = true ↔
    strictlyBetter ord i (denotation interpFn A ord i w)
      (denotation interpFn B ord i w) := by
  sorry


-- ════════════════════════════════════════════════════════════════
-- § 8. Fact 13: Extremal Degrees
-- ════════════════════════════════════════════════════════════════

/-- Fact 13a: the full field I_i is the maximum degree.
deg(⊤) = {I_i}: the tautology's denotation is the whole field,
and nothing is strictly better than I_i. -/
theorem field_is_max {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I)
    (hX : X ⊆ field ord i) :
    ¬ strictlyBetter ord i X (field ord i) ∨
    degreeEquiv ord i X (field ord i) := by
  sorry

/-- Fact 13b: the empty set is the minimum degree.
deg(⊥) = {∅}: the contradiction's denotation is empty,
and nothing is strictly worse than ∅. -/
theorem empty_is_min {I : Type} [Fintype I] [DecidableEq I]
    (ord : SemanticOrdering I) (i : I) (X : Finset I)
    (hX : X ⊆ field ord i) :
    ¬ strictlyBetter ord i (∅ : Finset I) X ∨
    degreeEquiv ord i X ∅ := by
  sorry


end Semantics.Comparison.MetalinguisticDegree
