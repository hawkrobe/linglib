import Linglib.Core.QUD
import Linglib.Core.DecisionTheory

/-!
# Partition Lattice

Refinement, coarsening, and cell enumeration for partitions (`QUD`).

Partitions arise wherever a domain is classified into mutually exclusive,
exhaustive categories. Groenendijk & Stokhof (1984) use them for question
denotations, but the lattice structure is domain-general: it applies equally
to attribute spaces (Carnap 1971, Merin 1999), conceptual categories, and
any classificatory scheme.

## Lattice Structure

Partitions form a bounded lattice ordered by refinement:
- **Refinement** (⊑): Q refines Q' iff Q's cells are subsets of Q''s
- **Coarsening**: dual — Q coarsens Q' iff Q' refines Q
- **Meet** (`*`): coarsest common refinement (`QUD.compose`)
- **Top**: exact partition (finest)
- **Bottom**: trivial partition (coarsest)

## Decision-Theoretic Significance

Merin (1999) argues that partitions are decision-theoretically privileged:
coarsening preserves compositionality of expected value, while arbitrary
restructuring does not. Negative attributes are products of proper coarsening —
an epistemic, syntax-independent characterization of negativity.

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions.
- Merin (1999). Negative Attributes, Partitions, and Rational Decisions.
- Blackwell (1953). Equivalent Comparisons of Experiments.
- Carnap (1971). A Basic System of Inductive Logic. Part I.
-/

namespace QUD

variable {M : Type*}

/-! ### Refinement and Coarsening -/

/-- Q refines Q' iff Q's equivalence classes are subsets of Q''s.

Intuitively: knowing the Q-answer tells you the Q'-answer.
If two elements give the same Q-answer, they must give the same Q'-answer.

Forms a partial order on partitions (up to extensional equivalence). -/
def refines (q q' : QUD M) : Prop :=
  ∀ w v, q.sameAnswer w v = true → q'.sameAnswer w v = true

scoped infix:50 " ⊑ " => QUD.refines

/-- Q coarsens Q' iff Q' refines Q (dual of refinement).

Coarsening merges cells: where Q' distinguishes elements, Q may not.
Merin (1999) defines negative attributes in terms of coarsening:
negation is the linguistic device that produces coarsenings on the fly. -/
def coarsens (q q' : QUD M) : Prop := q' ⊑ q

/-- Refinement is reflexive. -/
theorem refines_refl (q : QUD M) : q ⊑ q := λ _ _ h => h

/-- Refinement is transitive. -/
theorem refines_trans {q1 q2 q3 : QUD M} :
    q1 ⊑ q2 → q2 ⊑ q3 → q1 ⊑ q3 :=
  λ h12 h23 w v h1 => h23 w v (h12 w v h1)

/-- Refinement is antisymmetric up to extensional equivalence of `sameAnswer`.

True propositional antisymmetry (`q1 = q2`) would require quotient types;
this is the extensional version. -/
theorem refines_antisymm {q1 q2 : QUD M} :
    q1 ⊑ q2 → q2 ⊑ q1 → (∀ w v, q1.sameAnswer w v = q2.sameAnswer w v) := by
  intro h12 h21 w v
  cases hq1 : q1.sameAnswer w v with
  | false =>
    cases hq2 : q2.sameAnswer w v with
    | false => rfl
    | true => exact absurd (h21 w v hq2) (by simp [hq1])
  | true =>
    exact (h12 w v hq1).symm

/-- All partitions refine (are coarser than or equal to) the trivial partition. -/
theorem all_refine_trivial (q : QUD M) :
    q ⊑ trivial := λ _ _ _ => rfl

/-- The meet (coarsest common refinement) refines the left factor. -/
theorem compose_refines_left (q1 q2 : QUD M) : (q1 * q2) ⊑ q1 := by
  intro w v h
  simp only [HMul.hMul, Mul.mul, QUD.compose] at h
  cases h1 : q1.sameAnswer w v <;> cases h2 : q2.sameAnswer w v <;> simp_all

/-- The meet (coarsest common refinement) refines the right factor. -/
theorem compose_refines_right (q1 q2 : QUD M) : (q1 * q2) ⊑ q2 := by
  intro w v h
  simp only [HMul.hMul, Mul.mul, QUD.compose] at h
  cases h1 : q1.sameAnswer w v <;> cases h2 : q2.sameAnswer w v <;> simp_all

/-- The exact (finest) partition refines all partitions. -/
theorem exact_refines_all [BEq M] [LawfulBEq M] (q : QUD M) :
    exact ⊑ q := by
  intro w v h
  simp only [exact] at h
  have heq : w = v := by rw [beq_iff_eq] at h; exact h
  rw [heq]; exact q.refl v

/-! ### Finite Partition Cells -/

/-- Compute partition cells as characteristic functions over a finite domain.

Each cell is the set of elements equivalent to a representative. Representatives
are chosen greedily from the input list. -/
def toCells (q : QUD M) (elements : List M) : List (M → Bool) :=
  let representatives := elements.foldl (λ acc w =>
    if acc.any λ r => q.sameAnswer r w then acc else w :: acc
  ) []
  representatives.map λ rep => λ w => q.sameAnswer rep w

/-- Number of cells in the partition over a finite domain. -/
def numCells (q : QUD M) (elements : List M) : Nat :=
  (q.toCells elements).length

/-- Finer partitions have at least as many cells. -/
theorem refines_numCells_ge (q q' : QUD M) (elements : List M) :
    q ⊑ q' → q.numCells elements >= q'.numCells elements := by
  sorry -- TODO: requires showing refinement can only split cells, never merge

/-! ### Proper Coarsening (Merin 1999) -/

/-- Q is a proper coarsening of Q' over a finite domain iff Q coarsens Q'
and has strictly fewer cells.

Merin (1999) defines negative attributes via proper coarsening:
R is a *negative attribute* with respect to partition F iff for some Q ∈ F,
{R, Q} is a proper coarsening of F. This characterization is purely epistemic
and syntax-independent — negativity is a matter of partition kinetics, not
morphological form. -/
def isProperCoarsening (q q' : QUD M) (elements : List M) : Prop :=
  q.coarsens q' ∧ q.numCells elements < q'.numCells elements

/-! ### Binary Partitions (Merin 1999) -/

/-- Binary partition from a Boolean predicate. Two elements are equivalent
iff the predicate gives the same value on both.

Binary partitions are the building blocks of coarsening: every proper
coarsening can be decomposed into steps that merge exactly two cells,
each corresponding to a binary partition. Merin (1999) characterizes
negative attributes entirely in terms of binary partition coarsening. -/
abbrev binaryPartition (p : M → Bool) : QUD M := ofProject p

/-- Complement predicates induce the same binary partition.

Merin (1999, Fact 1): a proposition and its negation carry exactly the same
information. {P-worlds, ¬P-worlds} = {¬P-worlds, P-worlds} as partitions. -/
theorem complement_same_partition (p : M → Bool) (w v : M) :
    (binaryPartition p).sameAnswer w v =
    (binaryPartition (fun m => !p m)).sameAnswer w v := by
  simp only [ofProject_sameAnswer]
  cases p w <;> cases p v <;> rfl

/-- A binary partition from a predicate that respects q's equivalence classes
is a coarsening of q. Every "coarser" yes/no distinction is a coarsening. -/
theorem binaryPartition_coarsens (q : QUD M) (p : M → Bool)
    (h : ∀ w v, q.sameAnswer w v = true → p w = p v) :
    (binaryPartition p).coarsens q := by
  intro w v hq
  simp only [ofProject_sameAnswer, beq_iff_eq]
  exact h w v hq

/-- A predicate R is a *negative attribute* with respect to partition Q over
a finite domain iff the binary partition of R is a proper coarsening of Q.

Merin (1999): negativity is not a syntactic property (presence of "un-",
"not", etc.) but a partition-kinetic one. R is negative relative to Q when
the R/¬R distinction is strictly coarser than Q's partition — answering
whether R holds loses information that Q distinguishes. -/
def isNegativeAttribute (R : M → Bool) (q : QUD M) (elements : List M) : Prop :=
  isProperCoarsening (binaryPartition R) q elements

/-! ### Coarsest P-Preserving Coarsening (Merin 1999, Fact 3) -/

/-- The coarsest coarsening of Q that preserves predicate P.

Two elements are equivalent iff they are Q-equivalent AND agree on P.
This is the meet of Q with the binary partition of P: the finest partition
that is coarser than both Q and binaryPartition P.

Merin (1999): for any proposition P and partition Q, this is the unique
coarsest partition that refines Q while still distinguishing P-worlds
from ¬P-worlds within each Q-cell. -/
def coarsestPreserving (q : QUD M) (P : M → Bool) : QUD M :=
  q * binaryPartition P

/-- The P-preserving coarsening refines Q (it can only be finer). -/
theorem coarsestPreserving_refines (q : QUD M) (P : M → Bool) :
    coarsestPreserving q P ⊑ q :=
  compose_refines_left q (binaryPartition P)

/-- The P-preserving coarsening respects P: equivalent elements agree on P. -/
theorem coarsestPreserving_preserves_P (q : QUD M) (P : M → Bool)
    (w v : M) (h : (coarsestPreserving q P).sameAnswer w v = true) :
    P w = P v := by
  have hbin := compose_refines_right q (binaryPartition P) w v h
  simp only [ofProject_sameAnswer, beq_iff_eq] at hbin
  exact hbin

/-- Any partition that refines Q and preserves P also refines the
P-preserving coarsening. This is the universality property: `coarsestPreserving`
is the coarsest such partition. -/
theorem coarsestPreserving_universal (q q' : QUD M) (P : M → Bool)
    (hrefines : q' ⊑ q)
    (hpreserves : ∀ w v, q'.sameAnswer w v = true → P w = P v) :
    q' ⊑ coarsestPreserving q P := by
  intro w v h
  unfold coarsestPreserving
  simp only [HMul.hMul, Mul.mul, compose]
  simp only [Bool.and_eq_true]
  exact ⟨hrefines w v h, by simp only [ofProject_sameAnswer, beq_iff_eq]; exact hpreserves w v h⟩

/-! ### EU Compositionality under Coarsening (Merin 1999, Central Theorem) -/

open Core.DecisionTheory in
/-- Expected utility computed via a partition: weight each cell's conditional EU
by the cell's probability.

EU_Q(a) = Σ_{c ∈ cells(Q)} P(c) · EU(a | c)

This is the partition-relative expected utility that Merin (1999) shows is
compositional under coarsening. -/
def partitionEU {A : Type*} (dp : DecisionProblem M A) (q : QUD M)
    (worlds : List M) (a : A) : ℚ :=
  let cells := q.toCells worlds
  cells.foldl (fun acc cell =>
    let cellWorlds := worlds.filter cell
    let cellProb := cellWorlds.foldl (fun s w => s + dp.prior w) 0
    let cellEU := conditionalEU dp cellWorlds a cell
    acc + cellProb * cellEU
  ) 0

open Core.DecisionTheory in
/-- EU compositionality under coarsening (Merin 1999, central theorem).

If Q coarsens Q' (Q has fewer distinctions), then computing EU via Q gives
the same result as computing EU via Q', provided the utility function only
depends on Q-level distinctions.

In full generality: EU is always recoverable from any refinement. Coarsening
preserves EU because each coarse cell is a union of fine cells, and
EU decomposes additively over probability-weighted cells.

The unconditional expected utility equals the partition-relative EU for
any partition, because partitions are exhaustive and mutually exclusive. -/
theorem eu_eq_partitionEU {A : Type*} (dp : DecisionProblem M A)
    (worlds : List M) (a : A) (q : QUD M) :
    expectedUtility dp worlds a = partitionEU dp q worlds a := by
  sorry -- TODO: by induction on cells, using exhaustivity and mutual exclusivity

open Core.DecisionTheory in
/-- Coarsening preserves partition-relative EU.

If Q coarsens Q', then partitionEU via Q equals partitionEU via Q'.
This is the formal content of Merin's claim that partitions are
decision-theoretically privileged: EU decomposes additively over any
partition of the probability space, so coarsening (merging cells)
cannot change the total. -/
theorem coarsening_preserves_eu {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M)
    (worlds : List M) (a : A)
    (hcoarse : q.coarsens q') :
    partitionEU dp q worlds a = partitionEU dp q' worlds a := by
  sorry -- TODO: each coarse cell is a union of fine cells; EU decomposes additively

/-! ### Blackwell Ordering (Blackwell 1953) -/

open Core.DecisionTheory in
/-- The value of a decision problem under partition Q: the maximum expected
utility achievable when the decision-maker learns which Q-cell obtains. -/
def partitionValue {A : Type*} (dp : DecisionProblem M A)
    (q : QUD M) (worlds : List M) (actions : List A) : ℚ :=
  let cells := q.toCells worlds
  cells.foldl (fun acc cell =>
    let cellWorlds := worlds.filter cell
    let cellProb := cellWorlds.foldl (fun s w => s + dp.prior w) 0
    let bestEU := actions.foldl (fun best a =>
      max best (conditionalEU dp cellWorlds a cell)) 0
    acc + cellProb * bestEU
  ) 0

open Core.DecisionTheory in
/-- Blackwell's theorem for partitions: finer partitions are always at least
as valuable as coarser ones, for any decision problem.

If Q refines Q' (Q makes all the distinctions Q' does, and more), then
learning which Q-cell obtains is at least as useful as learning which
Q'-cell obtains, regardless of the decision problem.

V_Q(D) ≥ V_{Q'}(D) for all decision problems D, whenever Q ⊑ Q'.

This is the information-theoretic backbone of Merin's theory: refinement
in the partition lattice corresponds to Blackwell's ordering of experiments.
A finer partition is a "more informative experiment" — it can never hurt
the decision-maker. -/
theorem blackwell_refinement_value {A : Type*}
    (dp : DecisionProblem M A) (q q' : QUD M)
    (worlds : List M) (actions : List A)
    (hrefines : q ⊑ q') :
    partitionValue dp q worlds actions ≥ partitionValue dp q' worlds actions := by
  sorry -- TODO: finer partition → can condition on more → higher max EU

open Core.DecisionTheory in
/-- Blackwell ordering characterizes refinement: Q refines Q' if and only if
Q is at least as valuable as Q' for every decision problem.

This is the converse of `blackwell_refinement_value`: if Q is always at
least as valuable, then Q must refine Q'. Together they establish that
partition refinement IS Blackwell ordering. -/
theorem blackwell_characterizes_refinement
    (q q' : QUD M)
    (worlds : List M)
    (h : ∀ (A : Type) (dp : DecisionProblem M A) (actions : List A),
      partitionValue dp q worlds actions ≥ partitionValue dp q' worlds actions) :
    q ⊑ q' := by
  sorry -- TODO: construct a specific DP that witnesses non-refinement

end QUD
