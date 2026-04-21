import Linglib.Core.Question.Partition.QUD
import Linglib.Core.Question.Partition.Lattice

/-!
# Binary Partitions and P-Preserving Coarsenings
@cite{merin-1999}

Yes/no partitions induced by Boolean predicates, plus the coarsest
P-preserving coarsening of a given partition:

* `binaryPartition p` — equivalence by agreement on `p`. Building block of
  proper coarsening: every refinement step that merges two cells is a
  binary partition.
* `complement_same_partition` — `p` and `!p` carry the same information.
* `coarsestPreserving q P = q * binaryPartition P` — the finest partition
  that refines `q` and still distinguishes P-worlds from ¬P-worlds.
  Universality property: any q'-refinement that preserves P also refines
  this construction.

Used by `Core/Question/Partition/Negativity.lean` for Merin's epistemic
characterization of negative attributes.
-/

namespace QUD

variable {M : Type*}

/-! ### Binary Partitions -/

/-- Binary partition from a Boolean predicate. Two elements are equivalent
 iff the predicate gives the same value on both.

Binary partitions are the building blocks of coarsening: every proper
coarsening can be decomposed into steps that merge exactly two cells,
each corresponding to a binary partition. @cite{merin-1999} characterizes
negative attributes entirely in terms of binary partition coarsening. -/
abbrev binaryPartition (p : M → Bool) : QUD M := ofProject p

/-- Complement predicates induce the same binary partition.

@cite{merin-1999}: a proposition and its negation carry exactly the same
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

/-! ### Coarsest P-Preserving Coarsening (@cite{merin-1999}, Fact 3) -/

/-- The coarsest coarsening of Q that preserves predicate P.

Two elements are equivalent iff they are Q-equivalent AND agree on P.
This is the meet of Q with the binary partition of P: the finest partition
that is coarser than both Q and binaryPartition P.

@cite{merin-1999}: for any proposition P and partition Q, this is the unique
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
    P w = P v :=
  (ofProject_sameAnswer_iff _ _ _).mp (compose_refines_right q (binaryPartition P) w v h)

/-- Any partition that refines Q and preserves P also refines the
P-preserving coarsening. This is the universality property: `coarsestPreserving`
is the coarsest such partition. -/
theorem coarsestPreserving_universal (q q' : QUD M) (P : M → Bool)
    (hrefines : q' ⊑ q)
    (hpreserves : ∀ w v, q'.sameAnswer w v = true → P w = P v) :
    q' ⊑ coarsestPreserving q P := by
  intro w v h
  unfold coarsestPreserving
  simp only [mul_sameAnswer, Bool.and_eq_true]
  exact ⟨hrefines w v h, (ofProject_sameAnswer_iff _ _ _).mpr (hpreserves w v h)⟩

end QUD
