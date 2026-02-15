import Linglib.Core.Partition
import Linglib.Core.NaturalLogic

/-!
# Polarity–Partition Bridge

Connects the natural logic algebra (`Core.NaturalLogic`) to partition
structure (`Core.Partition`), formalizing Merin's (1999) central insight:
**negativity is coarsening**.

## Key connections

1. `NLRelation.negation` (A∩B=∅, A∪B=U) corresponds to partition identity:
   complements induce the same binary partition (`complements_same_partition`).

2. `ContextPolarity.downward` (DE) corresponds to partition coarsening:
   a DE context maps refinements to coarsenings.

3. `negationSig ^ 2 = addMult` (double negation = morphism) corresponds to
   double complement being the identity on partitions
   (`double_complement_same_partition`).

## Design

`Core.NaturalLogic` is the algebraic root: `EntailmentSig`, `ContextPolarity`,
`NLRelation` define the abstract algebra of entailment and polarity.
`Core.Partition` provides the partition lattice on `QUD`. This module
connects them: the NL algebra *governs* partition structure.

## References

- Merin (1999). Negative Attributes, Partitions, and Rational Decisions.
- Icard (2012). Inclusion and Exclusion in Natural Language.
-/

namespace Core.PolarityPartition

open Core.NaturalLogic

variable {M : Type*}

-- ============================================================================
-- §1 — NLRelation.negation ↔ Partition Identity
-- ============================================================================

/-- Two predicates are pointwise complements. This is the semantic content
of `NLRelation.negation` (A∩B=∅ and A∪B=U) instantiated to Boolean
predicates on a type `M`. -/
def AreComplements (p q : M → Bool) : Prop :=
  ∀ m, q m = !p m

/-- Complementary predicates (NLRelation.negation) induce identical
binary partitions. This grounds the set-theoretic NL relation in
partition structure: complements carry the same information content.

This is Merin (1999, Fact 1) via the NL relation algebra. -/
theorem complements_same_partition (p q : M → Bool) (h : AreComplements p q)
    (w v : M) :
    (QUD.binaryPartition p).sameAnswer w v =
    (QUD.binaryPartition q).sameAnswer w v := by
  simp only [QUD.ofProject_sameAnswer]
  rw [h w, h v]
  cases p w <;> cases p v <;> rfl

/-- Double complement returns to the same partition.

Partition-theoretic content of `negationSig ^ 2 = addMult` (Icard 2012):
complement ∘ complement is the identity on partitions. The algebraic
fact that the anti-morphism signature is self-inverse is *visible* in
partition structure as double complement preserving all cells. -/
theorem double_complement_same_partition (p : M → Bool) (w v : M) :
    (QUD.binaryPartition p).sameAnswer w v =
    (QUD.binaryPartition (fun m => !!p m)).sameAnswer w v := by
  simp [QUD.ofProject_sameAnswer, Bool.not_not]

-- ============================================================================
-- §2 — DE and Partition Coarsening
-- ============================================================================

/-- Complement preserves the coarsening relation.

If the binary partition of R is a coarsening of Q, then so is the binary
partition of ¬R. This follows immediately from `complement_same_partition`:
the two partitions are identical, so they coarsen the same things.

This is the partition-theoretic reading of DE: complement doesn't change
the information structure. -/
theorem complement_preserves_coarsening (q : QUD M) (R : M → Bool)
    (h : (QUD.binaryPartition R).coarsens q) :
    (QUD.binaryPartition (fun m => !R m)).coarsens q := by
  intro w v hq
  have := QUD.complement_same_partition R w v
  rw [← this]
  exact h w v hq

/-- A negative attribute and its complement are equally negative
(coarsening direction).

Merin's fundamental insight: negativity is not about morphological negation
("un-", "not") but about the partition a predicate induces. Since complements
induce the same partition, R is a negative attribute iff ¬R is.

Syntactic negation markers are *surface cues* for partition coarsening,
but the underlying property is purely information-theoretic. -/
theorem complement_equally_negative_coarsening (R : M → Bool) (q : QUD M) :
    (QUD.binaryPartition R).coarsens q ↔
    (QUD.binaryPartition (fun m => !R m)).coarsens q :=
  ⟨complement_preserves_coarsening q R,
   fun h => by
     have h' := complement_preserves_coarsening q (fun m => !R m) h
     simp only [Bool.not_not] at h'
     exact h'⟩

-- ============================================================================
-- §3 — EntailmentSig and Partition Structure
-- ============================================================================

end Core.PolarityPartition
