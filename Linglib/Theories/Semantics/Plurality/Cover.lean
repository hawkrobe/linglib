import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Linglib.Core.Mereology

/-!
# Schwarzschild Covers and Partitions
@cite{schwarzschild-1996} @cite{champollion-2017}

A *cover* of a plural entity `x` is a set of parts of `x` whose least
upper bound is `x` itself. @cite{schwarzschild-1996} introduces covers
(building on Gillon 1987 — bib entry pending) to model nonatomic
distributivity:
when "the shoes cost fifty dollars" distributes over pairs of shoes
(not individual shoes), the distributivity operator is anaphoric on a
contextually-salient cover of *the shoes* by pairs.
@cite{champollion-2017} adopts this strategy and extends it to the
temporal domain via stratified reference.

## Main declarations

* `IsCover` — a set of parts whose least upper bound is the whole.
  Mathematically `IsLUB`; renamed for linguistics-literature grounding.
* `IsPartition` — a cover whose parts are pairwise disjoint.
* `IsFinCover` — finite-cover specialisation via `Finset.sup'`.
* `algClosure_of_finCover` — bridge from explicit Schwarzschild
  decomposition to Champollion-style `AlgClosure`.

## Implementation notes

A cover is an EXPLICIT decomposition; `AlgClosure` is the IMPLICIT
closure. Stratified reference (`Theories/Semantics/Aspect/Stratified.lean`)
uses `AlgClosure` because the strata are existentially closed; covers
are the right primitive when the parts must be supplied (anaphoric
distributivity, contextually-salient partitions). The reverse direction
(`AlgClosure` → cover) is non-trivial: `AlgClosure` witnesses are not
unique covers since the inductive `sum` constructor can be applied in
many orders.

## Todo

* Bridge to @cite{brisson-1998}'s ill-fitting covers (non-maximality
  via cover-cells with exceptions).
* Bridge to `CandidateInterpretation.fullCandidateSet` — a candidate
  is morally a cell of *some* cover, but the substrate-level
  connection is not yet stated.
-/

namespace Semantics.Plurality.Cover

open _root_.Mereology

/-! ### Cover -/

/-- @cite{schwarzschild-1996} *cover*: a set of parts whose least upper
    bound is the whole. Parts may overlap.

    Mathematically equivalent to mathlib's `IsLUB parts whole`; the
    cover terminology is preserved for the linguistics literature.

    The "every part is ≤ whole" condition is automatic from `IsLUB`
    (whole is by definition an upper bound). -/
abbrev IsCover {α : Type*} [Preorder α] (parts : Set α) (whole : α) : Prop :=
  IsLUB parts whole

/-- The whole is its own one-element cover (trivial cover). -/
theorem isCover_singleton {α : Type*} [Preorder α] (x : α) :
    IsCover ({x} : Set α) x :=
  isLUB_singleton

/-- Two-part cover: when `whole = x ⊔ y` in a join semilattice,
    `{x, y}` is a cover of `whole`. The minimal nontrivial case. -/
theorem isCover_pair {α : Type*} [SemilatticeSup α] (x y : α) :
    IsCover ({x, y} : Set α) (x ⊔ y) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases ha with ha | ha
    · subst ha; exact le_sup_left
    · rcases ha with rfl; exact le_sup_right
  · intro b hb
    apply sup_le
    · exact hb (Set.mem_insert _ _)
    · exact hb (Set.mem_insert_of_mem _ rfl)

/-! ### Partition -/

/-- @cite{schwarzschild-1996} *partition*: a cover whose parts are
    pairwise disjoint. Used by atomic distributivity (the special
    atomic case of @cite{schwarzschild-1996}) where each plural element
    distributes to a unique cell of the partition.

    "Disjoint" here is meet-bottom; requires the carrier to have a
    `SemilatticeInf` and `OrderBot`. -/
def IsPartition {α : Type*} [Lattice α] [OrderBot α]
    (parts : Set α) (whole : α) : Prop :=
  IsCover parts whole ∧ parts.PairwiseDisjoint id

/-! ### Finite covers -/

/-- Finite cover: the typical linguistic case where the contextually
    salient set of parts is enumerable. Uses `Finset.sup'` to avoid the
    `OrderBot` requirement of `Finset.sup`.

    Example: in *the shoes cost fifty dollars* with the salient cover
    "by pairs of shoes", the cover is the finite set of pairs. -/
def IsFinCover {α : Type*} [SemilatticeSup α]
    (parts : Finset α) (h : parts.Nonempty) (whole : α) : Prop :=
  parts.sup' h id = whole

/-! ### Bridge to `Mereology.AlgClosure`

If `parts` is a finite cover of `whole` and every part satisfies `P`,
then `whole` is in the algebraic closure of `P`. The reverse direction
is non-trivial (see Implementation notes above). -/

/-- A finite cover whose parts all satisfy `P` witnesses `AlgClosure P whole`. -/
theorem algClosure_of_finCover {α : Type*} [SemilatticeSup α]
    {P : α → Prop} {parts : Finset α} {h : parts.Nonempty} {whole : α}
    (hCover : IsFinCover parts h whole)
    (hP : ∀ p ∈ parts, P p) : AlgClosure P whole := by
  unfold IsFinCover at hCover
  rw [← hCover]
  exact Finset.sup'_induction h id
    (fun _ ha _ hb => AlgClosure.sum ha hb)
    (fun p hp => AlgClosure.base (hP p hp))

end Semantics.Plurality.Cover
