import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range

/-!
# Domain-Relativized Contiguity
[moskal-2015a-dissertation] [moskal-2015]
[smith-moskal-xu-kang-bobaljik-2019]

A domain partition assigns each cell position in a paradigm to a
*domain tag* — abstractly representing the cell's locality unit
(spellout domain / phase / accessibility domain etc.). Within a
domain, the *ABA contiguity constraint applies; across domain
boundaries, AAB patterns are admitted.

## Motivation

`Morphology.DM.ContainmentVI.Degree.vi_cmpr_eq_sprl` (the DM
derivation, [bobaljik-2012]) predicts CMPR-cell = SPRL-cell for
any VI-generable root pattern. Lifted to case (Wardaman 3SG: ABS=
narnaj, ERG=narnaj-(j)i, DAT=gunga; [smith-moskal-xu-kang-bobaljik-2019]
§3.6) and number (Yagua 2: SG=jiy, PL=jiry-éy, DL=sáada;
[smith-moskal-xu-kang-bobaljik-2019] §4.2 Table 46), the
prediction is empirically falsified — AAB patterns are attested in
both case and number suppletion.

[smith-moskal-xu-kang-bobaljik-2019] §3.7 attribute the gap to
*locality*: structural-adjacency ([bobaljik-2012]) and linear-
adjacency ([embick-2010]) are too restrictive once AAB is
admitted. They endorse the [moskal-2015a-dissertation] theory of
**accessibility domains (AD)**: a category-defining node has a
delimiting effect that puts more-distant material outside the AD of
the root, blocking it from conditioning suppletion. Lexical material
has such a node (so case can't reach the root); pronouns lack it
(so case and number can both condition pronominal suppletion).

## What this substrate models, and what it doesn't

This file represents the **output** of an AD computation projected
onto cell positions: a function `Nat → Tag` that says, for each cell,
which locality unit it belongs to. The trigger-relative AD theory
([moskal-2015a-dissertation]: "the first category-defining node
above the root, and one node above that") is more nuanced — it's a
relation between a *trigger node* and a *root node* in a tree, not a
labeling of paradigm cells.

The substrate is theory-neutral about how the partition is computed.
[moskal-2015a-dissertation]'s AD is one source. [embick-2010]'s
linear adjacency is another (every position in its own one-cell
domain). [bobaljik-2012]'s structural adjacency is a third.
[caha-2009]'s Nanosyntax doesn't fit a domain-partition shape at
all — it derives AAB exclusion (or non-exclusion) from phrasal
spellout + the Superset Principle, not from locality. Consumers
state which projection they want; the substrate doesn't pick.

## Design

`ViolatesABAWithin π cells` is the Prop predicate "there exist
positions i < j < k in `cells.length`, all in the same domain under
`π`, such that `cells[i] = cells[k] ≠ cells[j]`." Decidability comes
free via `Fintype (Fin n)` — no Bool-first decision procedure needed.

## Why not import `Syntax/Minimalist/Phase.lean`?

`Phase.lean` operates on `SyntacticObject` trees with `isPhaseHeadOf`.
The morphological "domain" is more abstract — it lives at the level
of cell-position projections of paradigm tables, with no syntactic-
tree commitment. A future cross-layer connection (showing that
syntactic phases project to morphological domains under a
DM-with-phase analysis) can be added in `Morphology/` once
a consumer requests it.
-/

namespace Morphology.DomainLocality

variable {Tag : Type*} [DecidableEq Tag]

-- ============================================================================
-- § 1: Domain Partition
-- ============================================================================

/-- A domain partition assigns each cell position to a domain tag.
    Polymorphic over the tag type so callers (Bobaljik2012, SmithMoskal,
    Caha …) can use whatever tag type their analysis demands.

    `abbrev` so `π i` reduces through the type alias — needed by
    `decide` on concrete partitions. -/
abbrev DomainPartition (Tag : Type*) : Type _ := Nat → Tag

/-- Two cell positions lie in the same domain. `abbrev` for the same
    `decide`-reduction reason. -/
abbrev SameDomain (π : DomainPartition Tag) (i j : Nat) : Prop := π i = π j

instance (π : DomainPartition Tag) (i j : Nat) : Decidable (SameDomain π i j) :=
  inferInstanceAs (Decidable (_ = _))

/-- The trivial partition: every position in one domain (`Unit` tag). -/
abbrev DomainPartition.trivial : DomainPartition Unit := λ _ => ()

-- ============================================================================
-- § 2: Within-Domain *ABA Predicate
-- ============================================================================

/-- A list violates the domain-relativized *ABA constraint when there
    exist three positions i < j < k (within the list's length), all
    in the same domain under π, such that the cells at i and k share
    a value distinct from the cell at j.

    Bounded by `Finset.range cells.length` so decidability composes
    cleanly via `Finset.decidableBExists`. `cells[·]?` (returning
    `Option Nat`) is the cell accessor; `Option Nat` has
    `DecidableEq`. Direct propositional content, no Bool wrapper. -/
def ViolatesABAWithin (π : DomainPartition Tag) (cells : List Nat) : Prop :=
  ∃ i ∈ Finset.range cells.length,
  ∃ j ∈ Finset.range cells.length,
  ∃ k ∈ Finset.range cells.length,
    i < j ∧ j < k ∧
    SameDomain π i j ∧ SameDomain π i k ∧
    cells[i]? = cells[k]? ∧ cells[i]? ≠ cells[j]?

instance (π : DomainPartition Tag) (cells : List Nat) :
    Decidable (ViolatesABAWithin π cells) :=
  inferInstanceAs (Decidable
    (∃ i ∈ Finset.range cells.length,
     ∃ j ∈ Finset.range cells.length,
     ∃ k ∈ Finset.range cells.length,
       i < j ∧ j < k ∧
       SameDomain π i j ∧ SameDomain π i k ∧
       cells[i]? = cells[k]? ∧ cells[i]? ≠ cells[j]?))

/-- Domain-relativized contiguity: no within-domain *ABA violation. -/
def IsContiguousWithin (π : DomainPartition Tag) (cells : List Nat) : Prop :=
  ¬ ViolatesABAWithin π cells

instance (π : DomainPartition Tag) (cells : List Nat) :
    Decidable (IsContiguousWithin π cells) :=
  inferInstanceAs (Decidable (¬ _))

-- ============================================================================
-- § 3: Trivial-Partition Specialization
-- ============================================================================

/-- Under the trivial partition, every same-domain check trivially
    holds, so `ViolatesABAWithin` reduces to the unconstrained
    *ABA-pattern existential. -/
theorem ViolatesABAWithin_trivial_iff_unconstrained (cells : List Nat) :
    ViolatesABAWithin DomainPartition.trivial cells ↔
      ∃ i ∈ Finset.range cells.length,
      ∃ j ∈ Finset.range cells.length,
      ∃ k ∈ Finset.range cells.length,
        i < j ∧ j < k ∧
        cells[i]? = cells[k]? ∧ cells[i]? ≠ cells[j]? := by
  unfold ViolatesABAWithin
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi, j, hj, k, hk, hij, hjk, _, _, h1, h2⟩
    exact ⟨i, hi, j, hj, k, hk, hij, hjk, h1, h2⟩
  · rintro ⟨i, hi, j, hj, k, hk, hij, hjk, h1, h2⟩
    exact ⟨i, hi, j, hj, k, hk, hij, hjk, rfl, rfl, h1, h2⟩

-- ============================================================================
-- § 4: Smoke Tests
-- ============================================================================

/-! Trivial-partition behavior: same shape as the universal predicate.
    Across-domain examples illustrate that AAB *ABA-shapes are
    admitted when the inner cell is in a different domain than the
    outer cells. -/

/-- ABB under trivial partition: contiguous (no *ABA). -/
example : IsContiguousWithin DomainPartition.trivial [0, 1, 1] := by decide

/-- ABA under trivial partition: violates *ABA. -/
example : ViolatesABAWithin DomainPartition.trivial [0, 1, 0] := by decide

/-- AAB under trivial partition: contiguous (the AAB shape is *ABA-
    contiguous; it's excluded by VI locality, not by ABA). -/
example : IsContiguousWithin DomainPartition.trivial [0, 0, 1] := by decide

/-- An AAB pattern with positions 0,1 in domain `"a"` and position 2
    in domain `"b"`. Trivially contiguous regardless of partition
    (AAB is *ABA-contiguous). -/
example : IsContiguousWithin
    (λ i => if i = 2 then "b" else "a" : DomainPartition String)
    [0, 0, 1] := by decide

/-- The same partition admits an "across-domain ABA" shape `[0, 1, 0]`:
    positions 0 and 2 (both cell value 0) are in different domains, so
    the within-domain *ABA check does not fire. The universal contiguity
    predicate (`Morphology.Containment.IsContiguous`) would reject this
    pattern; the domain-relativized version permits it. -/
example : ¬ ViolatesABAWithin
    (λ i => if i = 2 then "b" else "a" : DomainPartition String)
    [0, 1, 0] := by decide

/-- Same `[0, 1, 0]` ABA pattern under the trivial partition: violates,
    as expected. -/
example : ViolatesABAWithin DomainPartition.trivial [0, 1, 0] := by decide

end Morphology.DomainLocality
