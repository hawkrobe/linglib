import Mathlib.Data.Setoid.Partition
import Linglib.Core.Issue.Basic
import Linglib.Core.Mood.POSWQ

/-!
# Partition as Inquiry — Setoid → Issue embedding
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{theiler-etal-2018}
@cite{puncochar-2019}

The faithful embedding of partition-based inquiry (`Setoid W` — what
`POSWQ.inquiry` carries) into the more general inquisitive-content
representation (`Issue W` — downward-closed nonempty
families of information states).

## Architectural placement

This file implements the embedding direction prescribed in the
"Architectural note: Setoid vs. Issue" section of
`POSWQ.lean` (added 0.229.922): we keep `inquiry : Setoid W` as the
field of `POSWQ` (partitions are the right shape for the propositional-
discourse use cases that currently exist), and provide a *one-way*
embedding `Setoid → Issue`. The embedding goes this way
and not the other because every Setoid-based partition can be expressed
as an Issue (each equivalence class becomes a maximal
proposition / alternative), but the reverse fails — mention-some,
intermediate-exhaustive, and conditional question alternatives are
non-disjoint or non-exhaustive and so are not representable as the
classes of any equivalence relation (see @cite{theiler-etal-2018}).

This mirrors mathlib's `Set.toFinset` / `Filter.principal` /
`UniformSpace.toTopologicalSpace` pattern: the "less general" structure
sits inside the "more general" one via a faithful but not surjective
forgetful map.

## What this gives us

- `fromSetoid r : Issue W` — the inquisitive content whose
  alternatives are the equivalence classes of `r`. Concretely,
  `props = {q | q = ∅ ∨ ∃ c ∈ r.classes, q ⊆ c}`: a non-empty information
  state `q` resolves the issue iff it is contained in some equivalence
  class (i.e., everything in `q` is `r`-equivalent).
- `info_fromSetoid` — informative content is `Set.univ`. Setoid-based
  inquiry is **non-informative**: it raises an issue but supplies no
  information. (This matches the standard partition-semantics view.)
- `isInquisitive_fromSetoid_of_two_classes` — if `r` has at least two
  distinct equivalence classes, the resulting content is inquisitive
  (in `Issue`'s sense: `info ∉ props`). The trivial
  partition (one class) yields a declarative.
-/

namespace Core

namespace Issue

universe u
variable {W : Type u}

/-- The Issue associated with a setoid `r` on `W`: a
    proposition `q` resolves the issue iff `q = ∅` or `q` is contained
    in some `r`-equivalence class (i.e., everything in `q` agrees on the
    `r`-question). The maximal such propositions are the equivalence
    classes themselves. -/
def fromSetoid (r : Setoid W) : Issue W where
  props := {q | q = ∅ ∨ ∃ c ∈ r.classes, q ⊆ c}
  contains_empty := Or.inl rfl
  downward_closed := fun p hp q hq => by
    rcases hp with hempty | ⟨c, hc, hpc⟩
    · left
      rw [hempty] at hq
      exact Set.subset_empty_iff.mp hq
    · right
      exact ⟨c, hc, hq.trans hpc⟩

/-- The informative content of a partition-based inquiry is the whole
    universe: every world is in some equivalence class, so every world
    appears in some resolving proposition. Setoid-derived inquisitive
    contents are **non-informative** — they raise issues but provide no
    information. -/
theorem info_fromSetoid (r : Setoid W) : (fromSetoid r).info = Set.univ := by
  ext w
  simp only [info, fromSetoid, Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_univ,
             iff_true]
  refine ⟨{x | r x w}, ?_, ?_⟩
  · exact Or.inr ⟨{x | r x w}, Setoid.mem_classes r w, subset_rfl⟩
  · exact Setoid.refl' r w

/-- If a setoid has two distinct equivalence classes, the resulting
    inquisitive content is inquisitive: `Set.univ` is not contained in
    any single equivalence class (it would have to coincide with both),
    so `info ∉ props`. -/
theorem isInquisitive_fromSetoid_of_two_classes
    (r : Setoid W) (w₁ w₂ : W) (hne : ¬ r w₁ w₂) :
    (fromSetoid r).isInquisitive := by
  show (fromSetoid r).info ∉ (fromSetoid r).props
  rw [info_fromSetoid]
  rintro (huniv | ⟨c, hc, hsub⟩)
  · exact (huniv ▸ Set.mem_univ w₁ : w₁ ∈ (∅ : Set W)).elim
  · obtain ⟨v, hv, rfl⟩ := hc
    have h1 : r w₁ v := hsub (Set.mem_univ w₁)
    have h2 : r w₂ v := hsub (Set.mem_univ w₂)
    exact hne (Setoid.trans' r h1 (Setoid.symm' r h2))

/-! ### Setoid–Issue bridge: refinement = entailment

The `fromSetoid` embedding is **monotone** in mathlib's lattice order on
`Setoid` (where `r₁ ≤ r₂` iff `r₁` is *finer*: `r₁.Rel x y → r₂.Rel x y`)
and the entailment order on `Issue` (`P ≤ Q` iff `P.props ⊆ Q.props`).
The bridge is moreover a **lattice embedding**: `≤` is reflected back.

This is the clean, Set-based replacement for the Bool/List partition
bridge `refinesOn_iff_questionEntails_of_partition` formerly housed in
`Core/Partition.lean`. The same content (Groenendijk–Stokhof's
"partition refinement = question entailment") is here a one-liner over
`Setoid` and `Core.Issue`, with no `worlds : List W` quantifier and no
`isPartition` precondition. -/

/-- The `Setoid → Issue` embedding **reflects** the order: a setoid is
    finer than another iff its inquisitive content is entailed by the
    other's. The forward direction is monotonicity; the backward
    direction uses the fact that `r`-equivalent pairs are resolved by
    the two-element state `{x, y}`, which any cell-membership theorem
    can recover. -/
theorem fromSetoid_le_iff (r₁ r₂ : Setoid W) :
    fromSetoid r₁ ≤ fromSetoid r₂ ↔ r₁ ≤ r₂ := by
  refine ⟨?_, ?_⟩
  · -- ≤ on Issue → ≤ on Setoid: take r₁-related x y; the doubleton
    -- {x, y} resolves fromSetoid r₁, hence resolves fromSetoid r₂.
    intro hle x y hxy
    have hpair : ({x, y} : Set W) ∈ fromSetoid r₁ := by
      refine Or.inr ⟨{z | r₁ z x}, Setoid.mem_classes r₁ x, ?_⟩
      rintro z (rfl | hz)
      · exact Setoid.refl' r₁ z
      · rw [Set.mem_singleton_iff] at hz; subst hz
        exact Setoid.symm' r₁ hxy
    have hpair' : ({x, y} : Set W) ∈ fromSetoid r₂ := hle hpair
    rcases hpair' with hempty | ⟨c, hc, hsub⟩
    · have : x ∈ ({x, y} : Set W) := Set.mem_insert x _
      rw [hempty] at this; exact this.elim
    · obtain ⟨v, _hv, rfl⟩ := hc
      have hxv : r₂ x v := hsub (Set.mem_insert x _)
      have hyv : r₂ y v := hsub (Set.mem_insert_of_mem x rfl)
      exact Setoid.trans' r₂ hxv (Setoid.symm' r₂ hyv)
  · -- ≤ on Setoid → ≤ on Issue: a state contained in an r₁-cell is
    -- contained in the surrounding r₂-cell (cells only widen).
    intro hle q hq
    rcases hq with hempty | ⟨c, hc, hqc⟩
    · subst hempty; exact (fromSetoid r₂).contains_empty
    · obtain ⟨v, _hv, rfl⟩ := hc
      refine Or.inr ⟨{z | r₂ z v}, Setoid.mem_classes r₂ v, ?_⟩
      intro z hz
      exact hle (hqc hz)

/-- Monotonicity of the `fromSetoid` embedding (the easy direction of
    `fromSetoid_le_iff`). -/
theorem fromSetoid_mono {r₁ r₂ : Setoid W} (h : r₁ ≤ r₂) :
    fromSetoid r₁ ≤ fromSetoid r₂ :=
  (fromSetoid_le_iff r₁ r₂).mpr h

end Issue

end Core

/-! ## POSWQ bridge

Lift the partition-based inquiry component of a `POSWQ` to its full
`Issue`. This makes every existing POSWQ-using study
automatically a consumer of the inquisitive-content API: `info`,
`alt`, `isInquisitive`, the lattice operations, and the
mention-some/IE-question forcing arguments all become available
without rewriting the underlying state. -/

namespace Core.Mood

namespace POSWQ

open Core (Issue)

universe u
variable {W : Type u}

/-- The inquisitive content embedded in a POSWQ via its inquiry
    partition. Always non-informative (`info = univ`); inquisitive
    iff the partition has more than one cell. -/
def inquiryContent (c : POSWQ W) : Issue W :=
  Issue.fromSetoid c.inquiry

@[simp] theorem inquiryContent_eq (c : POSWQ W) :
    c.inquiryContent = Issue.fromSetoid c.inquiry := rfl

@[simp] theorem info_inquiryContent (c : POSWQ W) :
    c.inquiryContent.info = Set.univ :=
  Issue.info_fromSetoid c.inquiry

end POSWQ

end Core.Mood
