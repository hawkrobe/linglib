import Mathlib.Data.Setoid.Partition
import Linglib.Core.Inquisitive.Basic
import Linglib.Core.Mood.POSWQ

/-!
# Partition as Inquiry — Setoid → InquisitiveContent embedding
@cite{ciardelli-groenendijk-roelofsen-2018} @cite{theiler-etal-2018}
@cite{puncochar-2019}

The faithful embedding of partition-based inquiry (`Setoid W` — what
`POSWQ.inquiry` carries) into the more general inquisitive-content
representation (`InquisitiveContent W` — downward-closed nonempty
families of information states).

## Architectural placement

This file implements the embedding direction prescribed in the
"Architectural note: Setoid vs. InquisitiveContent" section of
`POSWQ.lean` (added 0.229.922): we keep `inquiry : Setoid W` as the
field of `POSWQ` (partitions are the right shape for the propositional-
discourse use cases that currently exist), and provide a *one-way*
embedding `Setoid → InquisitiveContent`. The embedding goes this way
and not the other because every Setoid-based partition can be expressed
as an InquisitiveContent (each equivalence class becomes a maximal
proposition / alternative), but the reverse fails — mention-some,
intermediate-exhaustive, and conditional question alternatives are
non-disjoint or non-exhaustive and so are not representable as the
classes of any equivalence relation (see @cite{theiler-etal-2018}).

This mirrors mathlib's `Set.toFinset` / `Filter.principal` /
`UniformSpace.toTopologicalSpace` pattern: the "less general" structure
sits inside the "more general" one via a faithful but not surjective
forgetful map.

## What this gives us

- `fromSetoid r : InquisitiveContent W` — the inquisitive content whose
  alternatives are the equivalence classes of `r`. Concretely,
  `props = {q | q = ∅ ∨ ∃ c ∈ r.classes, q ⊆ c}`: a non-empty information
  state `q` resolves the issue iff it is contained in some equivalence
  class (i.e., everything in `q` is `r`-equivalent).
- `info_fromSetoid` — informative content is `Set.univ`. Setoid-based
  inquiry is **non-informative**: it raises an issue but supplies no
  information. (This matches the standard partition-semantics view.)
- `isInquisitive_fromSetoid_of_two_classes` — if `r` has at least two
  distinct equivalence classes, the resulting content is inquisitive
  (in `InquisitiveContent`'s sense: `info ∉ props`). The trivial
  partition (one class) yields a declarative.
-/

namespace Core.Inquisitive

namespace InquisitiveContent

universe u
variable {W : Type u}

/-- The InquisitiveContent associated with a setoid `r` on `W`: a
    proposition `q` resolves the issue iff `q = ∅` or `q` is contained
    in some `r`-equivalence class (i.e., everything in `q` agrees on the
    `r`-question). The maximal such propositions are the equivalence
    classes themselves. -/
def fromSetoid (r : Setoid W) : InquisitiveContent W where
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

end InquisitiveContent

end Core.Inquisitive

/-! ## POSWQ bridge

Lift the partition-based inquiry component of a `POSWQ` to its full
`InquisitiveContent`. This makes every existing POSWQ-using study
automatically a consumer of the inquisitive-content API: `info`,
`alt`, `isInquisitive`, the lattice operations, and the
mention-some/IE-question forcing arguments all become available
without rewriting the underlying state. -/

namespace Core.Mood

namespace POSWQ

open Core.Inquisitive (InquisitiveContent)

universe u
variable {W : Type u}

/-- The inquisitive content embedded in a POSWQ via its inquiry
    partition. Always non-informative (`info = univ`); inquisitive
    iff the partition has more than one cell. -/
def inquiryContent (c : POSWQ W) : InquisitiveContent W :=
  InquisitiveContent.fromSetoid c.inquiry

@[simp] theorem inquiryContent_eq (c : POSWQ W) :
    c.inquiryContent = InquisitiveContent.fromSetoid c.inquiry := rfl

@[simp] theorem info_inquiryContent (c : POSWQ W) :
    c.inquiryContent.info = Set.univ :=
  InquisitiveContent.info_fromSetoid c.inquiry

end POSWQ

end Core.Mood
