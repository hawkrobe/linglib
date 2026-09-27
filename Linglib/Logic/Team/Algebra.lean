module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Lattice.Union

/-!
# Team algebra — pure `Finset` combinatorics for team semantics

[anttila-2021] [vaananen-2007] [yang-vaananen-2017]

The combinatorial primitives underlying team-semantic logics — BSML
(Aloni 2022), QBSML (Aloni & van Ormondt 2023), propositional team
logic PT⁺ (Yang & Väänänen 2017), modal team logic MTL (Hella et al.,
Lück), modal dependence logic MDᵂ (Yang), and inquisitive variants.

This file is **theory-neutral**: nothing in it knows about evaluation,
support, or formulas. It provides only the partition relations on teams
and the frame conditions on accessibility.

## Naming: "team" vs. "state"

We use "team" (Hodges 1997, Väänänen 2007) — the foundational term in
dependence/independence logic and propositional team logic. Aloni's
"state-based modal logic" papers use "state" for the same object (a
subset of evaluation points), inheriting via Anttila 2021. The two
terms are interchangeable in this layer; "team" is preferred here
because it generalizes cleanly: a team can be a set of worlds (BSML),
a set of (world, assignment) pairs (QBSML), a set of assignments
(dependence logic), etc., without the "state" connotation of "set of worlds".

## Two layers in this file

1. **Non-empty team splits** (`splitsAsNE`): the structural condition
   underlying BSML*'s split disjunction; the plain split is the pointwise
   sup `⊻` behind `Team.tensor` in `Team/Operations.lean`.

2. **Frame conditions on accessibility** (`IsStateBased`, `IsIndisputable`):
   Anttila Definition 2.2.10-equivalent properties of a relation
   `R : W → Finset W` relative to a base team. Used to distinguish
   epistemic and deontic modalities (Aloni 2022 §6.1).

## Family roadmap

Team-semantic logics form a family along two axes ([anttila-2025]):
a *signature* axis (propositional, modal, first-order) and a
*closure-class* axis over team properties (`∅ ∈ ·`, `IsLowerSet`,
`SupClosed`, `Set.OrdConnected`, with `DC = convex + empty`). Each logic
is pinned to a cell by an expressive-completeness theorem (`⟦L⟧` = the
properties in that cell), so the cell is a theorem about a logic, not a
directory. This substrate provides the closure predicates those theorems
are stated in; formalised consumers so far are BSML, QBSML, MDL, MIL,
InqML under `Logic/Modal/`.

The shared abstraction is a *lemma layer*, not a bundled `TeamLogic`
class — no closure law is shared across cells: `Team/Operations.lean`
defines the connectives as operations on team properties with their
closure lemmas, and `Team/Definability.lean` the definable classes. Refactor backward from concrete instances; do not extract
the abstraction forward (cf. the ≥ 3-systems rule). Full long-run shape,
target tree, and dependency-ordered build phases:
`Logic/Modal/README.md`.
-/

@[expose] public section

namespace Team

variable {α : Type*}

/-! ### Non-empty team splits -/

/-- Binary cover with both parts non-empty, `t₁ ∪ t₂ = s` with `t₁` and `t₂` non-empty. Used
    by pragmatically-enriched split disjunction in BSML* ([aloni-2022] §6.3.1). The plain
    split, `t₁ ∪ t₂ = s`, needs no name: the split clauses are `Team.tensor`, the pointwise
    sup `⊻` of team properties. -/
abbrev splitsAsNE [DecidableEq α] (s t₁ t₂ : Finset α) : Prop :=
  t₁ ∪ t₂ = s ∧ t₁.Nonempty ∧ t₂.Nonempty

theorem splitsAsNE_symm [DecidableEq α] {s t₁ t₂ : Finset α}
    (h : splitsAsNE s t₁ t₂) : splitsAsNE s t₂ t₁ :=
  ⟨(Finset.union_comm t₂ t₁).trans h.1, h.2.2, h.2.1⟩

instance [DecidableEq α] (s t₁ t₂ : Finset α) : Decidable (splitsAsNE s t₁ t₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A non-empty subteam of `u` on which `P` holds pointwise exists exactly when `P` holds
    somewhere in `u`: the witness may be taken to be a singleton. -/
theorem exists_nonempty_subset_forall_iff (u : Finset α) (P : α → Prop) :
    (∃ t ⊆ u, t.Nonempty ∧ ∀ x ∈ t, P x) ↔ ∃ x ∈ u, P x where
  mp := fun ⟨_, htu, ⟨x, hx⟩, h⟩ ↦ ⟨x, htu hx, h x hx⟩
  mpr := fun ⟨x, hxu, hx⟩ ↦
    ⟨{x}, Finset.singleton_subset_iff.mpr hxu, Finset.singleton_nonempty x,
      fun _ hy ↦ Finset.mem_singleton.mp hy ▸ hx⟩

end Team

namespace Team

variable {W : Type*}

/-! ### Frame conditions on accessibility -/

/-- `R` is **state-based** on team `s` iff every world in `s` is `R`-accessible
    exactly to `s`. Strictly stronger than indisputability.

    Aloni 2022 Definition 5; Anttila 2021 Definition 4.10-style. -/
def IsStateBased (R : W → Finset W) (s : Finset W) : Prop :=
  ∀ w ∈ s, R w = s

/-- `R` is **indisputable** on team `s` iff all worlds in `s` see the same
    set of accessible worlds. Equivalently: `R` is constant on `s`.

    Aloni 2022 Definition 5 (indisputable ↔ deontic-with-knowledgeable-speaker). -/
def IsIndisputable (R : W → Finset W) (s : Finset W) : Prop :=
  ∀ w₁ ∈ s, ∀ w₂ ∈ s, R w₁ = R w₂

/-- State-based implies indisputable. -/
theorem IsStateBased.isIndisputable {R : W → Finset W} {s : Finset W}
    (h : IsStateBased R s) : IsIndisputable R s := by
  intro w₁ hw₁ w₂ hw₂; rw [h w₁ hw₁, h w₂ hw₂]

instance (R : W → Finset W) (s : Finset W)
    [DecidableEq W] [Fintype W] : Decidable (IsStateBased R s) := by
  unfold IsStateBased; infer_instance

instance (R : W → Finset W) (s : Finset W)
    [DecidableEq W] [Fintype W] : Decidable (IsIndisputable R s) := by
  unfold IsIndisputable; infer_instance

end Team
