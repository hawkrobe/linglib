import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Union

/-!
# Team algebra — pure `Finset` combinatorics for team semantics

@cite{anttila-2021} @cite{vaananen-2007} @cite{yang-vaananen-2017}

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

1. **Team partition** (`splitsAs`, `splitsAsNE`): the structural condition
   underlying team-semantic split disjunction.

2. **Frame conditions on accessibility** (`isStateBased`, `isIndisputable`):
   Anttila Definition 2.2.10-equivalent properties of a relation
   `R : W → Finset W` relative to a base team. Used to distinguish
   epistemic and deontic modalities (Aloni 2022 §6.1).

We retain the term "state-based" in `isStateBased` because that is its
established name in the Aloni / Anttila literature — the property holds
of an accessibility relation, not of a team-semantic logic generally.

## Roadmap — team-semantics architecture

The team-semantic logics form a 4-family Hasse lattice over two orthogonal
axes — syntactic (which atoms/connectives are admitted) and semantic
(which closure property the definable team-properties have). Anttila's
dissertation (@cite{anttila-2025}) is the authoritative basic-level
taxonomy. The natural cuts that this `Core/Logic/Team/` substrate
underwrites, once enough Layer-2 consumers land to anchor them:

* **`Theories/Semantics/Bilateral/`** — Family A: BSML, BSML∨, BSML⊘,
  QBSML. Bilateral negation + NE atom. Currently at `Theories/Semantics/
  BSML/` and `QBSML/`; should consolidate. @cite{aloni-anttila-yang-2024}
  is the family's axiomatization paper, @cite{aloni-2022} the founding
  free-choice application, @cite{aloni-vanormondt-2023} the first-order
  extension. Closure: union-closed, empty-state property.
* **`Theories/Semantics/Dependence/`** — Family B: modal dependence logic,
  modal inclusion logic ML(⊆), ML(▽) (@cite{anttila-2025} Ch 5;
  @cite{vaananen-2007}). Closure: downward-closed (dependence),
  union-closed (inclusion).
* **`Theories/Semantics/DualNegation/`** — Family C: modal team logic
  (MTL with Boolean ~), propositional team logic, Hawke &
  Steinert-Threlkeld's logic, propositional dependence logic
  (@cite{anttila-2025} Ch 4). Closure: fully expressive over modally
  definable state properties.
* **`Theories/Semantics/Inquisitive/`** — Family D: InqB, InqML
  (global ∨∨ central; Ciardelli, Roelofsen). Close cousin of BSML∨.

The families are sibling, not nested — none extends another. They share
this substrate (team partitions + frame conditions), the closure-property
predicates in `Core/Logic/Team/Closure.lean`, and the abstract
`Core/Logic/Bilateral/IsBilateral` typeclass. Substrate consumers use
mathlib-direct predicates `IsLowerSet { t | support M φ t }`,
`SupClosed { t | support M φ t }`, and `support M φ ∅` per-`M` rather
than project-specific wrappers — see `Closure.lean`'s docstring for the
shape.

Layer 1 (a generic `Theories/Semantics/TeamSemantics/` parameterizing
over admitted connectives) should NOT be extracted until ≥ 3 systems
have landed and the duplication pattern is concrete. Premature
abstraction would design the typeclass interface against a sample size
of 1; the mathlib algebraic hierarchy got its current shape by being
refactored backward from concrete instances, not designed forward.
-/

namespace Core.Logic.Team

variable {α : Type*} [DecidableEq α]

-- ============================================================================
-- §1 Team partition (split disjunction primitive)
-- ============================================================================

/-- Binary cover: team `s` is the union of teams `t₁` and `t₂`. The two
    sub-teams may overlap; only their union must equal `s`. This is the
    structural condition under team-semantic split disjunction (also called
    *tensor disjunction* in dependence logic; cf. Anttila 2021 Definition
    2.1.5, Yang & Väänänen 2017).

    Argument order `s t₁ t₂` reads as "splits team s into t₁ and t₂".

    Defined as `abbrev` so that `t₁ ∪ t₂ = s` reduces transparently in proofs
    — consumers don't need `unfold splitsAs` and can pattern-match on the
    underlying union equation directly. -/
abbrev splitsAs (s t₁ t₂ : Finset α) : Prop :=
  t₁ ∪ t₂ = s

/-- Binary cover with both parts non-empty. Used by pragmatically-enriched
    split disjunction in BSML+ / QBSML+ (Aloni 2022 §3.3): `[φ ∨ ψ]⁺` requires
    both sub-teams to be non-empty (forced by the NE conjunct propagating
    through enrichment). -/
abbrev splitsAsNE (s t₁ t₂ : Finset α) : Prop :=
  t₁ ∪ t₂ = s ∧ t₁.Nonempty ∧ t₂.Nonempty

theorem splitsAsNE_imp_splitsAs (s t₁ t₂ : Finset α)
    (h : splitsAsNE s t₁ t₂) : splitsAs s t₁ t₂ := h.1

/-- The trivial split: `s = s ∪ ∅`. Used by classical formulas, which are
    supported on the empty team vacuously. -/
theorem splitsAs_self_empty (s : Finset α) : splitsAs s s ∅ :=
  Finset.union_empty s

theorem splitsAs_empty_self (s : Finset α) : splitsAs s ∅ s :=
  Finset.empty_union s

/-- The reflexive split: `s = s ∪ s` (parts may overlap). -/
theorem splitsAs_self_self (s : Finset α) : splitsAs s s s :=
  Finset.union_idempotent s

theorem splitsAs_symm {s t₁ t₂ : Finset α}
    (h : splitsAs s t₁ t₂) : splitsAs s t₂ t₁ :=
  (Finset.union_comm t₂ t₁).trans h

theorem splitsAsNE_symm {s t₁ t₂ : Finset α}
    (h : splitsAsNE s t₁ t₂) : splitsAs s t₂ t₁ ∧ t₂.Nonempty ∧ t₁.Nonempty :=
  ⟨splitsAs_symm h.1, h.2.2, h.2.1⟩

/-- Substate property: if `splitsAs s t₁ t₂`, then `t₁ ⊆ s`. -/
theorem splitsAs_left_subset {s t₁ t₂ : Finset α}
    (h : splitsAs s t₁ t₂) : t₁ ⊆ s :=
  h ▸ Finset.subset_union_left

theorem splitsAs_right_subset {s t₁ t₂ : Finset α}
    (h : splitsAs s t₁ t₂) : t₂ ⊆ s :=
  h ▸ Finset.subset_union_right

instance (s t₁ t₂ : Finset α) : Decidable (splitsAs s t₁ t₂) :=
  decEq _ _

instance (s t₁ t₂ : Finset α) : Decidable (splitsAsNE s t₁ t₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Core.Logic.Team

namespace Core.Logic.Team

variable {W : Type*}

-- ============================================================================
-- §2 Frame conditions on accessibility
-- ============================================================================

/-- `R` is **state-based** on team `s` iff every world in `s` is `R`-accessible
    exactly to `s`. Strictly stronger than indisputability.

    Aloni 2022 Definition 5; Anttila 2021 Definition 4.10-style. The name
    is established in the BSML literature even though we use "team" for
    the underlying object — the property pertains to the accessibility
    relation, not the team itself. -/
def isStateBased (R : W → Finset W) (s : Finset W) : Prop :=
  ∀ w ∈ s, R w = s

/-- `R` is **indisputable** on team `s` iff all worlds in `s` see the same
    set of accessible worlds. Equivalently: `R` is constant on `s`.

    Aloni 2022 Definition 5 (indisputable ↔ deontic-with-knowledgeable-speaker). -/
def isIndisputable (R : W → Finset W) (s : Finset W) : Prop :=
  ∀ w₁ ∈ s, ∀ w₂ ∈ s, R w₁ = R w₂

/-- State-based implies indisputable. -/
theorem isStateBased_imp_isIndisputable (R : W → Finset W) (s : Finset W)
    (h : isStateBased R s) : isIndisputable R s := by
  intro w₁ hw₁ w₂ hw₂; rw [h w₁ hw₁, h w₂ hw₂]

instance (R : W → Finset W) (s : Finset W)
    [DecidableEq W] [Fintype W] : Decidable (isStateBased R s) := by
  unfold isStateBased; infer_instance

instance (R : W → Finset W) (s : Finset W)
    [DecidableEq W] [Fintype W] : Decidable (isIndisputable R s) := by
  unfold isIndisputable; infer_instance

end Core.Logic.Team
