import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Rel
import Linglib.Semantics.Mereology

/-!
# Cumulative predication

This file defines the cumulative operator `**` on relations between individuals. In the
coverage form of [beck-sauerland-2000], `**R` holds of two finite pluralities when every atom
of the first is `R`-related to some atom of the second and conversely; in the closure form of
[krifka-1986] and [sternefeld-1998], `**R` is the smallest relation containing `R` and closed
under componentwise sum, which is Link's `*` on the product semilattice. The two agree on
nonempty finite sets of individuals.

## Definitions

* `Plurality.Cumulativity.Cumulative R x y`: bidirectional coverage of `x` and `y` by `R`.
* `Plurality.Cumulativity.Cumulation R x y`: the closure form, on any pair of
  join-semilattices.

## Main results

* `Plurality.Cumulativity.cumulative_iff_subset_preimage_image`: coverage is inclusion of `x`
  in the `SetRel.preimage` of `y` and of `y` in the `SetRel.image` of `x`.
* `Plurality.Cumulativity.Cumulative.union`, `Plurality.Cumulativity.singleton_right_cumulative`:
  coverage is closed under componentwise union and collapses to distribution over a singleton.
* `Plurality.Cumulativity.cumulation_iff_of_cum`: a cumulative relation is its own cumulation.
* `Plurality.Cumulativity.cumulation_map_singleton`: on finite sets, the closure form of a
  relation between individuals is coverage of a nonempty pair.

## References

* [M. Krifka, *Nominalreferenz und Zeitkonstitution* (1986)][krifka-1986]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
* [S. Beck and U. Sauerland, *Cumulation is needed: A reply to Winter (2000)*
  (2000)][beck-sauerland-2000]
* [G. Link, *The logical analysis of plurals and mass terms* (1983)][link-1983]
-/

namespace Plurality.Cumulativity

variable {A B : Type*} {R : A → B → Prop} {x : Finset A} {y : Finset B}

/-! ### Coverage form -/

/-- Bidirectional coverage: every atom of `x` is `R`-related to some atom of `y` and every atom
of `y` to some atom of `x` ([beck-sauerland-2000]). -/
def Cumulative (R : A → B → Prop) (x : Finset A) (y : Finset B) : Prop :=
  (∀ a ∈ x, ∃ b ∈ y, R a b) ∧ (∀ b ∈ y, ∃ a ∈ x, R a b)

instance (R : A → B → Prop) [DecidableRel R] (x : Finset A) (y : Finset B) :
    Decidable (Cumulative R x y) := by
  unfold Cumulative; infer_instance

theorem cumulative_iff_subset_preimage_image :
    Cumulative R x y ↔
      (x : Set A) ⊆ SetRel.preimage {p | R p.1 p.2} y ∧
        (y : Set B) ⊆ SetRel.image {p | R p.1 p.2} x :=
  Iff.rfl

@[simp]
theorem cumulative_singleton (R : A → B → Prop) (a : A) (b : B) :
    Cumulative R {a} {b} ↔ R a b := by
  simp [Cumulative]

/-- Coverage is closed under componentwise union. -/
theorem Cumulative.union [DecidableEq A] [DecidableEq B] {x' : Finset A} {y' : Finset B}
    (h : Cumulative R x y) (h' : Cumulative R x' y') : Cumulative R (x ∪ x') (y ∪ y') := by
  refine ⟨λ a ha => ?_, λ b hb => ?_⟩
  · rcases Finset.mem_union.1 ha with ha | ha
    · obtain ⟨b, hb, hab⟩ := h.1 a ha
      exact ⟨b, Finset.mem_union_left _ hb, hab⟩
    · obtain ⟨b, hb, hab⟩ := h'.1 a ha
      exact ⟨b, Finset.mem_union_right _ hb, hab⟩
  · rcases Finset.mem_union.1 hb with hb | hb
    · obtain ⟨a, ha, hab⟩ := h.2 b hb
      exact ⟨a, Finset.mem_union_left _ ha, hab⟩
    · obtain ⟨a, ha, hab⟩ := h'.2 b hb
      exact ⟨a, Finset.mem_union_right _ ha, hab⟩

/-- Over a singleton right argument, coverage of a nonempty plurality is distribution: the
number effect of [johnston-2023]. -/
theorem singleton_right_cumulative (hne : x.Nonempty) (b : B) :
    Cumulative R x {b} ↔ ∀ a ∈ x, R a b := by
  simp only [Cumulative, Finset.mem_singleton, exists_eq_left, forall_eq]
  refine ⟨And.left, λ h => ⟨h, ?_⟩⟩
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, ha, h a ha⟩

/-! ### Closure form

Krifka's `**R` is Link's `*` applied to `R` as a predicate on the product semilattice: the
smallest relation containing `R` and closed under componentwise sum. -/

section Closure

open Mereology

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β] {R S : α → β → Prop}
  {x x' : α} {y y' : β}

/-- The cumulation `**R` of a relation ([krifka-1986]; [sternefeld-1998]): the closure of `R`
under componentwise sum, `Mereology.AlgClosure` on the product semilattice. -/
def Cumulation (R : α → β → Prop) (x : α) (y : β) : Prop :=
  AlgClosure (Function.uncurry R) (x, y)

theorem Cumulation.of_rel (h : R x y) : Cumulation R x y := AlgClosure.base h

theorem Cumulation.sup (h : Cumulation R x y) (h' : Cumulation R x' y') :
    Cumulation R (x ⊔ x') (y ⊔ y') :=
  AlgClosure.sum h h'

theorem Cumulation.mono (hRS : ∀ x y, R x y → S x y) (h : Cumulation R x y) :
    Cumulation S x y :=
  algClosure_mono (P := Function.uncurry R) (λ p => hRS p.1 p.2) _ h

/-- A cumulative relation is its own cumulation. -/
theorem cumulation_iff_of_cum (hR : CUM (Function.uncurry R)) : Cumulation R x y ↔ R x y :=
  algClosure_of_cum hR

end Closure

/-! ### Sets of individuals -/

section Finset

open Mereology

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- On finite sets, `**` of a relation between individuals, taken as singletons, is
bidirectional coverage of a nonempty pair: the closure form of [krifka-1986] and the coverage
form of [beck-sauerland-2000] agree away from the empty pair. -/
theorem cumulation_map_singleton (R : A → B → Prop) (x : Finset A) (y : Finset B) :
    Cumulation (Relation.Map R ({·}) ({·})) x y ↔ x.Nonempty ∧ Cumulative R x y := by
  constructor
  · suffices ∀ p : Finset A × Finset B,
        AlgClosure (Function.uncurry (Relation.Map R ({·}) ({·}))) p →
          p.1.Nonempty ∧ Cumulative R p.1 p.2 from this (x, y)
    intro p h
    induction h with
    | @base p h =>
      obtain ⟨x, y⟩ := p
      change ∃ a b, R a b ∧ ({a} : Finset A) = x ∧ ({b} : Finset B) = y at h
      obtain ⟨a, b, hab, rfl, rfl⟩ := h
      exact ⟨Finset.singleton_nonempty a, (cumulative_singleton R a b).2 hab⟩
    | sum _ _ ih ih' => exact ⟨ih.1.mono Finset.subset_union_left, ih.2.union ih'.2⟩
  · rintro ⟨hx, hl, hr⟩
    have : Nonempty B := hx.elim λ a ha => (hl a ha).elim λ b _ => ⟨b⟩
    have : Nonempty A := hx.elim λ a _ => ⟨a⟩
    choose! f hf hRf using hl
    choose! g hg hRg using hr
    have hy : y.Nonempty := hx.elim λ a ha => ⟨f a, hf a ha⟩
    have key : x.sup' hx (λ a => ({a}, {f a})) ⊔ y.sup' hy (λ b => ({g b}, {b})) = (x, y) := by
      refine le_antisymm (sup_le ((Finset.sup'_le_iff _ _).2 λ a ha => ?_)
        ((Finset.sup'_le_iff _ _).2 λ b hb => ?_))
        (Prod.le_def.2 ⟨Finset.subset_iff.2 λ a ha => ?_, Finset.subset_iff.2 λ b hb => ?_⟩)
      · exact Prod.le_def.2
          ⟨Finset.singleton_subset_iff.2 ha, Finset.singleton_subset_iff.2 (hf a ha)⟩
      · exact Prod.le_def.2
          ⟨Finset.singleton_subset_iff.2 (hg b hb), Finset.singleton_subset_iff.2 hb⟩
      · have hle :=
          Prod.le_def.1 (Finset.le_sup' (λ a => (({a} : Finset A), ({f a} : Finset B))) ha)
        rw [Prod.fst_sup, Finset.sup_eq_union]
        exact Finset.mem_union_left _ (Finset.singleton_subset_iff.1 hle.1)
      · have hle :=
          Prod.le_def.1 (Finset.le_sup' (λ b => (({g b} : Finset A), ({b} : Finset B))) hb)
        rw [Prod.snd_sup, Finset.sup_eq_union]
        exact Finset.mem_union_right _ (Finset.singleton_subset_iff.1 hle.2)
    show AlgClosure _ (x, y)
    rw [← key]
    exact AlgClosure.sum (algClosure_finsetSup' hx λ a ha => .base ⟨a, f a, hRf a ha, rfl, rfl⟩)
      (algClosure_finsetSup' hy λ b hb => .base ⟨g b, b, hRg b hb, rfl, rfl⟩)

end Finset

end Plurality.Cumulativity
