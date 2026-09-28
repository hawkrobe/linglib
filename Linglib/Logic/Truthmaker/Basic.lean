module

public import Mathlib.Data.Set.Sups

/-!
# Truthmaker content

This file defines conjunctive parthood, the containment relation of Kit Fine's theory of
truthmaker content. States are ordered by parthood, with fusion as join, and a unilateral
proposition is the set of states that exactly verify it, so a proposition over states `S` is a
`Set S`. Conjunction is the pointwise fusion `s ⊻ t`, disjunction is the union `s ∪ t`, and
Fine's entailment of `t` by `s` is the inclusion `s ⊆ t`.

A state inexactly verifies `s` when some part of it exactly verifies `s`, that is, when it lies
in `upperClosure s`. Inexact verification obeys the classical clauses: `upperClosure_sups` and
`upperClosure_union` say that the inexact verifiers of `s ⊻ t` and `s ∪ t` are the common and the
pooled inexact verifiers of `s` and `t`.

## Main definitions

* `Truthmaker.IsConjunctivePart t s`: every verifier of `s` contains a verifier of `t`, and every
  verifier of `t` is part of a verifier of `s`.

## Main results

* `Truthmaker.isConjunctivePart_iff`: conjunctive parthood compares upper and lower closures.
* `Truthmaker.IsConjunctivePart.antisymm`: conjunctive parthood is antisymmetric on convex
  propositions.
* `Truthmaker.isConjunctivePart_singleton_right_iff`: parts of a single state are its parts.
* `Truthmaker.isConjunctivePart_sups_left`: a conjunct is a conjunctive part of a conjunction.
* `Truthmaker.isConjunctivePart_union_left_iff`: `s` contains `s ∨ t` only when every verifier of
  `t` is part of a verifier of `s`, so disjunction introduction fails for containment.
* `Truthmaker.isConjunctivePart_iff_sups_eq`: a closed convex proposition contains `t` exactly
  when conjoining `t` leaves it unchanged.

## Implementation notes

Fine defines conjunctive parthood only between propositions with a verifier. The relation here is
total, and the empty proposition is a conjunctive part only of itself. Fine's closure condition
asks for closure under arbitrary nonempty fusions, of which `SupClosed` is the finitary version.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [K. Fine, *Truthmaker Semantics* (2017)][fine-2017]
* [M. Jago, *Truthmaker Semantics* (2026)][jago-2026]
-/

@[expose] public section

open SetFamily

namespace Truthmaker

variable {S : Type*}

section Preorder

variable [Preorder S] {s t u : Set S}

/-- A proposition `t` is a conjunctive part of `s`, or `s` contains `t`, if every verifier of `s`
contains a verifier of `t` and every verifier of `t` is part of a verifier of `s`. -/
def IsConjunctivePart (t s : Set S) : Prop :=
  s ⊆ upperClosure t ∧ t ⊆ lowerClosure s

/-- Conjunctive parthood asks that every inexact verifier of `s` inexactly verify `t`, and that
every state below a verifier of `t` lie below a verifier of `s`. -/
theorem isConjunctivePart_iff :
    IsConjunctivePart t s ↔ upperClosure t ≤ upperClosure s ∧ lowerClosure t ≤ lowerClosure s := by
  rw [le_upperClosure, lowerClosure_le, IsConjunctivePart]

@[refl]
theorem IsConjunctivePart.refl (s : Set S) : IsConjunctivePart s s :=
  ⟨subset_upperClosure, subset_lowerClosure⟩

theorem IsConjunctivePart.rfl : IsConjunctivePart s s :=
  .refl s

theorem IsConjunctivePart.trans (hut : IsConjunctivePart u t) (hts : IsConjunctivePart t s) :
    IsConjunctivePart u s :=
  have h₁ := isConjunctivePart_iff.1 hut
  have h₂ := isConjunctivePart_iff.1 hts
  isConjunctivePart_iff.2 ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Two convex propositions that are conjunctive parts of each other are equal. -/
theorem IsConjunctivePart.antisymm (hs : s.OrdConnected) (ht : t.OrdConnected)
    (hts : IsConjunctivePart t s) (hst : IsConjunctivePart s t) : s = t := by
  obtain ⟨hu₁, hl₁⟩ := isConjunctivePart_iff.1 hts
  obtain ⟨hu₂, hl₂⟩ := isConjunctivePart_iff.1 hst
  rw [← hs.upperClosure_inter_lowerClosure, ← ht.upperClosure_inter_lowerClosure,
    le_antisymm hu₂ hu₁, le_antisymm hl₂ hl₁]

/-- A proposition with a verifier is a conjunctive part of the proposition verified by `a` alone
exactly when each of its verifiers is part of `a`. -/
theorem isConjunctivePart_singleton_right_iff (ht : t.Nonempty) {a : S} :
    IsConjunctivePart t {a} ↔ ∀ b ∈ t, b ≤ a := by
  refine ⟨fun h b hb ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, rfl, hba⟩ := mem_lowerClosure.1 (h.2 hb)
    exact hba
  · obtain ⟨b, hb⟩ := ht
    exact ⟨Set.singleton_subset_iff.2 (mem_upperClosure.2 ⟨b, hb, h b hb⟩),
      fun c hc ↦ mem_lowerClosure.2 ⟨a, rfl, h c hc⟩⟩

/-- The proposition verified by `b` alone is a conjunctive part of a proposition with a verifier
exactly when `b` is part of each of its verifiers. -/
theorem isConjunctivePart_singleton_left_iff (hs : s.Nonempty) {b : S} :
    IsConjunctivePart {b} s ↔ ∀ a ∈ s, b ≤ a := by
  refine ⟨fun h a ha ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, rfl, hba⟩ := mem_upperClosure.1 (h.1 ha)
    exact hba
  · obtain ⟨a, ha⟩ := hs
    exact ⟨fun c hc ↦ mem_upperClosure.2 ⟨b, rfl, h c hc⟩,
      Set.singleton_subset_iff.2 (mem_lowerClosure.2 ⟨a, ha, h a ha⟩)⟩

@[simp]
theorem isConjunctivePart_singleton_singleton {a b : S} :
    IsConjunctivePart {b} {a} ↔ b ≤ a := by
  simp [isConjunctivePart_singleton_right_iff]

/-- A proposition `s` contains the disjunction `s ∪ t` exactly when every verifier of `t` is part
of a verifier of `s`. -/
theorem isConjunctivePart_union_left_iff : IsConjunctivePart (s ∪ t) s ↔ t ⊆ lowerClosure s :=
  ⟨fun h ↦ Set.subset_union_right.trans h.2, fun h ↦
    ⟨Set.subset_union_left.trans subset_upperClosure, Set.union_subset subset_lowerClosure h⟩⟩

end Preorder

section SemilatticeSup

variable [SemilatticeSup S] {s t : Set S}

/-- A conjunct is a conjunctive part of a conjunction whose other conjunct has a verifier. -/
theorem isConjunctivePart_sups_left (ht : t.Nonempty) : IsConjunctivePart s (s ⊻ t) :=
  let ⟨b, hb⟩ := ht
  ⟨Set.sups_subset_iff.2 fun a ha _ _ ↦ mem_upperClosure.2 ⟨a, ha, le_sup_left⟩,
    fun a ha ↦ mem_lowerClosure.2 ⟨a ⊔ b, Set.sup_mem_sups ha hb, le_sup_left⟩⟩

/-- A conjunct is a conjunctive part of a conjunction whose other conjunct has a verifier. -/
theorem isConjunctivePart_sups_right (hs : s.Nonempty) : IsConjunctivePart t (s ⊻ t) :=
  Set.sups_comm t s ▸ isConjunctivePart_sups_left hs

/-- A closed, convex proposition `s` with a verifier contains `t` exactly when `s ⊻ t = s`. -/
theorem isConjunctivePart_iff_sups_eq (hs : s.Nonempty) (hsc : SupClosed s)
    (hso : s.OrdConnected) : IsConjunctivePart t s ↔ s ⊻ t = s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ isConjunctivePart_sups_right hs⟩
  refine (Set.sups_subset_iff.2 fun a ha b hb ↦ ?_).antisymm fun a ha ↦ ?_
  · obtain ⟨c, hc, hbc⟩ := mem_lowerClosure.1 (h.2 hb)
    exact hso.out ha (hsc ha hc) ⟨le_sup_left, sup_le_sup_left hbc a⟩
  · obtain ⟨b, hb, hba⟩ := mem_upperClosure.1 (h.1 ha)
    exact Set.mem_sups.2 ⟨a, ha, b, hb, sup_eq_left.2 hba⟩

end SemilatticeSup

end Truthmaker
