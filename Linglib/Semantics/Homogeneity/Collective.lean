import Linglib.Semantics.Supervaluation.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Generalised homogeneity for collective predicates

[kriz-2016] §5.1's generalisation of the homogeneity gap to collective
predicates via mereological overlap: a predicate is undefined of a
plurality that fails it but overlaps a plurality satisfying it. For
distributive predicates this reduces to supervaluation over atoms
(`generalisedTruthValue_distributive_reduction`); for collectives like
*perform Hamlet* the overlapping witness can be a larger group.

## Main definitions

* `overlaps`: two pluralities share an individual (`¬ Disjoint`).
* `generalisedTruthValue`: trivalent truth over pluralities.

## References

* [M. Križ, *Homogeneity, Non-Maximality, and All*][kriz-2016]
-/

namespace Semantics.Homogeneity

open Semantics.Supervaluation (superTrue)

variable {Atom : Type*} [DecidableEq Atom]

/-- Two pluralities overlap if they share at least one individual. -/
def overlaps (a b : Finset Atom) : Prop := ¬ Disjoint a b

instance (a b : Finset Atom) : Decidable (overlaps a b) :=
  inferInstanceAs (Decidable (¬ Disjoint a b))

/-- Trivalent truth for predicates on pluralities: true if `P` holds of
    `a`, gapped if `a` fails `P` but overlaps a `domain` plurality
    satisfying it, false otherwise. `domain` is the set of relevant
    pluralities — singletons suffice for distributive predicates,
    collectives need larger groups. -/
def generalisedTruthValue (P : Finset Atom → Prop) [DecidablePred P]
    (domain : Finset (Finset Atom)) (a : Finset Atom) : Trivalent :=
  if P a then .true
  else if ∃ b ∈ domain, overlaps a b ∧ P b then .indet
  else .false

/-- The generalised truth value is a genuine three-way partition. -/
theorem generalisedTruthValue_trichotomy (P : Finset Atom → Prop)
    [DecidablePred P] (domain : Finset (Finset Atom)) (a : Finset Atom) :
    generalisedTruthValue P domain a = .true ∨
    generalisedTruthValue P domain a = .false ∨
    generalisedTruthValue P domain a = .indet := by
  simp only [generalisedTruthValue]; split_ifs <;> simp

/-- If `P` holds of `a`, the generalised truth value is true. -/
theorem generalisedTruthValue_eq_true (P : Finset Atom → Prop)
    [DecidablePred P] (domain : Finset (Finset Atom)) (a : Finset Atom)
    (h : P a) : generalisedTruthValue P domain a = .true := by
  simp [generalisedTruthValue, h]

/-- For distributive predicates the generalised definition coincides with
    supervaluation over atoms, when the domain includes all member
    singletons. -/
theorem generalisedTruthValue_distributive_reduction
    (pred : Atom → Prop) [DecidablePred pred] (a : Finset Atom)
    (hne : a.Nonempty) (domain : Finset (Finset Atom))
    (hdomain : ∀ x ∈ a, {x} ∈ domain) :
    generalisedTruthValue (fun s => ∀ x ∈ s, pred x) domain a =
    superTrue pred ⟨a, hne⟩ := by
  unfold generalisedTruthValue superTrue
  by_cases hall : ∀ x ∈ a, pred x
  · rw [if_pos hall, if_pos hall]
  · rw [if_neg hall, if_neg hall]
    by_cases hnone : ∀ x ∈ a, ¬ pred x
    · have hNoWitness : ¬ ∃ b ∈ domain, overlaps a b ∧ ∀ x ∈ b, pred x := by
        rintro ⟨b, _, hov, hPb⟩
        obtain ⟨y, hy⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hov
        rw [Finset.mem_inter] at hy
        exact hnone y hy.1 (hPb y hy.2)
      rw [if_neg hNoWitness, if_pos hnone]
    · push Not at hnone
      obtain ⟨x, hxa, hpx⟩ := hnone
      have hOv : overlaps a {x} := by
        unfold overlaps
        rw [Finset.disjoint_singleton_right]
        exact fun h => h hxa
      have hWitness : ∃ b ∈ domain, overlaps a b ∧ ∀ y ∈ b, pred y :=
        ⟨{x}, hdomain x hxa, hOv,
          fun y hy => by rw [Finset.mem_singleton.mp hy]; exact hpx⟩
      rw [if_pos hWitness, if_neg]
      intro hf; exact hf x hxa hpx

end Semantics.Homogeneity
