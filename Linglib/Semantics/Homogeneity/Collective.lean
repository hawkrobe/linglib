module

public import Linglib.Semantics.Supervaluation
public import Mathlib.Data.Finset.Powerset

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

@[expose] public section

namespace Homogeneity

open Semantics.Supervaluation (superTrue superTrue_true_iff superTrue_false_iff
  superTrue_indet_iff)

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
  rcases h : superTrue pred ⟨a, hne⟩ with _ | _ | _
  · exact generalisedTruthValue_eq_true _ _ _ ((superTrue_true_iff _ _).1 h)
  · have hnone := (superTrue_false_iff _ _).1 h
    obtain ⟨x, hx⟩ := hne
    rw [generalisedTruthValue, ite_eq_right (fun hall => hnone x hx (hall x hx)), ite_eq_right]
    rintro ⟨b, _, hov, hPb⟩
    obtain ⟨y, hya, hyb⟩ := Finset.not_disjoint_iff.1 hov
    exact hnone y hya (hPb y hyb)
  · obtain ⟨⟨x, hxa, hpx⟩, y, hya, hpy⟩ := (superTrue_indet_iff _ _).1 h
    rw [generalisedTruthValue, ite_eq_right (fun hall => hpy (hall y hya)), ite_eq_left]
    exact ⟨{x}, hdomain x hxa, Finset.not_disjoint_iff.2 ⟨x, hxa, Finset.mem_singleton_self x⟩,
      fun z hz => Finset.mem_singleton.1 hz ▸ hpx⟩

end Homogeneity
