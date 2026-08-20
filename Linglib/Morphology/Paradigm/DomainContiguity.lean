import Linglib.Morphology.Paradigm.Contiguity

/-!
# Domain-relativized contiguity

A domain partition assigns each grade of a containment hierarchy a
*domain tag* — abstractly representing the grade's locality unit
(spellout domain / phase / accessibility domain). Within a domain, the
*ABA contiguity constraint applies; across domain boundaries,
ABA-shaped recurrences are admitted.

## Motivation

Structural adjacency ([bobaljik-2012]) predicts no ABA-shaped
recurrences anywhere in a containment hierarchy, but AAB patterns
attested in case and number suppletion falsify the universal form of
the prediction (Wardaman case, Yagua number;
[smith-moskal-xu-kang-bobaljik-2019], whose study file carries the
data). [smith-moskal-xu-kang-bobaljik-2019] attribute the gap to
locality, adopting [moskal-2015a-dissertation]'s accessibility domains:
a category-defining node delimits the material that can condition root
suppletion, so *ABA holds within a domain and ABA shapes across a
domain boundary are admitted.

## What this substrate models, and what it doesn't

A `DomainPartition` is the **output** of a locality computation
projected onto the grades: which locality unit each grade belongs to.
The substrate is theory-neutral about the source —
[moskal-2015a-dissertation]'s accessibility domains cut the hierarchy
at a delimiting node (`DomainPartition.threshold`), [embick-2010]'s
linear adjacency puts every grade in its own one-cell domain,
[bobaljik-2012]'s structural adjacency uses the trivial partition.
Consumers state which projection they want. The trigger-relative rule
side is `SmithMoskalEtAl2019.DomainLocal`.

## Main declarations

* `DomainPartition n Tag` — domain tag per grade;
  `DomainPartition.IsConvex`, `DomainPartition.threshold` — the
  interval-shaped partitions locality theories generate
* `ViolatesABAWithin`, `IsContiguousWithin` — *ABA relativized to
  same-domain triples, over `Morphology.Paradigm`
* `isContiguousWithin_trivial_iff` — under the trivial partition this
  is exactly `Morphology.IsContiguous`
* `violatesABAWithin_iff_of_convex` — for convex partitions the check
  needs only the outer grades to share a domain
-/

namespace Morphology

variable {n : ℕ} {Tag F : Type*}

/-- A domain partition assigns each grade of an `n`-grade hierarchy a
domain tag. Polymorphic over the tag type so consumers can use
whatever tag type their analysis demands. -/
abbrev DomainPartition (n : ℕ) (Tag : Type*) : Type _ := Fin n → Tag

/-- Two grades lie in the same domain. -/
abbrev SameDomain (π : DomainPartition n Tag) (i j : Fin n) : Prop :=
  π i = π j

instance [DecidableEq Tag] (π : DomainPartition n Tag) (i j : Fin n) :
    Decidable (SameDomain π i j) :=
  inferInstanceAs (Decidable (_ = _))

/-- The trivial partition: every grade in one domain. -/
abbrev DomainPartition.trivial (n : ℕ) : DomainPartition n Unit := λ _ => ()

/-- A partition is convex when its domains are intervals of the
hierarchy: anything between two same-domain grades lies in their
domain. Locality theories generate convex partitions — an accessibility
domain is the initial segment below the delimiting node
([moskal-2015a-dissertation]). -/
def DomainPartition.IsConvex (π : DomainPartition n Tag) : Prop :=
  ∀ ⦃i j k : Fin n⦄, i ≤ j → j ≤ k → SameDomain π i k → SameDomain π i j

/-- The threshold partition: grades below `t` inside the root's domain,
grades from `t` up outside it — the shape of an accessibility-domain
cut at a category-defining node ([moskal-2015a-dissertation]). -/
def DomainPartition.threshold (n t : ℕ) : DomainPartition n Bool :=
  λ i => decide ((i : ℕ) < t)

/-- Threshold partitions are convex. -/
theorem DomainPartition.threshold_isConvex (n t : ℕ) :
    (threshold n t).IsConvex := by
  intro i j k hij hjk h
  simp only [SameDomain, threshold, decide_eq_decide] at h ⊢
  have hij' : (i : ℕ) ≤ j := hij
  have hjk' : (j : ℕ) ≤ k := hjk
  omega

/-- A pattern violates the domain-relativized *ABA constraint: some
form recurs across a distinct intervening form, with all three grades
in the same domain. -/
def ViolatesABAWithin (π : DomainPartition n Tag) (p : Paradigm n F) : Prop :=
  ∃ i j k : Fin n, i < j ∧ j < k ∧
    SameDomain π i j ∧ SameDomain π i k ∧ p i = p k ∧ p i ≠ p j

instance [DecidableEq Tag] [DecidableEq F] (π : DomainPartition n Tag)
    (p : Paradigm n F) : Decidable (ViolatesABAWithin π p) := by
  unfold ViolatesABAWithin; infer_instance

/-- Domain-relativized contiguity: no within-domain *ABA violation. -/
def IsContiguousWithin (π : DomainPartition n Tag) (p : Paradigm n F) : Prop :=
  ¬ ViolatesABAWithin π p

instance [DecidableEq Tag] [DecidableEq F] (π : DomainPartition n Tag)
    (p : Paradigm n F) : Decidable (IsContiguousWithin π p) :=
  inferInstanceAs (Decidable (¬ _))

/-- For a convex partition the within-domain *ABA check needs only the
outer grades to share a domain: the intervener is trapped between
them. -/
theorem violatesABAWithin_iff_of_convex {π : DomainPartition n Tag}
    (hπ : π.IsConvex) (p : Paradigm n F) :
    ViolatesABAWithin π p ↔
      ∃ i j k : Fin n, i < j ∧ j < k ∧ SameDomain π i k
        ∧ p i = p k ∧ p i ≠ p j := by
  constructor
  · rintro ⟨i, j, k, hij, hjk, -, hik, heq, hne⟩
    exact ⟨i, j, k, hij, hjk, hik, heq, hne⟩
  · rintro ⟨i, j, k, hij, hjk, hik, heq, hne⟩
    exact ⟨i, j, k, hij, hjk, hπ hij.le hjk.le hik, hik, heq, hne⟩

/-- Under the trivial partition, domain-relativized contiguity is
exactly the universal contiguity predicate. -/
theorem isContiguousWithin_trivial_iff (p : Paradigm n F) :
    IsContiguousWithin (DomainPartition.trivial n) p ↔ IsContiguous p := by
  constructor
  · intro h i j k hij hjk heq
    by_contra hne
    have hij' : i < j := hij.lt_of_ne (λ he => hne (he ▸ rfl))
    have hjk' : j < k := by
      rcases hjk.lt_or_eq with h' | rfl
      · exact h'
      · exact absurd heq hne
    exact h ⟨i, j, k, hij', hjk', rfl, rfl, heq, hne⟩
  · rintro hp ⟨i, j, k, hij, hjk, -, -, heq, hne⟩
    exact hne (hp hij.le hjk.le heq)

/-! ### Smoke tests

Trivial-partition behavior matches the universal predicate;
across-domain examples show ABA-shapes are admitted when the outer
grades fall in different domains. -/

example : IsContiguousWithin (DomainPartition.trivial 3)
    (![0, 1, 1] : Paradigm 3 ℕ) := by decide

example : ViolatesABAWithin (DomainPartition.trivial 3)
    (![0, 1, 0] : Paradigm 3 ℕ) := by decide

example : IsContiguousWithin (DomainPartition.trivial 3)
    (![0, 0, 1] : Paradigm 3 ℕ) := by decide

/-- An ABA shape with the final grade in its own domain: the
within-domain check does not fire — the universal predicate would
reject this pattern; the domain-relativized one permits it. -/
example : IsContiguousWithin (![false, false, true] : DomainPartition 3 Bool)
    (![0, 1, 0] : Paradigm 3 ℕ) := by decide

end Morphology
