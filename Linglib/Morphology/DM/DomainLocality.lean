import Linglib.Morphology.Paradigm.Contiguity

/-!
# Domain-Relativized Contiguity
[moskal-2015a-dissertation] [moskal-2015]
[smith-moskal-xu-kang-bobaljik-2019]

A domain partition assigns each grade of a containment hierarchy a
*domain tag* — abstractly representing the grade's locality unit
(spellout domain / phase / accessibility domain). Within a domain, the
*ABA contiguity constraint applies; across domain boundaries,
ABA-shaped recurrences are admitted.

## Motivation

`Morphology.Containment.realize_const_of_terminal_adjacent` (the
structural-adjacency derivation, [bobaljik-2012]) predicts CMPR-cell =
SPRL-cell for any generable root pattern. Lifted to case (Wardaman
3SG: ABS=*narnaj*, ERG=*narnaj-(j)i*, DAT=*gunga*;
[smith-moskal-xu-kang-bobaljik-2019] §3.6) and number (Yagua 2:
SG=*jiy*, PL=*jiryéy*, DL=*sááda*;
[smith-moskal-xu-kang-bobaljik-2019] §4.2 Table 46), the prediction is
empirically falsified — AAB patterns are attested in both case and
number suppletion.

[smith-moskal-xu-kang-bobaljik-2019] §3.7 attribute the gap to
*locality*: structural adjacency ([bobaljik-2012]) and linear
adjacency ([embick-2010]) are too strict once AAB is admitted (Tamil
dative suppletion across the plural morpheme is "neither linearly nor
structurally adjacent to the root"). They adopt the
[moskal-2015a-dissertation] theory of **accessibility domains (AD)**:
a category-defining node has a delimiting effect that puts
more-distant material outside the AD of the root, blocking it from
conditioning suppletion. Lexical material has such a node (so case
cannot reach the root); pronouns lack it (so case and number can both
condition pronominal suppletion).

## What this substrate models, and what it doesn't

This file represents the **output** of an AD computation projected
onto the grades of a hierarchy: a `DomainPartition` saying, for each
grade, which locality unit it belongs to. The AD theory itself is
*trigger-relative* — a bound on which heads may condition root
suppletion, formalized at rule level as
`SmithMoskalEtAl2019.DomainLocal` on
`Morphology.Containment.ExponenceRule` vocabularies. The substrate is
theory-neutral about how the partition is computed:
[moskal-2015a-dissertation]'s AD is one source, [embick-2010]'s linear
adjacency another (every grade its own one-cell domain),
[bobaljik-2012]'s structural adjacency a third. Consumers state which
projection they want; the substrate doesn't pick.

## Main declarations

* `DomainPartition n Tag` — domain tag per grade
* `ViolatesABAWithin`, `IsContiguousWithin` — *ABA relativized to
  same-domain triples, over `Morphology.Paradigm`
* `isContiguousWithin_trivial_iff` — under the trivial partition this
  is exactly `Morphology.IsContiguous`
-/

namespace Morphology.DomainLocality


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

end Morphology.DomainLocality
