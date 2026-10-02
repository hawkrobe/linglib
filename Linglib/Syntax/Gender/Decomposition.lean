module

public import Mathlib.Data.Fintype.Card
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Syntax.Gender.Basic

/-!
# Feature decompositions of gender

Two decompositions of gender values: the split feature, whose morphological and semantic halves
may match, differ or go missing, and the bivalent [±feminine, ±neuter] presentation of a
sex-based three-gender system.

A split feature has a half legible to morphology and a half legible to semantics. The
halves match on a natural value, only the morphological half is present on an arbitrary
value, and a hybrid value carries mismatched halves, the committee-type nouns that a
classification of single feature tokens by interpretability cannot represent. The bivalent
presentation makes neuter the most specified gender and masculine the least, a containment
pair on the pattern of the person and number presentations.

## Main definitions

* `Gender.SplitFeature`: a feature with a morphological and a semantic half, with its five
  exhaustive cases `IsNatural`, `IsHybrid`, `IsArbitrary`, `IsSemanticOnly` and `IsAbsent`.
* `Gender.Features`: the bivalent [±feminine, ±neuter] features as finsets over the chain
  feminine < neuter, whose well-formed cells are `Features.neuter`, `Features.feminine` and
  `Features.masculine`.

## Implementation notes

* Kramer's calculus of valued gender features on the nominal categorizer lives beside its
  consumer in `Morphology/DistributedMorphology/Categorizer/Gender.lean`, where its heads
  are the non-hybrid split features.
* The bivalent presentation's three-cell bound `Features.card_wellFormed` is a claim about
  the presentation and not about gender systems: Fula has twenty controller genders.
* Hammerly's rejection of both schemes, with masculine a bare gender node and natural
  gender derived at LF, is a single-paper analysis for its study.

## References

* [smith-2015] — the split-feature architecture
* [smith-2021] — the mismatch typology
* [kramer-2015] — interpretable and uninterpretable gender
* [sauerland-2003] — the markedness ordering the bivalent presentation reconstructs
* [sauerland-2008b] — the Dominance test for markedness
* [hammerly-2019]
-/

@[expose] public section

namespace Gender

/-! ### The split-feature architecture -/

/-- A feature split into a morphology-legible half `uF` and a
    semantics-legible half `iF` ([smith-2015]). The halves usually match,
    but may differ (hybrid values) or be singly absent. -/
structure SplitFeature (V : Type*) where
  /-- The half legible to morphology (agreement, exponence). -/
  uF : Option V
  /-- The half legible to semantics (interpretation). -/
  iF : Option V
  deriving DecidableEq, Repr

namespace SplitFeature

variable {V : Type*} (s : SplitFeature V)

/-- A natural (conceptual) value has both halves present and matched, [kramer-2015]'s
interpretable gender in split-feature terms. -/
def IsNatural : Prop := ∃ v, s.uF = some v ∧ s.iF = some v

/-- An arbitrary value has the morphological half only, [kramer-2015]'s uninterpretable gender in
split-feature terms. -/
def IsArbitrary : Prop := (∃ v, s.uF = some v) ∧ s.iF = none

/-- Semantic-only value: interpreted but morphologically inert
    (the half [smith-2015] allows to go missing on the uF side). -/
def IsSemanticOnly : Prop := s.uF = none ∧ ∃ v, s.iF = some v

/-- A hybrid value has both halves present and mismatched, as committee-type nouns do
([smith-2015]), which a classification of single feature tokens by interpretability cannot
represent. -/
def IsHybrid : Prop := ∃ u i, s.uF = some u ∧ s.iF = some i ∧ u ≠ i

/-- A featureless value has both halves absent. -/
def IsAbsent : Prop := s.uF = none ∧ s.iF = none

/-- Every split feature is natural, hybrid, arbitrary, semantic-only, or absent. -/
theorem classify (s : SplitFeature V) :
    s.IsNatural ∨ s.IsHybrid ∨ s.IsArbitrary ∨ s.IsSemanticOnly ∨ s.IsAbsent := by
  obtain ⟨_ | u, _ | i⟩ := s
  · exact .inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  · exact .inr (.inr (.inr (.inl ⟨rfl, i, rfl⟩)))
  · exact .inr (.inr (.inl ⟨⟨u, rfl⟩, rfl⟩))
  · rcases eq_or_ne u i with rfl | h
    · exact .inl ⟨u, rfl, rfl⟩
    · exact .inr (.inl ⟨u, i, rfl, rfl, h⟩)

/-- A hybrid value is not natural. -/
theorem IsHybrid.not_isNatural {s : SplitFeature V} (h : s.IsHybrid) :
    ¬ s.IsNatural := by
  rintro ⟨v, hu, hi⟩
  obtain ⟨u, i, hu', hi', hne⟩ := h
  rw [hu] at hu'
  rw [hi] at hi'
  exact hne ((Option.some.inj hu').symm.trans (Option.some.inj hi'))

end SplitFeature

/-! ### The bivalent presentation: [±feminine, ±neuter]

[sauerland-2003] derives Czech gender agreement under coordination from a markedness ordering on
which masculine is semantically vacuous, feminine presupposes non-masculinity and neuter
presupposes genderlessness (§6, (45)); [sauerland-2008b]'s Dominance test, the gender a mixed
coordination takes, likewise makes masculine less marked than feminine (pp. 63–65). The
presentation here reconstructs the ordering as two binary features with the containment
[+neuter] → [+feminine], so the three genders of a sex-based system are the initial segments of
the chain feminine < neuter, neuter the most specified and masculine the least, as for person and
number (`Syntax/Agreement/ContainmentPair.lean`). -/

/-- The two gender features, neuter depending on feminine. -/
inductive Feature where
  /-- [feminine] holds of non-masculine referents, those feminine and neuter share. -/
  | feminine
  /-- [neuter] holds of referents triggering neuter agreement. -/
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- `Feature.rank` places feminine below neuter on the dependency chain. -/
def Feature.rank : Feature → Fin 2
  | .feminine => 0
  | .neuter => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

instance : LocallyFiniteOrderBot Feature := Fintype.toLocallyFiniteOrderBot

/-- A gender feature bundle is the set of its positive features. -/
abbrev Features := Finset Feature

open Finset in
/-- The neuter is [+feminine, +neuter], the whole chain. -/
def Features.neuter : Features := Iic .neuter

open Finset in
/-- The feminine is [+feminine, −neuter], the chain below neuter. -/
def Features.feminine : Features := Iic .feminine

/-- The masculine is [−feminine, −neuter], the empty bundle. -/
def Features.masculine : Features := ∅

theorem Features.neuter_eq : Features.neuter = {.feminine, .neuter} := by decide

theorem Features.feminine_eq : Features.feminine = {.feminine} := by decide

/-- The bundle with the neuter feature alone violates containment. -/
theorem Features.not_wellFormed_singleton_neuter :
    ¬ IsLowerSet (↑({.neuter} : Features) : Set Feature) := by
  decide

/-- Exactly three bundles pass the containment filter, the three genders. The bound is a claim
about the presentation and not about gender systems. -/
theorem Features.card_wellFormed :
    Fintype.card {gf : Features // IsLowerSet (↑gf : Set Feature)} = 3 := by
  rw [Fintype.card_subtype_isLowerSet]; rfl

/-- Map gender features to the comparative labels. -/
def Features.toGender (f : Features) : Option Gender :=
  if .neuter ∈ f then if .feminine ∈ f then some .neuter else none
  else if .feminine ∈ f then some .feminine else some .masculine

/-- Map comparative labels to gender features (partial — only sex-based
    labels have feature equivalents). -/
def Features.fromGender : Gender → Option Features
  | .neuter    => some Features.neuter
  | .feminine  => some Features.feminine
  | .masculine => some Features.masculine
  | _          => none

/-- A bundle passing the containment filter survives the round trip through its label. -/
theorem Features.fromGender_toGender {f : Features} (h : IsLowerSet (↑f : Set Feature)) :
    f.toGender.bind Features.fromGender = some f := by
  revert f; decide

end Gender
