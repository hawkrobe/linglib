import Mathlib.Data.Fintype.Card
import Linglib.Syntax.Agreement.ContainmentPair
import Linglib.Syntax.Gender.Basic

/-!
# Feature decompositions of gender

This file defines two decompositions of gender values: the split feature, whose
morphological and semantic halves may match, differ or go missing, and the bivalent
[±feminine, ±neuter] presentation of a sex-based three-gender system.

A split feature has a half legible to morphology and a half legible to semantics. The
halves match on a natural value, only the morphological half is present on an arbitrary
value, and a hybrid value carries mismatched halves, the committee-type nouns that a
classification of single feature tokens by interpretability cannot represent. The bivalent
presentation makes neuter the most specified gender and masculine the least, a containment
pair on the pattern of the person and number presentations.

## Main definitions

* `Gender.SplitFeature`: a feature with a morphological and a semantic half, with its five
  exhaustive cases `IsNatural`, `IsHybrid`, `IsArbitrary`, `IsSemanticOnly` and `IsAbsent`.
* `Gender.Features`: the bivalent [±feminine, ±neuter] features, a `ContainmentPairLike`
  presentation whose well-formed cells are `Features.neuter`, `Features.feminine` and
  `Features.masculine`.

## Implementation notes

* Kramer's calculus of valued gender features on the nominal categorizer lives beside its
  consumer in `Morphology/DistributedMorphology/Categorizer/Gender.lean`, where its heads
  are the non-hybrid split features.
* The bivalent presentation's three-cell bound is `ContainmentPairLike.no_four_way`, a claim
  about the presentation and not about gender systems: Fula has twenty controller genders.
* Hammerly's rejection of both schemes, with masculine a bare gender node and natural
  gender derived at LF, is a single-paper analysis for its study.

## References

* [smith-2015] — the split-feature architecture
* [smith-2021] — the mismatch typology
* [kramer-2015] — interpretable and uninterpretable gender
* [sauerland-2003] — the markedness ordering the bivalent presentation reconstructs
* [hammerly-2019]
-/

open Agreement

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

/-- Natural (conceptual) value: both halves present and matched —
    [kramer-2015]'s interpretable gender in split-feature terms. -/
def IsNatural : Prop := ∃ v, s.uF = some v ∧ s.iF = some v

/-- Arbitrary value: morphological half only — [kramer-2015]'s
    uninterpretable gender in split-feature terms. -/
def IsArbitrary : Prop := (∃ v, s.uF = some v) ∧ s.iF = none

/-- Semantic-only value: interpreted but morphologically inert
    (the half [smith-2015] allows to go missing on the uF side). -/
def IsSemanticOnly : Prop := s.uF = none ∧ ∃ v, s.iF = some v

/-- Hybrid value: both halves present and mismatched — committee-type
    nouns ([smith-2015]); unrepresentable in an interpretability
    classification of single feature tokens. -/
def IsHybrid : Prop := ∃ u i, s.uF = some u ∧ s.iF = some i ∧ u ≠ i

/-- Featureless: both halves absent. -/
def IsAbsent : Prop := s.uF = none ∧ s.iF = none

/-- The five cases are exhaustive: every split feature is natural, hybrid,
    arbitrary, semantic-only, or absent. -/
theorem classify (s : SplitFeature V) :
    s.IsNatural ∨ s.IsHybrid ∨ s.IsArbitrary ∨ s.IsSemanticOnly ∨ s.IsAbsent := by
  obtain ⟨_ | u, _ | i⟩ := s
  · exact .inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))
  · exact .inr (.inr (.inr (.inl ⟨rfl, i, rfl⟩)))
  · exact .inr (.inr (.inl ⟨⟨u, rfl⟩, rfl⟩))
  · rcases eq_or_ne u i with rfl | h
    · exact .inl ⟨u, rfl, rfl⟩
    · exact .inr (.inl ⟨u, i, rfl, rfl, h⟩)

/-- A hybrid value is not natural: the mismatch is real. -/
theorem IsHybrid.not_isNatural {s : SplitFeature V} (h : s.IsHybrid) :
    ¬ s.IsNatural := by
  rintro ⟨v, hu, hi⟩
  obtain ⟨u, i, hu', hi', hne⟩ := h
  rw [hu] at hu'
  rw [hi] at hi'
  exact hne ((Option.some.inj hu').symm.trans (Option.some.inj hi'))

end SplitFeature

/-! ### The bivalent presentation: [±feminine, ±neuter]

A reconstruction of [sauerland-2003]'s markedness ordering of sex-based gender, on which
masculine is semantically vacuous, feminine presupposes non-masculinity and neuter
presupposes genderlessness, as two binary features with the containment
[+neuter] → [+feminine]: neuter is the most specified gender, as singular is for number and
first person for person, and masculine the least. The paper itself states no features; the
three well-formed combinations are the three genders of a sex-based system, and the scheme
parallels person [±author] ⊂ [±participant] and number [±atomic] ⊂ [±minimal], all three
`ContainmentPairLike` presentations of one skeleton (`Syntax/Agreement/ContainmentPair.lean`). -/

/-- The two gender features, neuter depending on feminine, reconstructing
[sauerland-2003]'s markedness ordering. -/
inductive Feature where
  /-- [feminine]: non-masculine, the value feminine and neuter share. -/
  | feminine
  /-- [neuter]: the referent triggers neuter agreement. -/
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- Position on the dependency chain, feminine below neuter. -/
def Feature.rank : Feature → Fin 2
  | .feminine => 0
  | .neuter => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

/-- A gender feature bundle: the positive features. The three well-formed bundles are the
three sex-based genders: neuter [+feminine, +neuter], feminine [+feminine, −neuter],
masculine [−feminine, −neuter]. -/
abbrev Features := Finset Feature

/-- Neuter features: [+feminine, +neuter]. -/
def Features.neuter : Features := {.feminine, .neuter}

/-- Feminine features: [+feminine, −neuter]. -/
def Features.feminine : Features := {.feminine}

/-- Masculine features: [−feminine, −neuter]. -/
def Features.masculine : Features := ∅

/-- The gender features as the two features of a containment pair, feminine the outer and
neuter the inner. -/
def featureEquiv : Feature ≃ ContainmentPair.Feature where
  toFun
    | .feminine => .outer
    | .neuter => .inner
  invFun
    | .outer => .feminine
    | .inner => .neuter
  left_inv f := by cases f <;> rfl
  right_inv f := by cases f <;> rfl

/-- The bundles as containment pairs. -/
def featuresEquiv : Features ≃ ContainmentPair := featureEquiv.finsetCongr

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

/-- The three genders land on the three well-formed cells. -/
@[simp] theorem Features.toPair_neuter :
    ContainmentPairLike.toPair Features.neuter = .maximal := by decide
@[simp] theorem Features.toPair_feminine :
    ContainmentPairLike.toPair Features.feminine = .intermediate := by decide
@[simp] theorem Features.toPair_masculine :
    ContainmentPairLike.toPair Features.masculine = .minimal := by decide

/-- Well-formedness: [+neuter] → [+feminine], neuter entails feminine in the feature
geometry, inherited from `ContainmentPair.WellFormed`. -/
abbrev Features.WellFormed (gf : Features) : Prop :=
  ContainmentPairLike.WellFormed gf

@[simp] theorem Features.neuter_wellFormed : Features.neuter.WellFormed := by decide
@[simp] theorem Features.feminine_wellFormed : Features.feminine.WellFormed := by decide
@[simp] theorem Features.masculine_wellFormed : Features.masculine.WellFormed := by decide

/-- The bundle with the neuter feature alone is the one that violates containment. -/
theorem Features.not_wellFormed_singleton_neuter : ¬ ({.neuter} : Features).WellFormed := by
  decide

/-- Exactly three well-formed bundles, the three genders, the carrier count of the
containment chain. -/
theorem Features.card_wellFormed :
    Fintype.card {gf : Features // gf.WellFormed} = 3 := by decide

/-- Containment: [+neuter] → [+feminine] for all well-formed bundles. -/
theorem Features.feminine_of_neuter :
    ∀ f : Features, f.WellFormed → .neuter ∈ f → .feminine ∈ f := by
  decide

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

/-- A well-formed feature survives the round trip through its label. -/
theorem Features.fromGender_toGender {f : Features} (h : f.WellFormed) :
    f.toGender.bind Features.fromGender = some f := by
  revert f; decide

end Gender
