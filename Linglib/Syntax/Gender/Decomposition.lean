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

/-- Bivalent gender features [±feminine, ±neuter], reconstructing [sauerland-2003]'s
    markedness ordering. The three well-formed combinations yield the three sex-based
    genders: neuter [+feminine, +neuter], feminine [+feminine, −neuter], masculine
    [−feminine, −neuter]. -/
structure Features where
  /-- [+feminine]: non-masculine, the value feminine and neuter share. -/
  isFeminine : Bool
  /-- [+neuter]: referent triggers neuter agreement. -/
  isNeuter : Bool
  deriving DecidableEq, Repr, Fintype

/-- Neuter features: [+feminine, +neuter]. -/
def Features.neuter : Features := ⟨true, true⟩

/-- Feminine features: [+feminine, −neuter]. -/
def Features.feminine : Features := ⟨true, false⟩

/-- Masculine features: [−feminine, −neuter]. -/
def Features.masculine : Features := ⟨false, false⟩

/-- The `[±feminine, ±neuter]` decomposition is carrier-equivalent to the
    containment pair: `outer` = feminine, `inner` = neuter — one edge of the
    φ-feature iso-web (`phiKernelEquiv, Studies/Harbour2016.lean`). -/
def featuresEquiv : Features ≃ ContainmentPair where
  toFun f := ⟨f.isFeminine, f.isNeuter⟩
  invFun p := ⟨p.outer, p.inner⟩
  left_inv := λ ⟨_, _⟩ => rfl
  right_inv := λ ⟨_, _⟩ => rfl

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

/-- The three genders land on the three well-formed cells. -/
@[simp] theorem Features.toPair_neuter :
    ContainmentPairLike.toPair Features.neuter = .maximal := rfl
@[simp] theorem Features.toPair_feminine :
    ContainmentPairLike.toPair Features.feminine = .intermediate := rfl
@[simp] theorem Features.toPair_masculine :
    ContainmentPairLike.toPair Features.masculine = .minimal := rfl

/-- Well-formedness: [+neuter] → [+feminine] — neuter entails feminine in
    the feature geometry, inherited from `ContainmentPair.WellFormed`. -/
abbrev Features.WellFormed (gf : Features) : Prop :=
  ContainmentPairLike.WellFormed gf

@[simp] theorem Features.neuter_wellFormed : Features.neuter.WellFormed := by decide
@[simp] theorem Features.feminine_wellFormed : Features.feminine.WellFormed := by decide
@[simp] theorem Features.masculine_wellFormed : Features.masculine.WellFormed := by decide

/-- The filtered combination [−feminine, +neuter] is the only one that
    violates containment. -/
theorem Features.not_wellFormed_mk_false_true : ¬ (⟨false, true⟩ : Features).WellFormed := by
  decide

/-- Exactly 3 well-formed feature combinations (= 3 genders) — the carrier
    count of the containment chain (`ContainmentPair.card_wellFormed`). -/
theorem Features.card_wellFormed :
    Fintype.card {gf : Features // gf.WellFormed} = 3 := by decide

/-- Containment: [+neuter] → [+feminine] for all well-formed features. -/
theorem Features.isFeminine_of_isNeuter :
    ∀ f : Features, f.WellFormed → f.isNeuter = true → f.isFeminine = true := by
  decide

/-- Map gender features to the comparative labels. -/
def Features.toGender : Features → Option Gender
  | ⟨true, true⟩   => some .neuter
  | ⟨true, false⟩  => some .feminine
  | ⟨false, false⟩ => some .masculine
  | ⟨false, true⟩  => none

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
