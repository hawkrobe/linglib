import Linglib.Syntax.Person.Category
import Linglib.Syntax.Agreement.ContainmentPair

/-!
# Bivalent person features

This file defines the decomposition of person into two bivalent features. The feature
[±participant] says whether the referent includes a speech-act participant and [±author]
whether it includes the speaker, so the three persons are three of the four combinations. The
fourth, an author who is no participant, is cut by the containment filter, which the features
inherit from `Agreement.ContainmentPair` through `featuresEquiv`. Both the person inventory and
the referential categories decompose, and both decompositions underdetermine clusivity.

## Main definitions

* `Person.Feature`: the two features, author depending on participant.
* `Person.Features`: a bundle, the positive features.
* `Person.toFeatures`: the bundle of a person value, none for the impersonal.
* `Person.featuresEquiv`: the bundles as containment pairs.
* `Features.WellFormed`: the containment filter.
* `Category.toFeatures`: the bundle of a referential category.

## Main results

* `Person.card_wellFormed`: exactly three well-formed bundles.
* `Person.no_fourth_person`: no four well-formed bundles are distinct.
* `Category.toFeatures_wellFormed`: every category decomposes well-formedly.

## References

* [H. Harley and E. Ritter, *Person and number in pronouns* (2002)][harley-ritter-2002]
* [D. Adger and D. Harbour, *Why phi?* (2008)][adger-harbour-2008]
* [P. Ackema and A. Neeleman, *Features of Person* (2018)][ackema-neeleman-2018]
* [D. Harbour, *Impossible Persons* (2016)][harbour-2016]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
-/

open Agreement (ContainmentPair ContainmentPairLike)

namespace Person

/-- The two person features, the author feature depending on the participant feature. -/
inductive Feature where
  /-- [participant]: the referent includes a speech-act participant. -/
  | participant
  /-- [author]: the referent includes the speaker. -/
  | author
  deriving DecidableEq, Repr, Fintype

/-- Position on the dependency chain, participant below author. -/
def Feature.rank : Feature → Fin 2
  | .participant => 0
  | .author => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

/-- A person feature bundle: the positive features. -/
abbrev Features := Finset Feature

/-- First person, [+participant, +author]. -/
def firstF : Features := {.participant, .author}

/-- Second person, [+participant, −author]. -/
def secondF : Features := {.participant}

/-- Third person, [−participant, −author]. -/
def thirdF : Features := ∅

/-- The bundle of a person value. The quadripartition cells share `firstF`, the two-feature
system underdetermining clusivity, and the impersonal `zero` has no decomposition. -/
def toFeatures : Person → Option Features
  | .first | .firstInclusive | .firstExclusive => some firstF
  | .second => some secondF
  | .third => some thirdF
  | .zero => none

/-! ### The containment presentation -/

/-- The person features as the two features of a containment pair, participant the outer and
author the inner. -/
def featureEquiv : Feature ≃ ContainmentPair.Feature where
  toFun
    | .participant => .outer
    | .author => .inner
  invFun
    | .outer => .participant
    | .inner => .author
  left_inv f := by cases f <;> rfl
  right_inv f := by cases f <;> rfl

/-- The bundles as containment pairs. -/
def featuresEquiv : Features ≃ ContainmentPair := featureEquiv.finsetCongr

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

/-- The three persons land on the three well-formed cells. -/
@[simp] theorem firstF_is_maximal : ContainmentPairLike.toPair firstF = .maximal := by decide
@[simp] theorem secondF_is_intermediate :
    ContainmentPairLike.toPair secondF = .intermediate := by decide
@[simp] theorem thirdF_is_minimal : ContainmentPairLike.toPair thirdF = .minimal := by decide

/-- The containment filter: an author is necessarily a participant. -/
abbrev Features.WellFormed (pf : Features) : Prop := ContainmentPairLike.WellFormed pf

@[simp] theorem firstF_wellFormed : firstF.WellFormed := by decide
@[simp] theorem secondF_wellFormed : secondF.WellFormed := by decide
@[simp] theorem thirdF_wellFormed : thirdF.WellFormed := by decide

/-- The bundle with the author feature alone is the one that violates containment. -/
theorem not_wellFormed_singleton_author : ¬ ({.author} : Features).WellFormed := by decide

/-- Exactly three well-formed bundles, the carrier count of the containment chain. -/
theorem card_wellFormed : Fintype.card {pf : Features // pf.WellFormed} = 3 := by decide

/-- Every defined decomposition is well-formed. -/
theorem toFeatures_wellFormed (p : Person) : ∀ f, p.toFeatures = some f → f.WellFormed := by
  cases p <;> intro f hf <;>
    simp only [toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> decide

/-- `IsSAP` is featural participanthood. -/
theorem isSAP_iff_participant (p : Person) :
    ∀ f, p.toFeatures = some f → (p.IsSAP ↔ .participant ∈ f) := by
  cases p <;> intro f hf <;>
    simp only [toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> decide

/-- No four-way singular person distinction, inherited from the containment pair. -/
theorem no_fourth_person :
    ∀ (a b c d : Features),
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd ↦ ContainmentPairLike.no_four_way a b c d ha hb hc hd

/-! ### The features of a referential category -/

namespace Category

variable {c : Category}

/-- The category bears the feature: [participant] when it contains a speech-act participant,
[author] when it contains the speaker. -/
def Bears (c : Category) : Feature → Prop
  | .participant => c.participants.Nonempty
  | .author => c.IncludesSpeaker

instance : DecidablePred c.Bears := fun f ↦ by cases f <;> unfold Bears <;> infer_instance

/-- The bundle of a category. The features underdetermine the first person complex, whose
three categories all map to `firstF`. The decomposition that distinguishes the exclusive lives
in `Studies.Harbour2016.signOf`. -/
def toFeatures (c : Category) : Features := Finset.univ.filter c.Bears

@[simp] theorem mem_toFeatures {f : Feature} : f ∈ c.toFeatures ↔ c.Bears f := by
  simp [toFeatures]

@[simp] theorem author_mem_toFeatures : .author ∈ c.toFeatures ↔ c.IncludesSpeaker := by
  simp [Bears]

@[simp] theorem participant_mem_toFeatures :
    .participant ∈ c.toFeatures ↔ c.IncludesSpeaker ∨ c.IncludesAddressee := by
  cases c <;> decide +kernel

/-- Every category yields a well-formed bundle. -/
theorem toFeatures_wellFormed (c : Category) : c.toFeatures.WellFormed := by
  cases c <;> decide +kernel

end Category

end Person
