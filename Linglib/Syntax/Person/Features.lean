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

* `Person.Features`: the two features.
* `Person.toFeatures`: the features of a person value, none for the impersonal.
* `Person.featuresEquiv`: the features as a containment pair.
* `Features.WellFormed`: the containment filter.
* `Category.toFeatures`: the features of a referential category.

## Main results

* `Person.card_wellFormed`: exactly three well-formed combinations.
* `Person.no_fourth_person`: no four well-formed combinations are distinct.
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

/-- Bivalent person features [±participant, ±author]. The three persons are the three
combinations the containment filter `Features.WellFormed` admits: first
[+participant, +author], second [+participant, −author], third [−participant, −author]. -/
structure Features where
  /-- [+participant]: the referent includes a speech-act participant. -/
  hasParticipant : Bool
  /-- [+author]: the referent includes the speaker. -/
  hasAuthor : Bool
  deriving DecidableEq, Repr, Fintype

/-- First person features, [+participant, +author]. -/
def firstF : Features := ⟨true, true⟩

/-- Second person features, [+participant, −author]. -/
def secondF : Features := ⟨true, false⟩

/-- Third person features, [−participant, −author]. -/
def thirdF : Features := ⟨false, false⟩

/-- The features of a person value. The quadripartition cells share `firstF`, the two-feature
system underdetermining clusivity, and the impersonal `zero` has no decomposition. -/
def toFeatures : Person → Option Features
  | .first | .firstInclusive | .firstExclusive => some firstF
  | .second => some secondF
  | .third => some thirdF
  | .zero => none

/-! ### The containment presentation -/

/-- The decomposition is carrier-equivalent to the containment pair, `outer` the participant
feature and `inner` the author feature. -/
def featuresEquiv : Features ≃ ContainmentPair where
  toFun f := ⟨f.hasParticipant, f.hasAuthor⟩
  invFun p := ⟨p.outer, p.inner⟩
  left_inv := fun ⟨_, _⟩ ↦ rfl
  right_inv := fun ⟨_, _⟩ ↦ rfl

instance : ContainmentPairLike Features := .ofEquiv featuresEquiv

/-- The three persons land on the three well-formed cells. -/
@[simp] theorem firstF_is_maximal : ContainmentPairLike.toPair firstF = .maximal := rfl
@[simp] theorem secondF_is_intermediate :
    ContainmentPairLike.toPair secondF = .intermediate := rfl
@[simp] theorem thirdF_is_minimal : ContainmentPairLike.toPair thirdF = .minimal := rfl

/-- The containment filter: an author is necessarily a participant. -/
abbrev Features.WellFormed (pf : Features) : Prop := ContainmentPairLike.WellFormed pf

@[simp] theorem firstF_wellFormed : firstF.WellFormed := by decide
@[simp] theorem secondF_wellFormed : secondF.WellFormed := by decide
@[simp] theorem thirdF_wellFormed : thirdF.WellFormed := by decide

/-- The combination [−participant, +author] is the only one that violates containment. -/
theorem not_wellFormed_mk_false_true : ¬ (⟨false, true⟩ : Features).WellFormed := by decide

/-- Exactly three well-formed combinations, the carrier count of the containment chain. -/
theorem card_wellFormed : Fintype.card {pf : Features // pf.WellFormed} = 3 := by decide

/-- Every defined decomposition is well-formed. -/
theorem toFeatures_wellFormed (p : Person) : ∀ f, p.toFeatures = some f → f.WellFormed := by
  cases p <;> intro f hf <;>
    simp only [toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> decide

/-- `IsSAP` is featural participanthood. -/
theorem isSAP_iff_participant (p : Person) :
    ∀ f, p.toFeatures = some f → (p.IsSAP ↔ f.hasParticipant = true) := by
  cases p <;> intro f hf <;>
    simp only [toFeatures, Option.some.injEq, reduceCtorEq] at hf <;>
    subst hf <;> simp [IsSAP, firstF, secondF, thirdF]

/-- No four-way singular person distinction, inherited from the containment pair. -/
theorem no_fourth_person :
    ∀ (a b c d : Features),
      a.WellFormed → b.WellFormed → c.WellFormed → d.WellFormed →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False :=
  fun a b c d ha hb hc hd ↦ ContainmentPairLike.no_four_way a b c d ha hb hc hd

/-! ### The features of a referential category -/

namespace Category

variable {c : Category}

/-- The features of a category: whether it contains a speech-act participant and whether it
contains the speaker. The features underdetermine the first person complex, whose three
categories all map to `firstF`. The decomposition that distinguishes the exclusive lives in
`Studies.Harbour2016.signOf`. -/
def toFeatures (c : Category) : Features :=
  ⟨decide c.participants.Nonempty, decide c.IncludesSpeaker⟩

@[simp] theorem toFeatures_hasAuthor : c.toFeatures.hasAuthor = true ↔ c.IncludesSpeaker := by
  simp [toFeatures]

@[simp] theorem toFeatures_hasParticipant :
    c.toFeatures.hasParticipant = true ↔ c.IncludesSpeaker ∨ c.IncludesAddressee := by
  cases c <;> decide +kernel

/-- Every category yields well-formed features. -/
theorem toFeatures_wellFormed (c : Category) : c.toFeatures.WellFormed := by
  cases c <;> decide +kernel

end Category

end Person
