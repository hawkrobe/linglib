import Linglib.Core.Data.Setoid.Basic
import Linglib.Core.Order.UpperLower.Finset
import Linglib.Syntax.Person.Decomposition

/-!
# Clusivity: marking types of the first person complex

A person paradigm marks the three 'we' categories 1+2, 1+2+3 and 1+3 either by a morpheme of
their own or by one that also marks a singular category, and groups them in some way.
[cysouw-2003] writes such a pattern with a letter per specialized morpheme class and a dash
where a singular morpheme is reused, and of the fifteen possible patterns finds five common.
These form `Clusivity`, each given by `toPattern` as a setoid on the four speaker-including
categories, the singular speaker standing for any singular morpheme.

The types are told apart by four questions asked in order: whether 'we', the inclusive and the
exclusive are specialized, and whether the inclusive is split. A pattern's `profile` is the
questions it answers positively. The common types are exactly the lower sets of the questions,
each positive answer presupposing the ones before it, which is how the two addressee inclusion
implications read as conditions, and the First Person Hierarchy is the order of the profiles.

The five rare attested patterns are not types in this sense and live with the study. The
typology is finer than [cysouw-2013]'s WALS chapter, which collapses minimal/augmented into
inclusive/exclusive and whose "no 'we'" value is the absence of any first-person non-singular,
not `noWe`.

## References

* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
* [M. Cysouw, *Inclusive/Exclusive Distinction in Independent Pronouns* (2013)][cysouw-2013]
-/

namespace Person

/-- The five common marking types of the first person complex, the common five of the fifteen
patterns of [cysouw-2003]'s Fig. 3.1. -/
inductive Clusivity where
  /-- No 'we' category has a specialized morpheme, as in the English inflection (Pb). -/
  | noWe
  /-- All three 'we' categories share one specialized morpheme, as English *we* (Pa). -/
  | unifiedWe
  /-- 1+2 and 1+2+3 share a specialized morpheme and 1+3 has none, as in Maká (Pc). -/
  | onlyInclusive
  /-- 1+2 and 1+2+3 share one specialized morpheme and 1+3 has another, as in Apalai (Pd). -/
  | inclusiveExclusive
  /-- All three 'we' categories have separate specialized morphemes, as Ilocano
  *ta* ~ *tayo* ~ *mi* (Pe). -/
  | minimalAugmented
  deriving DecidableEq, Repr, Fintype

namespace Clusivity

/-- The four cells of a pattern, the categories that include the speaker; the singular speaker
stands for every singular morpheme. -/
abbrev Cell := {c : Category // c.IncludesSpeaker}

namespace Cell

/-- The singular speaker. -/
def speaker : Cell := ⟨.speaker, by decide⟩

/-- The minimal inclusive 1+2. -/
def speakerAddressee : Cell := ⟨.speakerAddressee, by decide⟩

/-- The augmented inclusive 1+2+3. -/
def speakerAddresseeOthers : Cell := ⟨.speakerAddresseeOthers, by decide⟩

/-- The exclusive 1+3. -/
def speakerOthers : Cell := ⟨.speakerOthers, by decide⟩

end Cell

/-- A marking pattern of the first person complex, the letter notation as a setoid on the
four cells. -/
abbrev Pattern := Setoid Cell

/-- The four questions that classify the patterns, in the order the hierarchy asks them. -/
inductive Question where
  /-- Is there any specialized form for 'we'? -/
  | specializedWe
  /-- Is the inclusive specialized? -/
  | specializedInclusive
  /-- Is the exclusive specialized? -/
  | specializedExclusive
  /-- Is the inclusive split? -/
  | splitInclusive
  deriving DecidableEq, Repr, Fintype

namespace Question

/-- Position in the order of asking. -/
def rank : Question → Fin 4
  | .specializedWe => 0
  | .specializedInclusive => 1
  | .specializedExclusive => 2
  | .splitInclusive => 3

instance : LinearOrder Question := LinearOrder.lift' rank (by decide)

end Question

namespace Pattern

variable (r : Pattern)

/-- Some 'we' cell is not marked like the speaker. -/
def SpecializedWe : Prop := ∃ c : Cell, c.1.IsFirstPersonComplex ∧ ¬ r c Cell.speaker

/-- Both inclusive cells are marked neither like the speaker nor like the exclusive. -/
def SpecializedInclusive : Prop :=
  ∀ c : Cell, c.1.IsInclusive → ¬ r c Cell.speaker ∧ ¬ r c Cell.speakerOthers

/-- The exclusive is marked neither like the speaker nor like an inclusive cell. -/
def SpecializedExclusive : Prop :=
  ¬ r Cell.speakerOthers Cell.speaker ∧ ∀ c : Cell, c.1.IsInclusive → ¬ r Cell.speakerOthers c

/-- Minimal and augmented inclusive are marked apart and neither like the speaker. -/
def SplitInclusive : Prop :=
  ¬ r Cell.speakerAddressee Cell.speakerAddresseeOthers ∧
    ¬ r Cell.speakerAddressee Cell.speaker ∧ ¬ r Cell.speakerAddresseeOthers Cell.speaker

/-- The pattern answers the question positively. -/
def Answers : Question → Prop
  | .specializedWe => r.SpecializedWe
  | .specializedInclusive => r.SpecializedInclusive
  | .specializedExclusive => r.SpecializedExclusive
  | .splitInclusive => r.SplitInclusive

variable [DecidableRel (⇑r)]

instance : Decidable r.SpecializedWe := by unfold SpecializedWe; infer_instance
instance : Decidable r.SpecializedInclusive := by unfold SpecializedInclusive; infer_instance
instance : Decidable r.SpecializedExclusive := by unfold SpecializedExclusive; infer_instance
instance : Decidable r.SplitInclusive := by unfold SplitInclusive; infer_instance
instance : DecidablePred r.Answers := fun q ↦ by cases q <;> unfold Answers <;> infer_instance

/-- The questions the pattern answers positively. -/
def profile : Finset Question := Finset.univ.filter r.Answers

/-- The pattern fits the hierarchy: read as conditions, each positive answer requires the
ones before it, so the profile is an initial segment of the questions. -/
def RespectsHierarchy : Prop := IsLowerSet (↑r.profile : Set Question)

instance : Decidable r.RespectsHierarchy := inferInstanceAs (Decidable (IsLowerSet _))

end Pattern

/-- The letters as morpheme classes, `0` being the class of the singular speaker, the dash,
in which every category outside the first person complex is placed. -/
def labels : Clusivity → Category → ℕ
  | .unifiedWe, .speakerAddressee | .unifiedWe, .speakerAddresseeOthers
  | .unifiedWe, .speakerOthers => 1
  | .onlyInclusive, .speakerAddressee | .onlyInclusive, .speakerAddresseeOthers => 1
  | .inclusiveExclusive, .speakerAddressee | .inclusiveExclusive, .speakerAddresseeOthers => 1
  | .inclusiveExclusive, .speakerOthers => 2
  | .minimalAugmented, .speakerAddressee => 1
  | .minimalAugmented, .speakerAddresseeOthers => 2
  | .minimalAugmented, .speakerOthers => 3
  | _, _ => 0

/-- The type's pattern, its column of letters as a setoid on the four cells. -/
abbrev toPattern (t : Clusivity) : Pattern := Setoid.ker (t.labels ∘ Subtype.val)

/-- The five patterns are distinct. -/
theorem toPattern_injective : Function.Injective toPattern := by
  show ∀ s t : Clusivity, _ → _; decide +kernel

/-- The questions a type answers positively. -/
abbrev profile (t : Clusivity) : Finset Question := t.toPattern.profile

/-- Every common type fits the hierarchy: a specialized exclusive requires a specialized
inclusive and a split inclusive a specialized exclusive, the two addressee inclusion
implications. -/
theorem profile_isLowerSet (t : Clusivity) : IsLowerSet (↑t.profile : Set Question) := by
  revert t; decide +kernel

/-- The rung of a type: its profile, a lower set of the questions. -/
def rung (t : Clusivity) : {S : Finset Question // IsLowerSet (↑S : Set Question)} :=
  ⟨t.profile, t.profile_isLowerSet⟩

/-- The common types are exactly the rungs of the hierarchy, one for each lower set of the
questions. -/
theorem rung_bijective : Function.Bijective rung := by decide +kernel

/-- The First Person Hierarchy: a type precedes another when it answers fewer of the questions,
no-we, unified-we, only-inclusive, inclusive/exclusive, minimal/augmented. -/
instance : LinearOrder Clusivity := LinearOrder.lift' (fun t ↦ t.profile.card) (by decide +kernel)

/-- Along the hierarchy each type's profile extends its predecessor's. -/
theorem le_iff_profile_subset {s t : Clusivity} : s ≤ t ↔ s.profile ⊆ t.profile := by
  revert s t; decide +kernel

theorem profile_monotone : Monotone profile := fun _ _ ↦ le_iff_profile_subset.1

/-- The converse of the first addressee inclusion implication fails at only-inclusive. -/
theorem onlyInclusive_profile :
    onlyInclusive.profile = {.specializedWe, .specializedInclusive} := by decide +kernel

end Clusivity

end Person
