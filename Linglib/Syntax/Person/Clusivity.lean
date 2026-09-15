import Linglib.Core.Data.Setoid.Basic
import Linglib.Syntax.Person.Decomposition

/-!
# Clusivity: marking types of the first person complex

A person paradigm marks the three 'we' categories 1+2, 1+2+3 and 1+3 either by a morpheme
of their own or by one that also marks a singular category, and groups them in some way.
[cysouw-2003]'s Fig. 3.1 writes such a pattern with a letter per specialized morpheme class
and a dash where a singular morpheme is reused; of the fifteen possible patterns five are
common (his Table 3.2) and form `Clusivity`. Each type's `toPattern` is that notation as a
setoid on `Clusivity.Cell`, the four speaker-including categories, the singular speaker
standing for any singular morpheme, and the four questions of his Fig. 3.10 are read off the
setoid. The First Person Hierarchy (3.26) is the linear order on the types, along which each
question's answer is monotone.

The five rare attested patterns ((Pf)–(Pj), his §3.6.6) are not types in this sense and live
with the study. The typology is finer than [cysouw-2013]'s WALS chapter, which collapses
minimal/augmented into inclusive/exclusive and whose "no 'we'" value is the absence of any
first-person non-singular, not `Clusivity.noWe`.

## References

* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
* [M. Cysouw, *Inclusive/Exclusive Distinction in Independent Pronouns* (2013)][cysouw-2013]
-/

namespace Person

/-- The five common marking types of the first person complex ([cysouw-2003] Table 3.2, the
common five of the fifteen patterns of his Fig. 3.1). -/
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
  *ta* ~ *tayo* ~ *mi* (Pe, his Fig. 3.6). -/
  | minimalAugmented
  deriving DecidableEq, Repr, Fintype

namespace Clusivity

/-- Fig. 3.1's four cells, the categories that include the speaker; the singular speaker
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

/-- A marking pattern of the first person complex, Fig. 3.1's notation as a setoid on the
four cells. -/
abbrev Pattern := Setoid Cell

namespace Pattern

variable (r : Pattern)

/-- Some 'we' cell is not marked like the speaker (Fig. 3.10's first question). -/
def SpecializedWe : Prop := ∃ c : Cell, c.1.IsFirstPersonComplex ∧ ¬ r c Cell.speaker

/-- Both inclusive cells are marked neither like the speaker nor like the exclusive
(Fig. 3.10's second question, read as his Fig. 3.8 reads it for the common types). -/
def SpecializedInclusive : Prop :=
  ∀ c : Cell, c.1.IsInclusive → ¬ r c Cell.speaker ∧ ¬ r c Cell.speakerOthers

/-- The exclusive is marked neither like the speaker nor like an inclusive cell (Fig. 3.10's
third question). -/
def SpecializedExclusive : Prop :=
  ¬ r Cell.speakerOthers Cell.speaker ∧ ∀ c : Cell, c.1.IsInclusive → ¬ r Cell.speakerOthers c

/-- Minimal and augmented inclusive are marked apart and neither like the speaker (Fig. 3.10's
fourth question). -/
def SplitInclusive : Prop :=
  ¬ r Cell.speakerAddressee Cell.speakerAddresseeOthers ∧
    ¬ r Cell.speakerAddressee Cell.speaker ∧ ¬ r Cell.speakerAddresseeOthers Cell.speaker

variable [DecidableRel (⇑r)]

instance : Decidable r.SpecializedWe := by unfold SpecializedWe; infer_instance
instance : Decidable r.SpecializedInclusive := by unfold SpecializedInclusive; infer_instance
instance : Decidable r.SpecializedExclusive := by unfold SpecializedExclusive; infer_instance
instance : Decidable r.SplitInclusive := by unfold SplitInclusive; infer_instance

end Pattern

/-- Fig. 3.2's letters as morpheme classes, `0` being the class of the singular speaker,
Fig. 3.1's dash, in which every category outside the first person complex is placed. -/
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

/-- The type's pattern, Fig. 3.2's column as a setoid on the four cells. -/
abbrev toPattern (t : Clusivity) : Pattern := Setoid.ker (t.labels ∘ Subtype.val)

/-- The five patterns are distinct. -/
theorem toPattern_injective : Function.Injective toPattern := by
  show ∀ s t : Clusivity, _ → _; decide +kernel

/-- A specialized exclusive requires a specialized inclusive ((3.23), Fig. 3.8). -/
theorem specializedInclusive_of_specializedExclusive {t : Clusivity}
    (h : t.toPattern.SpecializedExclusive) : t.toPattern.SpecializedInclusive := by
  revert t h; show ∀ t : Clusivity, _; decide +kernel

/-- The converse of (3.23) fails at only-inclusive. -/
theorem onlyInclusive_specializedInclusive : onlyInclusive.toPattern.SpecializedInclusive := by
  decide +kernel

theorem onlyInclusive_not_specializedExclusive :
    ¬ onlyInclusive.toPattern.SpecializedExclusive := by
  decide +kernel

/-- A split inclusive requires a specialized exclusive ((3.24), Fig. 3.9). -/
theorem specializedExclusive_of_splitInclusive {t : Clusivity}
    (h : t.toPattern.SplitInclusive) : t.toPattern.SpecializedExclusive := by
  revert t h; show ∀ t : Clusivity, _; decide +kernel

/-- Position on the First Person Hierarchy (3.26), the number of Fig. 3.10's questions
answered positively: no-we, unified-we, only-inclusive, inclusive/exclusive,
minimal/augmented. -/
def hierarchyRank : Clusivity → ℕ
  | .noWe => 0
  | .unifiedWe => 1
  | .onlyInclusive => 2
  | .inclusiveExclusive => 3
  | .minimalAugmented => 4

/-- The First Person Hierarchy (3.26) as the order on the types. -/
instance : LinearOrder Clusivity := LinearOrder.lift' hierarchyRank (by decide)

/-- Each of Fig. 3.10's answers is monotone along the hierarchy, so each type's profile
extends its predecessor's by one positive answer. -/
theorem specializedWe_of_le {s t : Clusivity} (h : s ≤ t) (hs : s.toPattern.SpecializedWe) :
    t.toPattern.SpecializedWe := by
  revert s t h hs; show ∀ s t : Clusivity, _; decide +kernel

theorem specializedInclusive_of_le {s t : Clusivity} (h : s ≤ t)
    (hs : s.toPattern.SpecializedInclusive) : t.toPattern.SpecializedInclusive := by
  revert s t h hs; show ∀ s t : Clusivity, _; decide +kernel

theorem specializedExclusive_of_le {s t : Clusivity} (h : s ≤ t)
    (hs : s.toPattern.SpecializedExclusive) : t.toPattern.SpecializedExclusive := by
  revert s t h hs; show ∀ s t : Clusivity, _; decide +kernel

theorem splitInclusive_of_le {s t : Clusivity} (h : s ≤ t) (hs : s.toPattern.SplitInclusive) :
    t.toPattern.SplitInclusive := by
  revert s t h hs; show ∀ s t : Clusivity, _; decide +kernel

end Clusivity

end Person
