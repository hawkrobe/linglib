import Linglib.Core.Data.Setoid.Basic
import Linglib.Features.Person.Decomposition

/-!
# Clusivity systems: marking types of the first person complex

A person paradigm marks the three 'we' categories 1+2, 1+2+3 and 1+3 either by a morpheme
of their own or by one that also marks a singular category, and groups them in some way.
[cysouw-2003]'s Fig. 3.1 writes such a pattern with a letter per specialized morpheme class
and a dash where a singular morpheme is reused; of the fifteen possible patterns five are
common (his Table 3.2) and form `System`. Each type's `pattern` is that notation as a setoid
on `Cell`, the four speaker-including categories, the singular speaker standing for any
singular morpheme, and the four questions of his Fig. 3.10 are read off the setoid. The
First Person Hierarchy (3.26) is the linear order on the types, along which each question's
answer is monotone.

The five rare attested patterns ((Pf)–(Pj), his §3.6.6) are not systems in this sense and
live with the study. The typology is finer than [cysouw-2013]'s WALS chapter, which
collapses minimal/augmented into inclusive/exclusive and whose "no 'we'" value is the absence
of any first-person non-singular, not `System.noWe`.

## References

* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
* [M. Cysouw, *Inclusive/Exclusive Distinction in Independent Pronouns* (2013)][cysouw-2013]
-/

namespace Person.Clusivity

/-- Fig. 3.1's four cells, the categories that include the speaker; the singular speaker
stands for every singular morpheme. -/
abbrev Cell := {c : Category // c.IncludesSpeaker}

namespace Cell

/-- The singular speaker. -/
def s1 : Cell := ⟨.s1, by decide⟩

/-- The minimal inclusive 1+2. -/
def minIncl : Cell := ⟨.minIncl, by decide⟩

/-- The augmented inclusive 1+2+3. -/
def augIncl : Cell := ⟨.augIncl, by decide⟩

/-- The exclusive 1+3. -/
def excl : Cell := ⟨.excl, by decide⟩

end Cell

section Questions

variable (r : Setoid Cell)

/-- Some 'we' cell is not marked like the speaker (Fig. 3.10's first question). -/
def SpecializedWe : Prop := ∃ c : Cell, c.1.IsFirstPersonComplex ∧ ¬ r c Cell.s1

/-- Both inclusive cells are marked neither like the speaker nor like the exclusive
(Fig. 3.10's second question, read as his Fig. 3.8 reads it for the common types). -/
def SpecializedInclusive : Prop :=
  ∀ c : Cell, c.1.IsInclusive → ¬ r c Cell.s1 ∧ ¬ r c Cell.excl

/-- The exclusive is marked neither like the speaker nor like an inclusive cell (Fig. 3.10's
third question). -/
def SpecializedExclusive : Prop :=
  ¬ r Cell.excl Cell.s1 ∧ ∀ c : Cell, c.1.IsInclusive → ¬ r Cell.excl c

/-- Minimal and augmented inclusive are marked apart and neither like the speaker (Fig. 3.10's
fourth question). -/
def SplitInclusive : Prop :=
  ¬ r Cell.minIncl Cell.augIncl ∧ ¬ r Cell.minIncl Cell.s1 ∧ ¬ r Cell.augIncl Cell.s1

variable [DecidableRel (⇑r)]

instance : Decidable (SpecializedWe r) := by unfold SpecializedWe; infer_instance
instance : Decidable (SpecializedInclusive r) := by
  unfold SpecializedInclusive; infer_instance
instance : Decidable (SpecializedExclusive r) := by
  unfold SpecializedExclusive; infer_instance
instance : Decidable (SplitInclusive r) := by unfold SplitInclusive; infer_instance

end Questions

/-- The five common marking types of the first person complex ([cysouw-2003] Table 3.2, the
common five of the fifteen patterns of his Fig. 3.1). -/
inductive System where
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

namespace System

/-- Fig. 3.2's letters as morpheme classes, `0` being the class of the singular speaker,
Fig. 3.1's dash, in which every category outside the first person complex is placed. -/
def labels : System → Category → ℕ
  | .unifiedWe, .minIncl | .unifiedWe, .augIncl | .unifiedWe, .excl => 1
  | .onlyInclusive, .minIncl | .onlyInclusive, .augIncl => 1
  | .inclusiveExclusive, .minIncl | .inclusiveExclusive, .augIncl => 1
  | .inclusiveExclusive, .excl => 2
  | .minimalAugmented, .minIncl => 1
  | .minimalAugmented, .augIncl => 2
  | .minimalAugmented, .excl => 3
  | _, _ => 0

/-- The type's pattern, Fig. 3.2's column as a setoid on the four cells. -/
abbrev pattern (t : System) : Setoid Cell := Setoid.ker (t.labels ∘ Subtype.val)

/-- Some specialized 'we' morpheme exists. -/
abbrev SpecializedWe (t : System) : Prop := Clusivity.SpecializedWe t.pattern

/-- The inclusive has a specialized morpheme of its own. -/
abbrev SpecializedInclusive (t : System) : Prop := Clusivity.SpecializedInclusive t.pattern

/-- The exclusive has a specialized morpheme of its own. -/
abbrev SpecializedExclusive (t : System) : Prop := Clusivity.SpecializedExclusive t.pattern

/-- Minimal and augmented inclusive are marked apart. -/
abbrev SplitInclusive (t : System) : Prop := Clusivity.SplitInclusive t.pattern

/-- The five patterns are distinct. -/
theorem pattern_injective : Function.Injective pattern := by
  show ∀ s t : System, _ → _; decide +kernel

/-- A specialized exclusive requires a specialized inclusive ((3.23), Fig. 3.8). -/
theorem specializedInclusive_of_specializedExclusive {t : System}
    (h : t.SpecializedExclusive) : t.SpecializedInclusive := by
  revert t h; show ∀ t : System, _; decide +kernel

/-- The converse of (3.23) fails at only-inclusive. -/
theorem onlyInclusive_specializedInclusive : onlyInclusive.SpecializedInclusive := by
  decide +kernel

theorem onlyInclusive_not_specializedExclusive : ¬ onlyInclusive.SpecializedExclusive := by
  decide +kernel

/-- A split inclusive requires a specialized exclusive ((3.24), Fig. 3.9). -/
theorem specializedExclusive_of_splitInclusive {t : System} (h : t.SplitInclusive) :
    t.SpecializedExclusive := by
  revert t h; show ∀ t : System, _; decide +kernel

/-- Position on the First Person Hierarchy (3.26), the number of Fig. 3.10's questions
answered positively: no-we, unified-we, only-inclusive, inclusive/exclusive,
minimal/augmented. -/
def hierarchyRank : System → ℕ
  | .noWe => 0
  | .unifiedWe => 1
  | .onlyInclusive => 2
  | .inclusiveExclusive => 3
  | .minimalAugmented => 4

/-- The First Person Hierarchy (3.26) as the order on the types. -/
instance : LinearOrder System := LinearOrder.lift' hierarchyRank (by decide)

/-- Each of Fig. 3.10's answers is monotone along the hierarchy, so each type's profile
extends its predecessor's by one positive answer. -/
theorem specializedWe_of_le {s t : System} (h : s ≤ t) (hs : s.SpecializedWe) :
    t.SpecializedWe := by
  revert s t h hs; show ∀ s t : System, _; decide +kernel

theorem specializedInclusive_of_le {s t : System} (h : s ≤ t) (hs : s.SpecializedInclusive) :
    t.SpecializedInclusive := by
  revert s t h hs; show ∀ s t : System, _; decide +kernel

theorem specializedExclusive_of_le {s t : System} (h : s ≤ t) (hs : s.SpecializedExclusive) :
    t.SpecializedExclusive := by
  revert s t h hs; show ∀ s t : System, _; decide +kernel

theorem splitInclusive_of_le {s t : System} (h : s ≤ t) (hs : s.SplitInclusive) :
    t.SplitInclusive := by
  revert s t h hs; show ∀ s t : System, _; decide +kernel

end System

end Person.Clusivity
