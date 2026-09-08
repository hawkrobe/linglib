import Linglib.Features.Person.Decomposition

/-!
# Clusivity systems: marking types of the first person complex

A person paradigm marks the three 'we' categories 1+2, 1+2+3 and 1+3 either by a morpheme
of their own or by one that also marks a singular category, and groups them in some way.
[cysouw-2003]'s Fig. 3.1 writes such a pattern with a letter per specialized morpheme class
and a dash where a singular morpheme is reused; of the fifteen possible patterns five are
common (his Table 3.2) and form `System`. Each type's `pattern` is that notation as a
labelling of the four speaker-including categories, the singular speaker standing for any
singular morpheme, and the four questions of his Fig. 3.10 are read off the labelling. The
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

section Pattern

variable {α β : Type*} (f : Category → α)

/-- Some 'we' category has a morpheme of its own (Fig. 3.10's first question). -/
def SpecializedWe : Prop := ∃ c : Category, c.IsFirstPersonComplex ∧ f c ≠ f .s1

/-- Both inclusive categories have a morpheme of their own, shared neither with a singular
nor with the exclusive (Fig. 3.10's second question, read as his Fig. 3.8 reads it for the
common types). -/
def SpecializedInclusive : Prop :=
  ∀ c : Category, c.IsInclusive → f c ≠ f .s1 ∧ f c ≠ f .excl

/-- The exclusive has a morpheme of its own (Fig. 3.10's third question). -/
def SpecializedExclusive : Prop :=
  f .excl ≠ f .s1 ∧ ∀ c : Category, c.IsInclusive → f .excl ≠ f c

/-- Minimal and augmented inclusive each have a morpheme of their own, marked apart
(Fig. 3.10's fourth question). -/
def SplitInclusive : Prop := f .minIncl ≠ f .augIncl ∧ f .minIncl ≠ f .s1 ∧ f .augIncl ≠ f .s1

/-- Two labellings group the speaker-including categories, Fig. 3.1's four cells, alike. -/
def SamePattern (g : Category → β) : Prop :=
  ∀ a b : Category, a.IncludesSpeaker → b.IncludesSpeaker → (f a = f b ↔ g a = g b)

section Decidable

variable [DecidableEq α] [DecidableEq β]

instance : Decidable (SpecializedWe f) := by unfold SpecializedWe; infer_instance
instance : Decidable (SpecializedInclusive f) := by
  unfold SpecializedInclusive; infer_instance
instance : Decidable (SpecializedExclusive f) := by
  unfold SpecializedExclusive; infer_instance
instance : Decidable (SplitInclusive f) := by unfold SplitInclusive; infer_instance
instance (g : Category → β) : Decidable (SamePattern f g) := by
  unfold SamePattern; infer_instance

end Decidable

variable {f} {g : Category → β}

theorem SamePattern.specializedWe_iff (h : SamePattern f g) :
    SpecializedWe f ↔ SpecializedWe g :=
  exists_congr λ c => and_congr_right λ hc =>
    not_congr (h c _ hc.includesSpeaker (by decide))

theorem SamePattern.specializedInclusive_iff (h : SamePattern f g) :
    SpecializedInclusive f ↔ SpecializedInclusive g :=
  forall_congr' λ c => imp_congr_right λ hc =>
    and_congr (not_congr (h c _ hc.includesSpeaker (by decide)))
      (not_congr (h c _ hc.includesSpeaker (by decide)))

theorem SamePattern.specializedExclusive_iff (h : SamePattern f g) :
    SpecializedExclusive f ↔ SpecializedExclusive g :=
  and_congr (not_congr (h _ _ (by decide) (by decide)))
    (forall_congr' λ c => imp_congr_right λ hc =>
      not_congr (h _ c (by decide) hc.includesSpeaker))

theorem SamePattern.splitInclusive_iff (h : SamePattern f g) :
    SplitInclusive f ↔ SplitInclusive g :=
  and_congr (not_congr (h _ _ (by decide) (by decide)))
    (and_congr (not_congr (h _ _ (by decide) (by decide)))
      (not_congr (h _ _ (by decide) (by decide))))

end Pattern

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
def pattern : System → Category → ℕ
  | .unifiedWe, .minIncl | .unifiedWe, .augIncl | .unifiedWe, .excl => 1
  | .onlyInclusive, .minIncl | .onlyInclusive, .augIncl => 1
  | .inclusiveExclusive, .minIncl | .inclusiveExclusive, .augIncl => 1
  | .inclusiveExclusive, .excl => 2
  | .minimalAugmented, .minIncl => 1
  | .minimalAugmented, .augIncl => 2
  | .minimalAugmented, .excl => 3
  | _, _ => 0

/-- Some specialized 'we' morpheme exists. -/
abbrev SpecializedWe (t : System) : Prop := Clusivity.SpecializedWe t.pattern

/-- The inclusive has a specialized morpheme of its own. -/
abbrev SpecializedInclusive (t : System) : Prop := Clusivity.SpecializedInclusive t.pattern

/-- The exclusive has a specialized morpheme of its own. -/
abbrev SpecializedExclusive (t : System) : Prop := Clusivity.SpecializedExclusive t.pattern

/-- Minimal and augmented inclusive are marked apart. -/
abbrev SplitInclusive (t : System) : Prop := Clusivity.SplitInclusive t.pattern

/-- The five patterns are distinct. -/
theorem eq_of_samePattern {s t : System} (h : SamePattern s.pattern t.pattern) : s = t := by
  revert s t h; decide

/-- A specialized exclusive requires a specialized inclusive ((3.23), Fig. 3.8). -/
theorem specializedInclusive_of_specializedExclusive {t : System}
    (h : t.SpecializedExclusive) : t.SpecializedInclusive := by
  revert t h; decide

/-- The converse of (3.23) fails at only-inclusive. -/
theorem onlyInclusive_specializedInclusive : onlyInclusive.SpecializedInclusive := by decide

theorem onlyInclusive_not_specializedExclusive : ¬ onlyInclusive.SpecializedExclusive := by
  decide

/-- A split inclusive requires a specialized exclusive ((3.24), Fig. 3.9). -/
theorem specializedExclusive_of_splitInclusive {t : System} (h : t.SplitInclusive) :
    t.SpecializedExclusive := by
  revert t h; decide

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
  revert s t h hs; decide

theorem specializedInclusive_of_le {s t : System} (h : s ≤ t) (hs : s.SpecializedInclusive) :
    t.SpecializedInclusive := by
  revert s t h hs; decide

theorem specializedExclusive_of_le {s t : System} (h : s ≤ t) (hs : s.SpecializedExclusive) :
    t.SpecializedExclusive := by
  revert s t h hs; decide

theorem splitInclusive_of_le {s t : System} (h : s ≤ t) (hs : s.SplitInclusive) :
    t.SplitInclusive := by
  revert s t h hs; decide

end System

end Person.Clusivity
