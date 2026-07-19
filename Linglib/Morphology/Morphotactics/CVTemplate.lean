/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.Root
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# CV templates and template association

The skeletal species of template — [mccarthy-1981]'s *prosodic template*,
also called the CV-skeleton — as the sibling of the position-class
`AffixTemplate`: an ordered sequence of consonantal and vocalic timing
slots. A `TemplateMatch` pairs a consonantal root, a vocalism, and affixal
material with a template and a list of association lines; `spellout` reads
off the surface segments. Gemination is a one-to-many association from one
melody element to several slots ([mccarthy-1981]); a slot with no
association line receives no phonetic realization.

Association *conventions* — one-to-one left-to-right, spreading, erasure
rules — are derivational recipes and live with the studies that state them
(`Studies/McCarthy1981.lean`, `Studies/Faust2026.lean`); this file provides
the representations they manipulate.

## Main declarations

* `CVSlot`, `CVTemplate` — skeletal slots and templates.
* `Association` — a sourced melody-to-slot association line.
* `TemplateMatch` — a root, vocalism, and affix matched to a template.
* `TemplateMatch.spellout` — the surface segments of a match.
* `TemplateMatch.OrderedOn` — the tier-internal well-formedness condition.
* `TemplateMatch.links` — the per-tier link sets, in the coordinates of the
  autosegmental substrate.

## Main results

* `TemplateMatch.orderedOn_iff` — `OrderedOn` decomposes into the
  substrate's `Autosegmental.IsNonCrossing` plus [mccarthy-1981]'s
  prohibition against many-to-one associations (`SlotUnique`), so the
  list-level representation here interprets into
  `Phonology/Autosegmental/NonCrossing.lean` rather than duplicating it.
-/

namespace Morphology

/-- A slot in a CV-skeletal template ([mccarthy-1981], [lowenstamm-1996]):
a bare consonantal timing slot, a vowel timing slot, or a C-slot bearing
[+consonantal], which blocks association from glides ([faust-2026]). -/
inductive CVSlot where
  /-- A bare consonantal timing slot. -/
  | C
  /-- A vowel timing slot. -/
  | V
  /-- A C-slot specified [+consonantal]. -/
  | Cspec
  deriving DecidableEq, Repr

namespace CVSlot

/-- `IsC s` asserts that `s` is a C-slot, bare or [+consonantal]. -/
def IsC : CVSlot → Prop
  | .C | .Cspec => True
  | .V => False

instance : DecidablePred IsC := fun s => by cases s <;> unfold IsC <;> infer_instance

/-- `IsV s` asserts that `s` is a V-slot. -/
def IsV : CVSlot → Prop
  | .V => True
  | _ => False

instance : DecidablePred IsV := fun s => by cases s <;> unfold IsV <;> infer_instance

/-- `RequiresConsonantal s` asserts that `s` demands a [+consonantal]
segment. -/
def RequiresConsonantal : CVSlot → Prop
  | .Cspec => True
  | _ => False

instance : DecidablePred RequiresConsonantal := fun s => by
  cases s <;> unfold RequiresConsonantal <;> infer_instance

end CVSlot

/-- A CV-skeletal template: an ordered sequence of timing slots. -/
structure CVTemplate where
  /-- The slots, in order. -/
  slots : List CVSlot
  deriving Repr, DecidableEq

namespace CVTemplate

/-- The number of slots. -/
def length (t : CVTemplate) : Nat := t.slots.length

/-- The number of C-slots. -/
def cCount (t : CVTemplate) : Nat :=
  (t.slots.filter (fun s => decide (CVSlot.IsC s))).length

/-- `t.isFinalSlot i` asserts that `i` is the final slot position. -/
abbrev isFinalSlot (t : CVTemplate) (i : Nat) : Prop := i + 1 = t.length

/-- The slot at position `i`, if in range. -/
def slotAt (t : CVTemplate) (i : Nat) : Option CVSlot := t.slots[i]?

/-- The positions of the C-slots, in order. -/
def cSlots (t : CVTemplate) : List Nat :=
  (List.range t.length).filter fun i =>
    match t.slots[i]? with
    | some s => decide (CVSlot.IsC s)
    | none => false

/-- The positions of the V-slots, in order. -/
def vSlots (t : CVTemplate) : List Nat :=
  (List.range t.length).filter fun i =>
    match t.slots[i]? with
    | some s => decide (CVSlot.IsV s)
    | none => false

end CVTemplate

/-- The tier a melody element on one end of an association line belongs to:
the consonantal root, the vocalism, or affixal material. Tiers are
morphologically defined ([mccarthy-1981]) — one melody per morpheme class. -/
inductive AssocSource where
  /-- The consonantal root tier. -/
  | root
  /-- The vocalic melody tier. -/
  | vocalism
  /-- An affixal tier ([faust-2026]'s intruders are sister-exponent affixal
  material in this sense). -/
  | affix
  deriving DecidableEq, Repr

/-- A single melody-to-slot association line ([mccarthy-1981]).
`melodyIndex` indexes into the melody named by `source`; defaults to `.root`
so ordinary root associations stay terse. -/
structure Association where
  /-- The tier the associated melody element lives on. -/
  source : AssocSource := .root
  /-- The index of the melody element on its tier. -/
  melodyIndex : Nat
  /-- The index of the template slot. -/
  slotIndex : Nat
  deriving DecidableEq, Repr

/-- A consonantal root, a vocalism, and affixal material matched to a
template by a list of association lines. Different *candidate* realizations
of the same morpheme combination are different `TemplateMatch` values
sharing everything but `associations`; gemination is one melody index
associated to several slots. -/
structure TemplateMatch (α : Type*) where
  /-- The consonantal root. -/
  root : Root α
  /-- The vocalic melody. -/
  vocalism : List α := []
  /-- The affixal material. -/
  affix : List α := []
  /-- The template. -/
  template : CVTemplate
  /-- The association lines. -/
  associations : List Association
  deriving Repr, DecidableEq

namespace TemplateMatch

variable {α : Type*} (m : TemplateMatch α)

/-- The melody of a tier. -/
def melody : AssocSource → List α
  | .root => m.root.segments
  | .vocalism => m.vocalism
  | .affix => m.affix

/-- The segment an association line contributes, if its index is in range. -/
def segmentAt (a : Association) : Option α := (m.melody a.source)[a.melodyIndex]?

/-- The surface segments of the match: each slot contributes the segment of
its first association line; a slot with no association receives no phonetic
realization ([mccarthy-1981]). -/
def spellout : List α :=
  (List.range m.template.length).filterMap fun i =>
    (m.associations.find? (·.slotIndex == i)).bind m.segmentAt

/-- The C-slot positions not filled by any association. -/
def unfilledCSlots : List Nat :=
  m.template.cSlots.filter fun i => !m.associations.any (·.slotIndex == i)

/-- `m.allCSlotsFilled` asserts that every C-slot is filled by some
association line. -/
abbrev allCSlotsFilled : Prop := m.unfilledCSlots = []

/-- `m.inBounds` asserts that every association line points to an in-range
melody element and slot. -/
abbrev inBounds : Prop :=
  ∀ a ∈ m.associations,
    a.slotIndex < m.template.length ∧ a.melodyIndex < (m.melody a.source).length

/-- `m.OrderedOn s` asserts that the association lines from tier `s` do not
cross: distinct melody elements associate to slots in melody order
([goldsmith-1976]'s no-crossing condition, within one tier). -/
def OrderedOn (s : AssocSource) : Prop :=
  ∀ a ∈ m.associations, ∀ b ∈ m.associations,
    a.source = s → b.source = s →
    a.melodyIndex < b.melodyIndex → a.slotIndex < b.slotIndex

instance : Decidable (m.allCSlotsFilled) := inferInstanceAs (Decidable (_ = _))

instance : Decidable (m.inBounds) :=
  inferInstanceAs (Decidable (∀ a ∈ m.associations, _ ∧ _))

instance (s : AssocSource) : Decidable (m.OrderedOn s) :=
  inferInstanceAs (Decidable (∀ a ∈ m.associations, ∀ b ∈ m.associations, _))

/-- A match with no associations spells out to nothing. -/
theorem spellout_nil (r : Root α) (t : CVTemplate) :
    (TemplateMatch.mk r [] [] t []).spellout = [] := by
  simp [spellout]

/-! ### Interpretation into the autosegmental substrate -/

open Autosegmental

/-- The link set of tier `s`, in the two-layer coordinates of
`Phonology/Autosegmental/NonCrossing.lean`: one `(melodyIndex, slotIndex)`
pair per association line from `s`. -/
def links (s : AssocSource) : Finset (Nat × Nat) :=
  ((m.associations.filter (·.source == s)).map fun a =>
    (a.melodyIndex, a.slotIndex)).toFinset

/-- `m.SlotUnique s` asserts that no slot hosts two distinct melody elements
of tier `s` — [mccarthy-1981]'s prohibition against many-to-one
associations. -/
def SlotUnique (s : AssocSource) : Prop :=
  ∀ a ∈ m.associations, ∀ b ∈ m.associations, a.source = s → b.source = s →
    a.slotIndex = b.slotIndex → a.melodyIndex = b.melodyIndex

instance (s : AssocSource) : Decidable (m.SlotUnique s) :=
  inferInstanceAs (Decidable (∀ a ∈ m.associations, ∀ b ∈ m.associations, _))

theorem mem_links (p : Nat × Nat) (s : AssocSource) :
    p ∈ m.links s ↔
      ∃ a ∈ m.associations, a.source = s ∧ a.melodyIndex = p.1 ∧ a.slotIndex = p.2 := by
  simp only [links, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨a, ⟨ha, hs⟩, rfl⟩
    exact ⟨a, ha, hs, rfl, rfl⟩
  · rintro ⟨a, ha, hs, h1, h2⟩
    exact ⟨a, ⟨ha, hs⟩, by cases p; simp_all⟩

/-- A tier is `OrderedOn` iff its link set is non-crossing in the sense of
the autosegmental substrate *and* one-to-one per slot: [goldsmith-1976]'s
No-Crossing Constraint plus [mccarthy-1981]'s prohibition against
many-to-one associations. -/
theorem orderedOn_iff (s : AssocSource) :
    m.OrderedOn s ↔ IsNonCrossing (m.links s) ∧ m.SlotUnique s := by
  constructor
  · refine fun h => ⟨isNonCrossing_iff.mpr ?_, fun a ha b hb has hbs hslot => ?_⟩
    · rintro p hp q hq hlt
      obtain ⟨a, ha, has, h1, h2⟩ := (m.mem_links p s).mp hp
      obtain ⟨b, hb, hbs, h3, h4⟩ := (m.mem_links q s).mp hq
      have := h a ha b hb has hbs (by omega)
      omega
    · by_contra hne
      rcases Nat.lt_or_ge a.melodyIndex b.melodyIndex with hlt | hge
      · exact absurd (h a ha b hb has hbs hlt) (by omega)
      · rcases Nat.lt_or_ge b.melodyIndex a.melodyIndex with hlt' | _
        · exact absurd (h b hb a ha hbs has hlt') (by omega)
        · omega
  · rintro ⟨hnc, hu⟩ a ha b hb has hbs hlt
    have hle := isNonCrossing_iff.mp hnc
      _ ((m.mem_links (a.melodyIndex, a.slotIndex) s).mpr ⟨a, ha, has, rfl, rfl⟩)
      _ ((m.mem_links (b.melodyIndex, b.slotIndex) s).mpr ⟨b, hb, hbs, rfl, rfl⟩) hlt
    rcases Nat.lt_or_eq_of_le hle with hlt' | heq
    · exact hlt'
    · exact absurd (hu a ha b hb has hbs heq) (by omega)

end TemplateMatch

end Morphology
