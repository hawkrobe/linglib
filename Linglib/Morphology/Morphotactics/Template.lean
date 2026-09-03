import Mathlib.Data.List.Chain
import Mathlib.Tactic.TypeStar

/-!
# Templates: word-skeletal morphotactic substrate

A **template** stipulates a word's positional skeleton directly — the
word-skeletal answer to where affix order comes from, rival to the
rule-combining answer on which templates are emergent patterns of rule
composition ([stump-2022]). The layered-vs-templatic *typological*
contrast and its diagnostics (long-distance slot dependencies,
non-functional slot assignment) are [bickel-nichols-2007] §6, with the
caveat that templatic vs layered properties "are likely to hold of
individual formatives rather than of the entire string" (p. 219).
`AffixTemplate` is the position-class species (a prosodic/CV species
would be its sibling); the rivalry itself is study content, not settled
here.

A word's affix template: the ordered position-class slots of its prefix and
suffix strings, parameterized by the slot type `Slot` — so the order lives
once, as Fragment data, and study files derive their checks from it rather
than re-typing the template. Instantiating at `MorphCategory`
(`Morphology/RelevanceHierarchy.lean`) gives a language's slot order in
relevance-hierarchy vocabulary; a language-specific slot type carries
finer position classes: `Mayan.template` uses `Mayan.VerbSlot`, with the
prefix/suffix split encoding a morpheme's position relative to the verb stem.

## Main definitions

* `Morphology.AffixTemplate` — a word's prefix/suffix slots over an arbitrary slot type.
* `Morphology.PositionClassSystem` — a template with the exponents of each slot, and the
  slots that may be filled more than once; `PositionClassSystem.Licenses` is the affix
  strings it admits.
-/

namespace Morphology

/-- A word's affix position-class template. `suffixSlots` runs stem-outward
(innermost suffix first); `prefixSlots` is listed as the source grammar writes
it, word-edge inward. Slots are `Slot` tags, not exponents — the actual
morphemes live in the citing grammar. -/
structure AffixTemplate (Slot : Type*) where
  /-- Prefix slots, ordered word-edge inward (outermost prefix first). -/
  prefixSlots : List Slot := []
  /-- Suffix slots, ordered stem-outward (innermost suffix first). -/
  suffixSlots : List Slot := []
  deriving Repr, DecidableEq

/-! ### Position-class systems -/

universe u

/-- A position-class system: a slot inventory ordered by an affix template, the exponents of
each slot, and the slots that may be filled by several exponents in sequence. The exponents
are abstract symbols, as the symbols of a `FirstOrder.Language` are; their forms are an
interpretation supplied by the citing grammar. -/
structure PositionClassSystem where
  /-- The position classes. -/
  Slot : Type u
  [decEq : DecidableEq Slot]
  /-- Their order. -/
  template : AffixTemplate Slot
  /-- The exponents of each slot. -/
  Exponent : Slot → Type u
  /-- The slots admitting more than one exponent in sequence. -/
  Iterable : Slot → Prop := fun _ => False
  [decIterable : DecidablePred Iterable]

namespace PositionClassSystem

attribute [instance] decEq decIterable

variable (P : PositionClassSystem)

/-- In the slot order `slots`, `b` may follow `a`: a later slot, or the same iterable slot. -/
def Precedes (slots : List P.Slot) (a b : P.Slot) : Prop :=
  slots.idxOf a < slots.idxOf b ∨ a = b ∧ P.Iterable a

instance (slots : List P.Slot) : DecidableRel (P.Precedes slots) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- The affix strings admitted in the slot order `slots`: every exponent in one of its slots,
consecutive exponents in later or iterable slots. -/
def LicensesIn (slots : List P.Slot) (w : List (Σ s, P.Exponent s)) : Prop :=
  (∀ x ∈ w, x.1 ∈ slots) ∧ (w.map Sigma.fst).IsChain (P.Precedes slots)

instance (slots : List P.Slot) (w : List (Σ s, P.Exponent s)) :
    Decidable (P.LicensesIn slots w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The words the system admits: the prefixes licensed in the prefix order and the suffixes
in the suffix order. -/
def Licenses (pre suf : List (Σ s, P.Exponent s)) : Prop :=
  P.LicensesIn P.template.prefixSlots pre ∧ P.LicensesIn P.template.suffixSlots suf

instance (pre suf : List (Σ s, P.Exponent s)) : Decidable (P.Licenses pre suf) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two exponents of one slot cannot be adjacent unless the slot is iterable. -/
theorem not_licensesIn_pair {s : P.Slot} (h : ¬ P.Iterable s) (slots : List P.Slot)
    (e₁ e₂ : P.Exponent s) : ¬ P.LicensesIn slots [⟨s, e₁⟩, ⟨s, e₂⟩] := by
  simp [LicensesIn, Precedes, h]

end PositionClassSystem

end Morphology
