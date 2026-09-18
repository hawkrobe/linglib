/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.CategoryTheory.Monoidal.LabeledTuple
import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Floating autosegmental forms

This file defines two-tier autosegmental forms in position coordinates, with the surface
bookkeeping of a serial optimality-theoretic derivation, and the one-step GEN over them.

A floating form has an upper tier of autosegments over a lower tier of slots, each element
sponsored by a morpheme of an opaque type, and a set of underlying association lines between
positions of the two tiers. Its surface state consists of the autosegments deleted so far and
the current surface lines. GEN edits the surface state and never the underlying one, so that
faithfulness constraints can compare the two. An autosegment that is neither deleted nor
linked on the surface is floating. Several autosegments may share one slot, so contours are
representable.

An input form is one whose surface state is its underlying state. Input forms are closed
under concatenation, which juxtaposes the tiers and shifts the right factor's lines past the
left factor's, and they form a monoid under it.

## Main definitions

* `Sponsored α M`: a tier element with the morpheme that sponsors it.
* `FloatingForm S T M`: an autosegmental form with slots in `S`, autosegments in `T`, and
  sponsors in `M`.
* `FloatingForm.input`: the form of an underlying representation, whose surface state is
  its underlying state; `FloatingForm.IsInput` recognises such forms.
* `FloatingForm.concat`: the concatenation of two underlying forms; `FloatingForm.concatInputs`
  concatenates a list.
* `FloatingForm.IsFloating`, `FloatingForm.IsLinked`, `FloatingForm.IsLinkedLower`,
  `FloatingForm.IsTautomorphemic`: the surface predicates on autosegments, slots, and lines.
* `FloatingForm.insertedLinks`, `FloatingForm.deletedLinks`: the lines GEN has added or
  removed, which the `DEP` and `MAX` constraints count.
* `FloatingForm.deleteTierElem`, `FloatingForm.insertLink`, `FloatingForm.deleteLink`: the
  atomic GEN operations.
* `FloatingForm.gen`: the one-step GEN, filtered by the No-Crossing Constraint.
* `FloatingForm.linksTo`, `FloatingForm.tierValues`, `FloatingForm.aliveTierIdxs`,
  `FloatingForm.lowerOfMorpheme`: readings of the surface in tier order.

## Main results

* `FloatingForm.mem_gen`: the candidates of one GEN step.
* `FloatingForm.upper_of_mem_gen`, `FloatingForm.lower_of_mem_gen`,
  `FloatingForm.links_of_mem_gen`: GEN edits only the surface.
* `FloatingForm.isNonCrossing_surfaceLinks_of_mem_gen`: GEN is closed on the No-Crossing
  Constraint.
* `FloatingForm.concat_assoc`, `FloatingForm.empty_concat`, `FloatingForm.concat_empty`:
  input forms form a monoid under concatenation.
* `FloatingForm.links_concat_subset`, `FloatingForm.isNonCrossing_links_concat`:
  concatenation keeps the lines in bounds and non-crossing.

## Implementation notes

Positions are natural numbers rather than elements of `Fin`, so that concatenation shifts
lines arithmetically and the studies' tableaux reduce under `decide`. An out-of-range line is
harmless, since every reading is guarded by a tier length, and `links_concat_subset` tracks
the bound. The readings of the surface are `List.range` filters, because `Finset.sort` does
not unfold structurally.

## References

* [goldsmith-1976]
* [pulleyblank-1986]
* [wolf-2007]
* [mccarthy-mullin-smith-2012]
* [mcpherson-lamont-2026]
* [lieber-1983]
* [laoide-kemp-2026]
* [zimmermann-2017]
* [jardine-heinz-2015]
-/

namespace Autosegmental

/-- A `Sponsored α M` is a tier element of type `α` together with the morpheme of type `M`
    that sponsors it. On the upper tier the element is an autosegment, on the lower tier a
    slot. -/
structure Sponsored (α M : Type*) where
  /-- The autosegment or slot. -/
  value : α
  /-- The sponsoring morpheme. -/
  morpheme : M
  deriving DecidableEq, Repr

/-- A `FloatingForm S T M` is a two-tier autosegmental form with slots in `S`, autosegments
    in `T`, and sponsors in `M`, together with the surface state of a serial derivation. The
    tiers and the underlying lines are fixed, and GEN edits `deleted` and `surfaceLinks`. -/
@[ext]
structure FloatingForm (S T M : Type*) where
  /-- The upper tier, of autosegments in tier order. -/
  upper : LabeledTuple (Sponsored T M)
  /-- The lower tier, of slots in tier order. -/
  lower : LabeledTuple (Sponsored S M)
  /-- The underlying association lines, each from an autosegment to a slot. -/
  links : Finset (ℕ × ℕ)
  /-- The autosegments deleted on the surface. -/
  deleted : Finset ℕ
  /-- The surface association lines. -/
  surfaceLinks : Finset (ℕ × ℕ)
  deriving DecidableEq

namespace FloatingForm

variable {S T M : Type*}

section Basic

variable (f : FloatingForm S T M) {k i : ℕ} {l : ℕ × ℕ}

/-! ### Morphemes -/

/-- `upperMorpheme? f k` is the sponsor of autosegment `k`, or `none` when `k` is out of
    range. -/
def upperMorpheme? (k : ℕ) : Option M := (f.upper.get? k).map Sponsored.morpheme

/-- `lowerMorpheme? f i` is the sponsor of slot `i`, or `none` when `i` is out of range. -/
def lowerMorpheme? (i : ℕ) : Option M := (f.lower.get? i).map Sponsored.morpheme

/-- `morphemes f` is the set of morphemes sponsoring an element of either tier. -/
def morphemes [DecidableEq M] : Finset M :=
  (f.lower.toList.map Sponsored.morpheme).toFinset ∪
    (f.upper.toList.map Sponsored.morpheme).toFinset

/-- `lowerOfMorpheme f m` lists the slots sponsored by `m` in tier order. -/
def lowerOfMorpheme [DecidableEq M] (m : M) : List ℕ :=
  (List.range f.lower.len).filter fun i ↦ f.lowerMorpheme? i = some m

@[simp] theorem mem_lowerOfMorpheme [DecidableEq M] {m : M} :
    i ∈ f.lowerOfMorpheme m ↔ i < f.lower.len ∧ f.lowerMorpheme? i = some m := by
  simp [lowerOfMorpheme]

/-! ### Surface predicates -/

/-- Autosegment `k` is linked when it bears a surface line. -/
def IsLinked (k : ℕ) : Prop := ∃ l ∈ f.surfaceLinks, l.1 = k

/-- Slot `i` is linked when it bears a surface line. -/
def IsLinkedLower (i : ℕ) : Prop := ∃ l ∈ f.surfaceLinks, l.2 = i

/-- Autosegment `k` is floating when it lies on the tier, is not deleted, and bears no surface
    line. -/
def IsFloating (k : ℕ) : Prop := k < f.upper.len ∧ k ∉ f.deleted ∧ ¬ f.IsLinked k

/-- A line is tautomorphemic when its autosegment and its slot have the same sponsor. Such
    lines are the ones `*TAUTDOCK` penalises. -/
def IsTautomorphemic (l : ℕ × ℕ) : Prop :=
  ∃ m, f.upperMorpheme? l.1 = some m ∧ f.lowerMorpheme? l.2 = some m

/-- `insertedLinks f` is the set of surface lines absent from the underlying form, which GEN
    has inserted and `DEP` counts. -/
def insertedLinks : Finset (ℕ × ℕ) := f.surfaceLinks \ f.links

/-- `deletedLinks f` is the set of underlying lines absent from the surface, which GEN has
    deleted and `MAX` counts. -/
def deletedLinks : Finset (ℕ × ℕ) := f.links \ f.surfaceLinks

instance : Decidable (f.IsLinked k) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (f.IsLinkedLower i) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (f.IsFloating k) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq M] : Decidable (f.IsTautomorphemic l) :=
  decidable_of_iff ((f.upperMorpheme? l.1).isSome ∧ f.upperMorpheme? l.1 = f.lowerMorpheme? l.2)
    (by cases h : f.upperMorpheme? l.1 <;> simp [IsTautomorphemic, h, eq_comm])

theorem isLinked_iff : f.IsLinked k ↔ ∃ i, (k, i) ∈ f.surfaceLinks :=
  ⟨fun ⟨⟨_, i⟩, h, rfl⟩ ↦ ⟨i, h⟩, fun ⟨_, h⟩ ↦ ⟨_, h, rfl⟩⟩

theorem isLinkedLower_iff : f.IsLinkedLower i ↔ ∃ k, (k, i) ∈ f.surfaceLinks :=
  ⟨fun ⟨⟨k, _⟩, h, rfl⟩ ↦ ⟨k, h⟩, fun ⟨_, h⟩ ↦ ⟨_, h, rfl⟩⟩

@[simp] theorem mem_insertedLinks : l ∈ f.insertedLinks ↔ l ∈ f.surfaceLinks ∧ l ∉ f.links :=
  Finset.mem_sdiff

@[simp] theorem mem_deletedLinks : l ∈ f.deletedLinks ↔ l ∈ f.links ∧ l ∉ f.surfaceLinks :=
  Finset.mem_sdiff

/-! ### Reading the surface

The readings of the surface are lists over `List.range` in tier order, which reduce under
kernel `decide`. -/

/-- `linksTo f i` lists the autosegments linked to slot `i` on the surface, in tier order. -/
def linksTo (i : ℕ) : List ℕ :=
  (List.range f.upper.len).filter fun k ↦ (k, i) ∈ f.surfaceLinks

/-- `tierValues f i` lists the values of the autosegments linked to slot `i` on the surface,
    in tier order. -/
def tierValues (i : ℕ) : List T :=
  (f.linksTo i).filterMap fun k ↦ (f.upper.get? k).map Sponsored.value

/-- `aliveTierIdxs f` lists the undeleted autosegments in tier order. -/
def aliveTierIdxs : List ℕ := (List.range f.upper.len).filter (· ∉ f.deleted)

@[simp] theorem mem_linksTo : k ∈ f.linksTo i ↔ k < f.upper.len ∧ (k, i) ∈ f.surfaceLinks := by
  simp [linksTo]

theorem nodup_linksTo (i : ℕ) : (f.linksTo i).Nodup := List.nodup_range.filter _

@[simp] theorem mem_tierValues {t : T} : t ∈ f.tierValues i ↔
    ∃ k, (k, i) ∈ f.surfaceLinks ∧ (f.upper.get? k).map Sponsored.value = some t := by
  simp only [tierValues, List.mem_filterMap, mem_linksTo]
  constructor
  · rintro ⟨k, ⟨-, hk⟩, ht⟩
    exact ⟨k, hk, ht⟩
  · rintro ⟨k, hk, ht⟩
    refine ⟨k, ⟨?_, hk⟩, ht⟩
    by_contra h
    simp [LabeledTuple.get?, h] at ht

@[simp] theorem mem_aliveTierIdxs : k ∈ f.aliveTierIdxs ↔ k < f.upper.len ∧ k ∉ f.deleted := by
  simp [aliveTierIdxs]

/-! ### The atomic GEN operations -/

/-- `deleteTierElem f k` deletes autosegment `k` on the surface, together with every surface
    line it bears. -/
@[simps] def deleteTierElem (k : ℕ) : FloatingForm S T M :=
  { f with deleted := insert k f.deleted, surfaceLinks := f.surfaceLinks.filter (·.1 ≠ k) }

/-- `insertLink f k i` inserts the surface line from autosegment `k` to slot `i`. -/
@[simps] def insertLink (k i : ℕ) : FloatingForm S T M :=
  { f with surfaceLinks := insert (k, i) f.surfaceLinks }

/-- `deleteLink f k i` deletes the surface line from autosegment `k` to slot `i`. -/
@[simps] def deleteLink (k i : ℕ) : FloatingForm S T M :=
  { f with surfaceLinks := f.surfaceLinks.erase (k, i) }

variable {f} {j : ℕ}

@[simp] theorem isLinked_deleteTierElem :
    (f.deleteTierElem k).IsLinked j ↔ j ≠ k ∧ f.IsLinked j := by
  simp only [isLinked_iff, deleteTierElem_surfaceLinks, Finset.mem_filter]
  aesop

@[simp] theorem isLinked_insertLink : (f.insertLink k i).IsLinked j ↔ j = k ∨ f.IsLinked j := by
  simp only [isLinked_iff, insertLink_surfaceLinks, Finset.mem_insert, Prod.mk.injEq]
  aesop

@[simp] theorem isLinkedLower_insertLink :
    (f.insertLink k i).IsLinkedLower j ↔ j = i ∨ f.IsLinkedLower j := by
  simp only [isLinkedLower_iff, insertLink_surfaceLinks, Finset.mem_insert, Prod.mk.injEq]
  aesop

@[simp] theorem isFloating_deleteTierElem :
    (f.deleteTierElem k).IsFloating j ↔ j ≠ k ∧ f.IsFloating j := by
  simp only [IsFloating, deleteTierElem_upper, deleteTierElem_deleted, Finset.mem_insert,
    isLinked_deleteTierElem]
  tauto

@[simp] theorem isFloating_insertLink :
    (f.insertLink k i).IsFloating j ↔ j ≠ k ∧ f.IsFloating j := by
  simp only [IsFloating, insertLink_upper, insertLink_deleted, isLinked_insertLink]
  tauto

theorem surfaceLinks_deleteTierElem_subset : (f.deleteTierElem k).surfaceLinks ⊆ f.surfaceLinks :=
  Finset.filter_subset _ _

theorem surfaceLinks_subset_insertLink : f.surfaceLinks ⊆ (f.insertLink k i).surfaceLinks :=
  Finset.subset_insert _ _

end Basic

/-! ### One-step GEN -/

section Gen

variable [DecidableEq S] [DecidableEq T] [DecidableEq M] (f : FloatingForm S T M)
  {g : FloatingForm S T M} {k i : ℕ}

/-- `gen f` is the one-step GEN of harmonic serialism. It contains `f` itself, the deletion of
    each undeleted autosegment, and each line from a floating autosegment to a slot that
    crosses no surface line; insert-and-associate and shift are omitted. -/
def gen : Finset (FloatingForm S T M) :=
  insert f <|
    ((Finset.range f.upper.len).filter (· ∉ f.deleted)).image f.deleteTierElem ∪
      ((((Finset.range f.upper.len).filter f.IsFloating) ×ˢ Finset.range f.lower.len).filter
        fun p ↦ ¬ IndexCrosses f.surfaceLinks p).image fun p ↦ f.insertLink p.1 p.2

variable {f}

theorem mem_gen : g ∈ f.gen ↔ g = f ∨
    (∃ k < f.upper.len, k ∉ f.deleted ∧ g = f.deleteTierElem k) ∨
      ∃ k i, f.IsFloating k ∧ i < f.lower.len ∧ ¬ IndexCrosses f.surfaceLinks (k, i) ∧
        g = f.insertLink k i := by
  simp only [gen, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range, Finset.mem_product, Prod.exists, eq_comm (a := g)]
  refine or_congr_right (or_congr (exists_congr fun k ↦ by tauto) ⟨?_, ?_⟩)
  · rintro ⟨k, i, ⟨⟨⟨-, hf⟩, hi⟩, hx⟩, rfl⟩
    exact ⟨k, i, hf, hi, hx, rfl⟩
  · rintro ⟨k, i, hf, hi, hx, rfl⟩
    exact ⟨k, i, ⟨⟨⟨hf.1, hf⟩, hi⟩, hx⟩, rfl⟩

@[simp] theorem self_mem_gen : f ∈ f.gen := Finset.mem_insert_self _ _

theorem deleteTierElem_mem_gen (hk : k < f.upper.len) (hd : k ∉ f.deleted) :
    f.deleteTierElem k ∈ f.gen :=
  mem_gen.2 (.inr (.inl ⟨k, hk, hd, rfl⟩))

theorem insertLink_mem_gen (hk : f.IsFloating k) (hi : i < f.lower.len)
    (hx : ¬ IndexCrosses f.surfaceLinks (k, i)) : f.insertLink k i ∈ f.gen :=
  mem_gen.2 (.inr (.inr ⟨k, i, hk, hi, hx, rfl⟩))

theorem upper_of_mem_gen (hg : g ∈ f.gen) : g.upper = f.upper := by
  rcases mem_gen.1 hg with rfl | ⟨_, -, -, rfl⟩ | ⟨_, _, -, -, -, rfl⟩ <;> rfl

theorem lower_of_mem_gen (hg : g ∈ f.gen) : g.lower = f.lower := by
  rcases mem_gen.1 hg with rfl | ⟨_, -, -, rfl⟩ | ⟨_, _, -, -, -, rfl⟩ <;> rfl

theorem links_of_mem_gen (hg : g ∈ f.gen) : g.links = f.links := by
  rcases mem_gen.1 hg with rfl | ⟨_, -, -, rfl⟩ | ⟨_, _, -, -, -, rfl⟩ <;> rfl

/-- GEN never resurrects a deleted autosegment. -/
theorem deleted_subset_of_mem_gen (hg : g ∈ f.gen) : f.deleted ⊆ g.deleted := by
  rcases mem_gen.1 hg with rfl | ⟨_, -, -, rfl⟩ | ⟨_, _, -, -, -, rfl⟩
  exacts [subset_rfl, Finset.subset_insert _ _, subset_rfl]

/-- GEN is closed on the No-Crossing Constraint, since deletion shrinks the surface lines and
    each inserted line passed the crossing filter. -/
theorem isNonCrossing_surfaceLinks_of_mem_gen (h : IsNonCrossing f.surfaceLinks)
    (hg : g ∈ f.gen) : IsNonCrossing g.surfaceLinks := by
  rcases mem_gen.1 hg with rfl | ⟨_, -, -, rfl⟩ | ⟨_, _, -, -, hx, rfl⟩
  exacts [h, h.subset surfaceLinks_deleteTierElem_subset, h.insert_of_not_indexCrosses hx]

/-- GEN keeps the surface lines in bounds, since it inserts lines only between positions on
    the tiers. -/
theorem surfaceLinks_subset_of_mem_gen
    (h : f.surfaceLinks ⊆ Finset.range f.upper.len ×ˢ Finset.range f.lower.len) (hg : g ∈ f.gen) :
    g.surfaceLinks ⊆ Finset.range g.upper.len ×ˢ Finset.range g.lower.len := by
  rcases mem_gen.1 hg with rfl | ⟨_, -, -, rfl⟩ | ⟨_, _, ⟨hk, -⟩, hi, -, rfl⟩
  · exact h
  · exact surfaceLinks_deleteTierElem_subset.trans h
  · simp only [insertLink_surfaceLinks, insertLink_upper, insertLink_lower]
    exact Finset.insert_subset (by simp [hk, hi]) h

end Gen

/-! ### Input forms and concatenation

An input form is one whose surface state is its underlying state. Input forms are closed
under concatenation, which juxtaposes the tiers and shifts the right factor's lines past the
left factor's, and they form a monoid under it. -/

section Input

variable {f g : FloatingForm S T M}

/-- `input upper lower links` is the form of an underlying representation, with nothing
    deleted and the underlying lines as its surface lines. -/
@[simps] def input (upper : LabeledTuple (Sponsored T M)) (lower : LabeledTuple (Sponsored S M))
    (links : Finset (ℕ × ℕ)) : FloatingForm S T M :=
  ⟨upper, lower, links, ∅, links⟩

/-- The empty form has empty tiers and no lines. -/
def empty : FloatingForm S T M := input .empty .empty ∅

/-- A form is an input when its surface state is its underlying state. -/
def IsInput (f : FloatingForm S T M) : Prop := f.deleted = ∅ ∧ f.surfaceLinks = f.links

instance : Decidable f.IsInput := inferInstanceAs (Decidable (_ ∧ _))

theorem isInput_iff : f.IsInput ↔ f = input f.upper f.lower f.links := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact FloatingForm.ext rfl rfl rfl h₁ h₂
  · intro h
    exact ⟨congrArg deleted h, congrArg surfaceLinks h⟩

@[simp] theorem isInput_input (upper lower links) :
    (input (S := S) (T := T) (M := M) upper lower links).IsInput := ⟨rfl, rfl⟩

@[simp] theorem isInput_empty : (empty : FloatingForm S T M).IsInput := ⟨rfl, rfl⟩

/-- An input has no inserted line. -/
@[simp] theorem IsInput.insertedLinks_eq_empty (h : f.IsInput) : f.insertedLinks = ∅ := by
  simp [insertedLinks, h.2]

/-- An input has no deleted line. -/
@[simp] theorem IsInput.deletedLinks_eq_empty (h : f.IsInput) : f.deletedLinks = ∅ := by
  simp [deletedLinks, h.2]

variable (f) (g)

/-- `concat f g` juxtaposes the tiers of `f` and `g` and shifts the lines of `g` past the tiers
    of `f`, as an input form. -/
def concat : FloatingForm S T M :=
  input (f.upper.concat g.upper) (f.lower.concat g.lower)
    (f.links ∪ g.links.image (shiftLink f.upper.len f.lower.len))

@[simp] theorem concat_upper : (f.concat g).upper = f.upper.concat g.upper := rfl

@[simp] theorem concat_lower : (f.concat g).lower = f.lower.concat g.lower := rfl

@[simp] theorem concat_links :
    (f.concat g).links = f.links ∪ g.links.image (shiftLink f.upper.len f.lower.len) := rfl

@[simp] theorem concat_deleted : (f.concat g).deleted = ∅ := rfl

@[simp] theorem concat_surfaceLinks : (f.concat g).surfaceLinks = (f.concat g).links := rfl

@[simp] theorem isInput_concat : (f.concat g).IsInput := ⟨rfl, rfl⟩

theorem concat_assoc (h : FloatingForm S T M) : (f.concat g).concat h = f.concat (g.concat h) := by
  refine FloatingForm.ext (LabeledTuple.concat_assoc ..) (LabeledTuple.concat_assoc ..) ?_ rfl ?_
  all_goals simp [Finset.image_union, Finset.image_image, shiftLink_comp, Finset.union_assoc]

variable {f g}

theorem empty_concat (h : g.IsInput) : empty.concat g = g := by
  rw [isInput_iff.1 h]
  exact FloatingForm.ext (LabeledTuple.empty_concat _) (LabeledTuple.empty_concat _)
    (by simp [empty]) rfl (by simp [empty])

theorem concat_empty (h : f.IsInput) : f.concat empty = f := by
  rw [isInput_iff.1 h]
  exact FloatingForm.ext (LabeledTuple.concat_empty _) (LabeledTuple.concat_empty _)
    (by simp [empty]) rfl (by simp [empty])

/-- Concatenation keeps the lines in bounds. -/
theorem links_concat_subset
    (hf : f.links ⊆ Finset.range f.upper.len ×ˢ Finset.range f.lower.len)
    (hg : g.links ⊆ Finset.range g.upper.len ×ˢ Finset.range g.lower.len) :
    (f.concat g).links ⊆
      Finset.range (f.concat g).upper.len ×ˢ Finset.range (f.concat g).lower.len := by
  simp only [concat_links, concat_upper, concat_lower, LabeledTuple.concat_len,
    Finset.union_subset_iff, Finset.image_subset_iff]
  refine ⟨hf.trans (Finset.product_subset_product (Finset.range_mono (Nat.le_add_right _ _))
    (Finset.range_mono (Nat.le_add_right _ _))), fun p hp ↦ ?_⟩
  have := hg hp
  simp only [Finset.mem_product, Finset.mem_range] at this ⊢
  simp only [shiftLink_apply]
  omega

/-- Concatenation preserves the No-Crossing Constraint when the left factor's lines are in
    bounds, since every left line then precedes every shifted right line on both tiers. -/
theorem isNonCrossing_links_concat
    (hf : f.links ⊆ Finset.range f.upper.len ×ˢ Finset.range f.lower.len)
    (h₁ : IsNonCrossing f.links) (h₂ : IsNonCrossing g.links) :
    IsNonCrossing (f.concat g).links := by
  rw [concat_links, isNonCrossing_union_iff]
  refine ⟨h₁, (isNonCrossing_image_shiftLink _ _ _).2 h₂, fun a ha b hb ↦ ?_⟩
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hb
  have := hf ha
  simp only [Finset.mem_product, Finset.mem_range] at this
  rw [isNonCrossing_pair]
  simp only [shiftLink_apply]
  omega

/-- `concatInputs gs` concatenates the forms in `gs` from left to right. -/
def concatInputs (gs : List (FloatingForm S T M)) : FloatingForm S T M := gs.foldr concat empty

@[simp] theorem concatInputs_nil : concatInputs ([] : List (FloatingForm S T M)) = empty := rfl

@[simp] theorem concatInputs_cons (g : FloatingForm S T M) (gs : List (FloatingForm S T M)) :
    concatInputs (g :: gs) = g.concat (concatInputs gs) := rfl

theorem isInput_concatInputs (gs : List (FloatingForm S T M)) : (concatInputs gs).IsInput := by
  cases gs <;> simp

/-- Input forms form a monoid under concatenation, with the empty form as unit. -/
instance instMonoidSubtypeIsInput : Monoid {f : FloatingForm S T M // f.IsInput} where
  mul f g := ⟨f.1.concat g.1, isInput_concat _ _⟩
  one := ⟨empty, isInput_empty⟩
  mul_assoc _ _ _ := Subtype.ext (concat_assoc ..)
  one_mul f := Subtype.ext (empty_concat f.2)
  mul_one f := Subtype.ext (concat_empty f.2)

end Input

end FloatingForm

end Autosegmental
