/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.CategoryTheory.Monoidal.LabeledTuple
import Linglib.Phonology.Autosegmental.NonCrossing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Embedding

/-!
# Floating autosegmental forms

This file defines two-tier autosegmental representations in position coordinates, the
candidates of a serial optimality-theoretic derivation over a fixed representation, and the
one-step GEN on candidates.

A form has an upper tier of autosegments over a lower tier of slots, each element sponsored by
a morpheme of an opaque type, and a set of association lines between positions of the two
tiers. Forms concatenate by juxtaposing the tiers and shifting the right factor's lines past
the left factor's, and they form a monoid under concatenation.

A candidate of a form records the autosegments deleted so far and the current surface lines.
GEN acts on candidates and never on the form, so faithfulness constraints compare the surface
lines with the form's lines. An autosegment that is neither deleted nor linked on the surface
is floating. Several autosegments may share one slot, so contours are representable.

## Main definitions

* `Sponsored α M`: a tier element with the morpheme that sponsors it.
* `Form S T M`: a representation with slots in `S`, autosegments in `T`, and sponsors in
  `M`; `Form.concat` and `Form.empty` make the forms a monoid.
* `Form.IsTautomorphemic`: a line whose autosegment and slot share a sponsor.
* `Candidate u`: the surface state of a derivation from the form `u`; `Candidate.input` is
  the faithful candidate.
* `Candidate.IsFloating`, `Candidate.IsLinked`, `Candidate.IsLinkedLower`: the surface
  predicates on autosegments and slots.
* `Candidate.insertedLinks`, `Candidate.deletedLinks`: the lines GEN has added or removed,
  which the `DEP` and `MAX` constraints count.
* `Candidate.deleteTierElem`, `Candidate.insertLink`, `Candidate.deleteLink`: the atomic
  GEN operations.
* `Candidate.gen`: the one-step GEN, filtered by the No-Crossing Constraint.
* `Candidate.linksTo`, `Candidate.tierValues`, `Candidate.alive`: readings of the surface
  in tier order.

## Main results

* `Form.mem_links_concat`: the lines of a concatenation.
* `Form.isNonCrossing_links_concat`: concatenation preserves the No-Crossing Constraint.
* `Candidate.mem_gen`: the candidates of one GEN step.
* `Candidate.deleted_subset_of_mem_gen`: GEN never resurrects a deleted autosegment.
* `Candidate.isNonCrossing_links_of_mem_gen`: GEN is closed on the No-Crossing Constraint.

## Implementation notes

Positions are elements of `Fin` over the tier lengths, so a candidate shares its form's
tiers by type and every line is in bounds. Numerals for positions of a concrete form need a
`NeZero` instance for its tier lengths, which a study supplies by `decide`. The readings of
the surface are `List.finRange` filters, which reduce under kernel `decide`, because
`Finset.sort` does not unfold structurally.

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

/-- A `Form S T M` is a two-tier autosegmental representation with slots in `S`, autosegments
    in `T`, and sponsors in `M`. Its association lines run from positions of the upper tier
    to positions of the lower tier. -/
structure Form (S T M : Type*) where
  /-- The upper tier, of autosegments in tier order. -/
  upper : LabeledTuple (Sponsored T M)
  /-- The lower tier, of slots in tier order. -/
  lower : LabeledTuple (Sponsored S M)
  /-- The association lines, each from an autosegment to a slot. -/
  links : Finset (Fin upper.len × Fin lower.len)

namespace Form

variable {S T M : Type*} (f g : Form S T M)

/-- Forms are compared tier by tier and then on their lines, which live over the same
    positions once the tiers agree. -/
instance [DecidableEq S] [DecidableEq T] [DecidableEq M] : DecidableEq (Form S T M)
  | ⟨u, l, ls⟩, ⟨u', l', ls'⟩ =>
    if h : u = u' then
      if h' : l = l' then by subst h h'; exact decidable_of_iff (ls = ls') (by simp)
      else isFalse fun he ↦ h' (congrArg lower he)
    else isFalse fun he ↦ h (congrArg upper he)

/-- Two forms are equal when their tiers agree and their lines correspond across the
    resulting identification of positions. -/
theorem ext {f g : Form S T M} (hu : f.upper = g.upper) (hl : f.lower = g.lower)
    (h : ∀ p, p ∈ f.links ↔
      (finCongr (congrArg LabeledTuple.len hu) p.1, finCongr (congrArg LabeledTuple.len hl) p.2)
        ∈ g.links) : f = g := by
  obtain ⟨u, l, ls⟩ := f
  obtain ⟨u', l', ls'⟩ := g
  cases hu
  cases hl
  simp only [finCongr_refl, Equiv.refl_apply] at h
  rw [Finset.ext_iff.2 h]

/-! ### Morphemes -/

/-- `morphemes f` is the set of morphemes sponsoring an element of either tier. -/
def morphemes [DecidableEq M] : Finset M :=
  (f.lower.toList.map Sponsored.morpheme).toFinset ∪
    (f.upper.toList.map Sponsored.morpheme).toFinset

/-- `lowerOfMorpheme f m` lists the slots sponsored by `m` in tier order. -/
def lowerOfMorpheme [DecidableEq M] (m : M) : List (Fin f.lower.len) :=
  (List.finRange f.lower.len).filter fun i ↦ (f.lower.label i).morpheme = m

@[simp] theorem mem_lowerOfMorpheme [DecidableEq M] {m : M} {i : Fin f.lower.len} :
    i ∈ f.lowerOfMorpheme m ↔ (f.lower.label i).morpheme = m := by
  simp [lowerOfMorpheme]

/-- A line is tautomorphemic when its autosegment and its slot have the same sponsor. Such
    lines are the ones `*TAUTDOCK` penalises. -/
def IsTautomorphemic (l : Fin f.upper.len × Fin f.lower.len) : Prop :=
  (f.upper.label l.1).morpheme = (f.lower.label l.2).morpheme

instance [DecidableEq M] (l : Fin f.upper.len × Fin f.lower.len) :
    Decidable (f.IsTautomorphemic l) :=
  inferInstanceAs (Decidable (_ = _))

/-! ### Concatenation

Concatenation juxtaposes the tiers and shifts the right factor's lines past the left factor's
tiers, so the forms are a monoid with the empty form as unit. -/

/-- `concat f g` juxtaposes the tiers of `f` and `g` and shifts the lines of `g` past the tiers
    of `f`. -/
def concat : Form S T M where
  upper := f.upper.concat g.upper
  lower := f.lower.concat g.lower
  links :=
    f.links.map ((Fin.castAddEmb g.upper.len).prodMap (Fin.castAddEmb g.lower.len)) ∪
      g.links.map ((Fin.natAddEmb f.upper.len).prodMap (Fin.natAddEmb f.lower.len))

/-- The empty form has empty tiers and no lines. -/
def empty : Form S T M := ⟨.empty, .empty, ∅⟩

@[simp] theorem concat_upper : (f.concat g).upper = f.upper.concat g.upper := rfl

@[simp] theorem concat_lower : (f.concat g).lower = f.lower.concat g.lower := rfl

@[simp] theorem empty_upper : (empty : Form S T M).upper = .empty := rfl

@[simp] theorem empty_lower : (empty : Form S T M).lower = .empty := rfl

@[simp] theorem empty_links : (empty : Form S T M).links = ∅ := rfl

variable {f g} in
/-- A line of a concatenation is a line of the left factor, or a line of the right factor
    shifted past the left factor's tiers. -/
theorem mem_links_concat {p : Fin (f.concat g).upper.len × Fin (f.concat g).lower.len} :
    p ∈ (f.concat g).links ↔
      (∃ q ∈ f.links, q.1.val = p.1.val ∧ q.2.val = p.2.val) ∨
        ∃ q ∈ g.links, f.upper.len + q.1.val = p.1.val ∧ f.lower.len + q.2.val = p.2.val := by
  obtain ⟨p₁, p₂⟩ := p
  simp [concat, Finset.mem_map, Function.Embedding.prodMap, Prod.ext_iff, Fin.ext_iff]

theorem concat_assoc (h : Form S T M) : (f.concat g).concat h = f.concat (g.concat h) := by
  refine ext (LabeledTuple.concat_assoc ..) (LabeledTuple.concat_assoc ..) fun p ↦ ?_
  have e₁ : (f.concat g).upper.len = f.upper.len + g.upper.len := rfl
  have e₂ : (f.concat g).lower.len = f.lower.len + g.lower.len := rfl
  rw [mem_links_concat (f := f.concat g) (g := h), mem_links_concat (f := f) (g := g.concat h)]
  simp only [finCongr_apply, Fin.val_cast]
  constructor
  · rintro (⟨q, hq, h₁, h₂⟩ | ⟨q, hq, h₁, h₂⟩)
    · rcases mem_links_concat.1 hq with ⟨r, hr, h₃, h₄⟩ | ⟨r, hr, h₃, h₄⟩
      · exact .inl ⟨r, hr, by omega, by omega⟩
      · exact .inr ⟨(Fin.castAdd _ r.1, Fin.castAdd _ r.2),
          mem_links_concat.2 (.inl ⟨r, hr, rfl, rfl⟩),
          by simp only [Fin.val_castAdd]; omega, by simp only [Fin.val_castAdd]; omega⟩
    · exact .inr ⟨(Fin.natAdd _ q.1, Fin.natAdd _ q.2), mem_links_concat.2 (.inr ⟨q, hq, rfl, rfl⟩),
        by simp only [Fin.val_natAdd]; omega, by simp only [Fin.val_natAdd]; omega⟩
  · rintro (⟨q, hq, h₁, h₂⟩ | ⟨q, hq, h₁, h₂⟩)
    · exact .inl ⟨(Fin.castAdd _ q.1, Fin.castAdd _ q.2),
        mem_links_concat.2 (.inl ⟨q, hq, rfl, rfl⟩),
        by simp only [Fin.val_castAdd]; omega, by simp only [Fin.val_castAdd]; omega⟩
    · rcases mem_links_concat.1 hq with ⟨r, hr, h₃, h₄⟩ | ⟨r, hr, h₃, h₄⟩
      · exact .inl ⟨(Fin.natAdd _ r.1, Fin.natAdd _ r.2),
          mem_links_concat.2 (.inr ⟨r, hr, rfl, rfl⟩),
          by simp only [Fin.val_natAdd]; omega, by simp only [Fin.val_natAdd]; omega⟩
      · exact .inr ⟨r, hr, by omega, by omega⟩

theorem empty_concat : empty.concat f = f := by
  refine ext (LabeledTuple.empty_concat _) (LabeledTuple.empty_concat _) fun p ↦ ?_
  have e₁ : (empty : Form S T M).upper.len = 0 := rfl
  have e₂ : (empty : Form S T M).lower.len = 0 := rfl
  rw [mem_links_concat]
  constructor
  · rintro (⟨q, hq, -⟩ | ⟨q, hq, h₁, h₂⟩)
    · exact absurd hq (Finset.notMem_empty _)
    · convert hq using 1
      exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
  · intro hp
    exact .inr ⟨_, hp, by simp, by simp⟩

theorem concat_empty : f.concat empty = f := by
  refine ext (LabeledTuple.concat_empty _) (LabeledTuple.concat_empty _) fun p ↦ ?_
  rw [mem_links_concat]
  constructor
  · rintro (⟨q, hq, h₁, h₂⟩ | ⟨q, hq, -⟩)
    · convert hq using 1
      exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
    · exact absurd hq (Finset.notMem_empty _)
  · intro hp
    exact .inl ⟨_, hp, by simp, by simp⟩

/-- Forms are a monoid under concatenation, with the empty form as unit. -/
instance instMonoid : Monoid (Form S T M) where
  mul := concat
  one := empty
  mul_assoc := concat_assoc
  one_mul := empty_concat
  mul_one := concat_empty

@[simp] theorem mul_eq_concat : f * g = f.concat g := rfl

@[simp] theorem one_eq_empty : (1 : Form S T M) = empty := rfl

/-- Concatenation preserves the No-Crossing Constraint, since every left line precedes every
    shifted right line on both tiers. -/
theorem isNonCrossing_links_concat (h₁ : IsNonCrossing f.links) (h₂ : IsNonCrossing g.links) :
    IsNonCrossing (f.concat g).links := by
  rw [isNonCrossing_iff] at h₁ h₂ ⊢
  intro a ha b hb hab
  rw [Fin.lt_def] at hab
  rw [Fin.le_def]
  rcases mem_links_concat.1 ha with ⟨q, hq, hq₁, hq₂⟩ | ⟨q, hq, hq₁, hq₂⟩ <;>
    rcases mem_links_concat.1 hb with ⟨r, hr, hr₁, hr₂⟩ | ⟨r, hr, hr₁, hr₂⟩
  · have := h₁ q hq r hr (Fin.lt_def.2 (by omega))
    rw [Fin.le_def] at this
    omega
  · omega
  · omega
  · have := h₂ q hq r hr (Fin.lt_def.2 (by omega))
    rw [Fin.le_def] at this
    omega

end Form

/-- A `Candidate u` is the surface state of a derivation from the form `u`, recording the
    autosegments deleted so far and the current surface lines. The faithful candidate is
    `Candidate.input u`, and GEN edits candidates while `u` stays fixed. -/
structure Candidate {S T M : Type*} (u : Form S T M) where
  /-- The autosegments deleted on the surface. -/
  deleted : Finset (Fin u.upper.len)
  /-- The surface association lines. -/
  links : Finset (Fin u.upper.len × Fin u.lower.len)
  deriving DecidableEq

namespace Candidate

variable {S T M : Type*} {u : Form S T M} (c : Candidate u) {k j : Fin u.upper.len}
  {i : Fin u.lower.len} {l : Fin u.upper.len × Fin u.lower.len}

/-- `input u` is the faithful candidate of `u`, with nothing deleted and the form's lines as
    its surface lines. -/
@[simps] def input (u : Form S T M) : Candidate u := ⟨∅, u.links⟩

/-! ### Surface predicates -/

/-- Autosegment `k` is linked when it bears a surface line. -/
def IsLinked (k : Fin u.upper.len) : Prop := ∃ l ∈ c.links, l.1 = k

/-- Slot `i` is linked when it bears a surface line. -/
def IsLinkedLower (i : Fin u.lower.len) : Prop := ∃ l ∈ c.links, l.2 = i

/-- Autosegment `k` is floating when it is not deleted and bears no surface line. -/
def IsFloating (k : Fin u.upper.len) : Prop := k ∉ c.deleted ∧ ¬ c.IsLinked k

/-- `insertedLinks c` is the set of surface lines absent from the form, which GEN has
    inserted and `DEP` counts. -/
def insertedLinks : Finset (Fin u.upper.len × Fin u.lower.len) := c.links \ u.links

/-- `deletedLinks c` is the set of the form's lines absent from the surface, which GEN has
    deleted and `MAX` counts. -/
def deletedLinks : Finset (Fin u.upper.len × Fin u.lower.len) := u.links \ c.links

instance : Decidable (c.IsLinked k) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (c.IsLinkedLower i) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (c.IsFloating k) := inferInstanceAs (Decidable (_ ∧ _))

variable {c}

theorem isLinked_iff : c.IsLinked k ↔ ∃ i, (k, i) ∈ c.links :=
  ⟨fun ⟨⟨_, i⟩, h, rfl⟩ ↦ ⟨i, h⟩, fun ⟨_, h⟩ ↦ ⟨_, h, rfl⟩⟩

theorem isLinkedLower_iff : c.IsLinkedLower i ↔ ∃ k, (k, i) ∈ c.links :=
  ⟨fun ⟨⟨k, _⟩, h, rfl⟩ ↦ ⟨k, h⟩, fun ⟨_, h⟩ ↦ ⟨_, h, rfl⟩⟩

@[simp] theorem mem_insertedLinks : l ∈ c.insertedLinks ↔ l ∈ c.links ∧ l ∉ u.links :=
  Finset.mem_sdiff

@[simp] theorem mem_deletedLinks : l ∈ c.deletedLinks ↔ l ∈ u.links ∧ l ∉ c.links :=
  Finset.mem_sdiff

/-- The faithful candidate has no inserted line. -/
@[simp] theorem insertedLinks_input : (input u).insertedLinks = ∅ := by
  simp [insertedLinks]

/-- The faithful candidate has no deleted line. -/
@[simp] theorem deletedLinks_input : (input u).deletedLinks = ∅ := by
  simp [deletedLinks]

/-! ### Reading the surface

The readings of the surface are lists over `List.finRange` in tier order, which reduce under
kernel `decide`. -/

variable (c)

/-- `linksTo c i` lists the autosegments linked to slot `i` on the surface, in tier order. -/
def linksTo (i : Fin u.lower.len) : List (Fin u.upper.len) :=
  (List.finRange u.upper.len).filter fun k ↦ (k, i) ∈ c.links

/-- `tierValues c i` lists the values of the autosegments linked to slot `i` on the surface,
    in tier order. -/
def tierValues (i : Fin u.lower.len) : List T :=
  (c.linksTo i).map fun k ↦ (u.upper.label k).value

/-- `alive c` lists the undeleted autosegments in tier order. -/
def alive : List (Fin u.upper.len) := (List.finRange u.upper.len).filter (· ∉ c.deleted)

variable {c}

@[simp] theorem mem_linksTo : k ∈ c.linksTo i ↔ (k, i) ∈ c.links := by
  simp [linksTo]

variable (c) in
theorem nodup_linksTo (i : Fin u.lower.len) : (c.linksTo i).Nodup :=
  (List.nodup_finRange _).filter _

@[simp] theorem mem_tierValues {t : T} :
    t ∈ c.tierValues i ↔ ∃ k, (k, i) ∈ c.links ∧ (u.upper.label k).value = t := by
  simp [tierValues]

@[simp] theorem mem_alive : k ∈ c.alive ↔ k ∉ c.deleted := by
  simp [alive]

/-! ### The atomic GEN operations -/

variable (c)

/-- `deleteTierElem c k` deletes autosegment `k` on the surface, together with every surface
    line it bears. -/
@[simps] def deleteTierElem (k : Fin u.upper.len) : Candidate u :=
  ⟨insert k c.deleted, c.links.filter (·.1 ≠ k)⟩

/-- `insertLink c k i` inserts the surface line from autosegment `k` to slot `i`. -/
@[simps] def insertLink (k : Fin u.upper.len) (i : Fin u.lower.len) : Candidate u :=
  ⟨c.deleted, insert (k, i) c.links⟩

/-- `deleteLink c k i` deletes the surface line from autosegment `k` to slot `i`. -/
@[simps] def deleteLink (k : Fin u.upper.len) (i : Fin u.lower.len) : Candidate u :=
  ⟨c.deleted, c.links.erase (k, i)⟩

variable {c}

@[simp] theorem isLinked_deleteTierElem :
    (c.deleteTierElem k).IsLinked j ↔ j ≠ k ∧ c.IsLinked j := by
  simp only [isLinked_iff, deleteTierElem_links, Finset.mem_filter]
  aesop

@[simp] theorem isLinked_insertLink : (c.insertLink k i).IsLinked j ↔ j = k ∨ c.IsLinked j := by
  simp only [isLinked_iff, insertLink_links, Finset.mem_insert, Prod.mk.injEq]
  aesop

@[simp] theorem isLinkedLower_insertLink {i' : Fin u.lower.len} :
    (c.insertLink k i).IsLinkedLower i' ↔ i' = i ∨ c.IsLinkedLower i' := by
  simp only [isLinkedLower_iff, insertLink_links, Finset.mem_insert, Prod.mk.injEq]
  aesop

@[simp] theorem isFloating_deleteTierElem :
    (c.deleteTierElem k).IsFloating j ↔ j ≠ k ∧ c.IsFloating j := by
  simp only [IsFloating, deleteTierElem_deleted, Finset.mem_insert, isLinked_deleteTierElem]
  tauto

@[simp] theorem isFloating_insertLink :
    (c.insertLink k i).IsFloating j ↔ j ≠ k ∧ c.IsFloating j := by
  simp only [IsFloating, insertLink_deleted, isLinked_insertLink]
  tauto

theorem links_deleteTierElem_subset : (c.deleteTierElem k).links ⊆ c.links :=
  Finset.filter_subset _ _

theorem links_subset_insertLink : c.links ⊆ (c.insertLink k i).links :=
  Finset.subset_insert _ _

/-! ### One-step GEN -/

section Gen

variable [DecidableEq S] [DecidableEq T] [DecidableEq M] {c' : Candidate u}

/-- `gen c` is the one-step GEN of harmonic serialism. It contains `c` itself, the deletion of
    each undeleted autosegment, and each line from a floating autosegment to a slot that
    crosses no surface line; insert-and-associate and shift are omitted. -/
def gen (c : Candidate u) : Finset (Candidate u) :=
  insert c <|
    (Finset.univ.filter (· ∉ c.deleted)).image c.deleteTierElem ∪
      ((Finset.univ.filter c.IsFloating ×ˢ Finset.univ).filter
        fun p ↦ ¬ IndexCrosses c.links p).image fun p ↦ c.insertLink p.1 p.2

theorem mem_gen : c' ∈ c.gen ↔ c' = c ∨ (∃ k ∉ c.deleted, c' = c.deleteTierElem k) ∨
    ∃ k i, c.IsFloating k ∧ ¬ IndexCrosses c.links (k, i) ∧ c' = c.insertLink k i := by
  simp only [gen, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product, and_true, Prod.exists, and_assoc,
    eq_comm (a := c')]

@[simp] theorem self_mem_gen : c ∈ c.gen := Finset.mem_insert_self _ _

theorem deleteTierElem_mem_gen (hd : k ∉ c.deleted) : c.deleteTierElem k ∈ c.gen :=
  mem_gen.2 (.inr (.inl ⟨k, hd, rfl⟩))

theorem insertLink_mem_gen (hk : c.IsFloating k) (hx : ¬ IndexCrosses c.links (k, i)) :
    c.insertLink k i ∈ c.gen :=
  mem_gen.2 (.inr (.inr ⟨k, i, hk, hx, rfl⟩))

/-- GEN never resurrects a deleted autosegment. -/
theorem deleted_subset_of_mem_gen (hc : c' ∈ c.gen) : c.deleted ⊆ c'.deleted := by
  rcases mem_gen.1 hc with rfl | ⟨_, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
  exacts [subset_rfl, Finset.subset_insert _ _, subset_rfl]

/-- GEN is closed on the No-Crossing Constraint, since deletion shrinks the surface lines and
    each inserted line passed the crossing filter. -/
theorem isNonCrossing_links_of_mem_gen (h : IsNonCrossing c.links) (hc : c' ∈ c.gen) :
    IsNonCrossing c'.links := by
  rcases mem_gen.1 hc with rfl | ⟨_, -, rfl⟩ | ⟨_, _, -, hx, rfl⟩
  exacts [h, h.subset links_deleteTierElem_subset, h.insert_of_not_indexCrosses hx]

end Gen

end Candidate

end Autosegmental
