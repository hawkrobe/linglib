/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Focus.Unalternatives

/-!
# Unalternative Semantics: the prosodic origin

Formalises [buring-2015]: calculating focus alternatives without
F-markers, from metrical structure alone. A branching node's stress
pattern restricts its focal targets. Under the default weak–strong
pattern the Weak Restriction ((4), the revision of the preliminary
(1) that keeps a node's literal meaning out of the banned set) bans
targets varying the weak daughter non-trivially while the strong stays
at its ordinary value; under prosodic reversal the Strong Restriction
((9)) allows exactly those same targets, so the two patterns divide a
node's focal targets between them.

The worked example is his *ordered BREAKfast* vs *ORDERED breakfast*:
default stress bans exactly *paid for breakfast*, licensing "all VP
meanings, except those that are relations to breakfast other than
ordering breakfast"; reversal licenses exactly what the default bans. The rules live in
`Semantics/Focus/Unalternatives.lean`, shared with the
morphosyntactic extension of [assmann-etal-2023].
-/

namespace Buring2015

open Focus (weakBanned strongAllowed licensedFocusValue)

/-- Transitive-verb meanings. -/
inductive Rel where
  | ordered | paidFor
  deriving DecidableEq, Repr

/-- Object meanings. -/
inductive Obj where
  | breakfast | lunch
  deriving DecidableEq, Repr

/-- VP meanings as verb–object applications, modelled as pairs. -/
def vt (r : Rel) : Obj → Rel × Obj := fun o => (r, o)

/-- *ordered*, with its transitive alternatives. -/
def orderedM : WithAlternatives (Obj → Rel × Obj) :=
  ⟨vt .ordered, {vt .ordered, vt .paidFor}⟩

/-- *breakfast*, with its object alternatives. -/
def breakfastM : WithAlternatives Obj := ⟨Obj.breakfast, {Obj.breakfast, Obj.lunch}⟩

private theorem vt_ne : vt .paidFor ≠ vt .ordered := fun h => by
  have := congrFun h .breakfast
  exact absurd (congrArg Prod.fst this) (by decide)

/-- Under default stress the banned targets are exactly the verb-focus ones: *paid for breakfast*
and nothing else. The subtraction of the weak daughter's ordinary value in (4) is what keeps
*ordered breakfast* itself out of the banned set. -/
theorem weakBanned_eq :
    weakBanned orderedM breakfastM = {(Rel.paidFor, Obj.breakfast)} := by
  ext ⟨r, o⟩
  simp only [weakBanned, Set.mem_seq_iff, Set.mem_sdiff, Set.mem_singleton_iff,
    Set.mem_insert_iff, orderedM, breakfastM]
  constructor
  · rintro ⟨f, ⟨rfl | rfl, hne⟩, a, rfl, heq⟩
    · exact absurd rfl hne
    · exact heq.symm
  · intro h
    exact ⟨vt .paidFor, ⟨Or.inr rfl, vt_ne⟩, .breakfast, rfl, by rw [h]; rfl⟩

/-- Default *ordered BREAKfast* bans the verb-focus target *paid for breakfast*: it varies the weak
daughter over given *breakfast*. -/
theorem default_bans_verb_focus :
    (Rel.paidFor, Obj.breakfast) ∈ weakBanned orderedM breakfastM := by
  rw [weakBanned_eq]; rfl

/-- It permits the object-focus target *ordered lunch*: no composition holds *breakfast* fixed. -/
theorem default_permits_object_focus :
    (Rel.ordered, Obj.lunch) ∉ weakBanned orderedM breakfastM := by
  rw [weakBanned_eq]; decide

/-- And it permits the node's own literal meaning. This is what rule (4) secures over the
preliminary (1), which banned it: "we should never, at the lower (VP) level, exclude the literal
meaning of a neutral node". -/
theorem default_permits_ordinary_value :
    (Rel.ordered, Obj.breakfast) ∉ weakBanned orderedM breakfastM := by
  rw [weakBanned_eq]; decide

/-- Reversed *ORDERED breakfast* allows exactly what the default bans — an instance of
`Focus.strongAllowed_eq_weakBanned`, so the two metrical patterns of the node divide its focal
targets between them. -/
theorem reversal_allows_exactly_default_bans :
    strongAllowed orderedM breakfastM = weakBanned orderedM breakfastM :=
  Focus.strongAllowed_eq_weakBanned _ _

/-- In particular reversal allows the non-trivial verb-focus target and nothing else: neither the
ordinary value nor an object-focus target. -/
theorem reversal_allows_only_verb_focus :
    (Rel.paidFor, Obj.breakfast) ∈ strongAllowed orderedM breakfastM ∧
      (Rel.ordered, Obj.breakfast) ∉ strongAllowed orderedM breakfastM ∧
      (Rel.ordered, Obj.lunch) ∉ strongAllowed orderedM breakfastM := by
  rw [reversal_allows_exactly_default_bans, weakBanned_eq]
  refine ⟨rfl, by decide, by decide⟩

/-- The licensed focal targets of default *ordered BREAKfast* are all the VP meanings the daughters
compose except the banned one — "all VP meanings, except those that are relations to breakfast
other than ordering breakfast". The licensed set is the focus value the prosody derives, which the
squiggle consumes at propositional type. -/
theorem licensed_eq :
    licensedFocusValue orderedM breakfastM =
      {p : Rel × Obj | p ≠ (Rel.paidFor, Obj.breakfast)} := by
  ext ⟨r, o⟩
  rw [licensedFocusValue, weakBanned_eq]
  simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_ofPred_eq, Set.mem_seq_iff,
    Set.mem_insert_iff, orderedM, breakfastM]
  constructor
  · rintro ⟨-, hne⟩; exact hne
  · intro hne
    exact ⟨⟨vt r, by cases r <;> simp, o, by cases o <;> simp, rfl⟩, hne⟩

end Buring2015
