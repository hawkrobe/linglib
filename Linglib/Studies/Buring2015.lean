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
pattern restricts its focal targets — under the default weak–strong
pattern the Weak Restriction (his (1)) bans targets that vary the
weak daughter while the strong stays at its ordinary value; under
prosodic reversal the Strong Restriction (his (9)) allows only
targets varying the accented daughter non-trivially.

The worked example is his *ordered BREAKfast* vs *ORDERED breakfast*:
default stress bans exactly the verb-focus targets ('R breakfast')
and permits object and VP focus; reversal permits exactly the
non-trivial verb-focus targets. The rules live in
`Semantics/Focus/Unalternatives.lean`, shared with the
morphosyntactic extension of [assmann-etal-2023].
-/

namespace Buring2015

open Alternatives
open Semantics.Focus (weakBanned strongAllowed)

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
def orderedM : AltMeaning (Obj → Rel × Obj) :=
  ⟨vt .ordered, [vt .ordered, vt .paidFor]⟩

/-- *breakfast*, with its object alternatives. -/
def breakfastM : AltMeaning Obj := ⟨.breakfast, [.breakfast, .lunch]⟩

private theorem vt_ne : vt .paidFor ≠ vt .ordered := fun h => by
  have := congrFun h .breakfast
  exact absurd (congrArg Prod.fst this) (by decide)

/-- Default *ordered BREAKfast* bans the verb-focus target 'paid for
breakfast': it varies the weak daughter over given *breakfast*. -/
theorem default_bans_verb_focus :
    (Rel.paidFor, Obj.breakfast) ∈ weakBanned orderedM breakfastM :=
  ⟨vt .paidFor, List.Mem.tail _ (List.Mem.head _), .breakfast, rfl, rfl⟩

/-- Default *ordered BREAKfast* permits the object-focus target
'ordered lunch': no way to compose it holding *breakfast* fixed. -/
theorem default_permits_object_focus :
    (Rel.ordered, Obj.lunch) ∉ weakBanned orderedM breakfastM := by
  rintro ⟨f, hf, a, rfl, heq⟩
  rcases List.mem_cons.mp hf with rfl | hf'
  · exact absurd (congrArg Prod.snd heq) (by decide)
  rcases List.mem_cons.mp hf' with rfl | hf''
  · exact absurd (congrArg Prod.snd heq) (by decide)
  · exact nomatch hf''

/-- Reversed *ORDERED breakfast* allows the non-trivial verb-focus
target 'paid for breakfast'. -/
theorem reversal_allows_verb_focus :
    (Rel.paidFor, Obj.breakfast) ∈ strongAllowed orderedM breakfastM :=
  ⟨vt .paidFor, ⟨List.Mem.tail _ (List.Mem.head _), vt_ne⟩,
    .breakfast, rfl, rfl⟩

/-- Reversed *ORDERED breakfast* excludes the trivial target 'ordered
breakfast' itself: the accented daughter must vary. -/
theorem reversal_excludes_trivial :
    (Rel.ordered, Obj.breakfast) ∉ strongAllowed orderedM breakfastM := by
  rintro ⟨f, ⟨hf, hne⟩, a, rfl, heq⟩
  rcases List.mem_cons.mp hf with rfl | hf'
  · exact hne rfl
  rcases List.mem_cons.mp hf' with rfl | hf''
  · exact absurd (congrArg Prod.fst heq) (by decide)
  · exact nomatch hf''

/-- Reversal also excludes object-focus targets: only the accented
verb may vary. -/
theorem reversal_excludes_object_focus :
    (Rel.ordered, Obj.lunch) ∉ strongAllowed orderedM breakfastM := by
  rintro ⟨f, ⟨hf, _⟩, a, rfl, heq⟩
  rcases List.mem_cons.mp hf with rfl | hf'
  · exact absurd (congrArg Prod.snd heq) (by decide)
  rcases List.mem_cons.mp hf' with rfl | hf''
  · exact absurd (congrArg Prod.snd heq) (by decide)
  · exact nomatch hf''

end Buring2015
