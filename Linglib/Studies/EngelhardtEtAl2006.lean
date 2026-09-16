import Linglib.Data.Examples.EngelhardtEtAl2006
import Linglib.Pragmatics.GriceanMaxims
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# Engelhardt et al. (2006): Do Speakers and Listeners Observe the Gricean Maxim of Quantity?

This file formalizes [engelhardt-etal-2006]'s reading of the Maxim of Quantity of [grice-1975]
for referring expressions over a visual world. A description under-describes when it does not
let the addressee identify the intended referent, and over-describes when it carries a modifier
that identification does not require: with one apple in the display *the apple* suffices and
*the apple on the towel* over-describes it, while with two apples *the apple* under-describes.
The instructions of Table 1 cross a prepositional-phrase modifier on the target with a
destination that matches the target's current location or differs from it, and their status
follows. Over the one-referent display, (4) is concise, (5) and (6) over-describe the target,
and (3) under-describes the destination, since the apple already rests on a towel and only *the
other towel* singles out the empty one; over the two-referent display the modifier of (6) is
required. The three experiments ask whether speakers and listeners observe the maxim. The ten
speakers of Experiment 1 modified the target on 98% of two-referent trials and almost always
modified a matching destination, but modified the target on 30% of one-referent trials. The
twenty-two listeners of Experiment 2 rated (3) lowest of the four instructions and the bare
target of the two-referent display far below the modified one, and once the destination was
modified throughout rated over-descriptions no worse than concise instructions. In the visual
world of Experiment 3, listeners hearing (6) over the one-referent display fixated the empty
towel at *on the towel* and reached the box later than with (4), the pattern of
[tanenhaus-etal-1995] and [spivey-etal-2002], and hearing (3) or (5) kept fixating the apple.
Under-descriptions are avoided and penalized; over-descriptions are produced, as in
[deutsch-pechmann-1982], tolerated in judgment, and still cost the listener. The paper takes
the looks to the empty towel to show an initial location parse of *on the towel* that the
pragmatics of the instruction cannot drive, since speakers never produce (3) in that context,
and attributes it to Minimal Attachment or to the saturation of *put*'s location argument
rather than to the Referential Model; the over-descriptions it attributes to the speaker's
representation of the apple as an apple on a towel, which a concise description would have to
edit away.

## Implementation notes

* A display is five objects, each a kind with the object it rests on; the towel under the apple
  is an object, so that *the towel* is ambiguous between it and the empty towel and *the other
  towel* excludes it. The displays are the paper's running example, an apple on a towel, a frog
  or a second apple, an empty towel and an empty box.
* Identification and the two Quantity violations are `Pragmatics.GriceanMaxims` over the
  extension of a description in a display, against every other object. The paper's order on
  descriptions puts a bare noun below its modified forms and nothing else, so the second
  submaxim measures a modified description against its bare noun alone, the paper's one
  contrast. Production rates, ratings and fixation proportions stay in the prose above.
* The examples are `Data.Examples.EngelhardtEtAl2006`.

## References

* [engelhardt-etal-2006]
* [grice-1975]
* [tanenhaus-etal-1995]
* [spivey-etal-2002]
* [deutsch-pechmann-1982]
-/

namespace EngelhardtEtAl2006

open Pragmatics.GriceanMaxims Data.Examples EngelhardtEtAl2006.Examples

/-- The kinds of object of the running example (Table 2): the apple to be moved, the frog, and
the two kinds of destination. -/
inductive Kind
  | apple
  | frog
  | towel
  | box
  deriving DecidableEq, Repr, Fintype

/-- An object of a display: its kind and the object it rests on or in, if any. -/
structure Object where
  kind : Kind
  support : Option (Fin 5) := none
  deriving DecidableEq, Repr

/-- A display of five objects, the target first and the object it rests on second. -/
abbrev Display := Fin 5 → Object

/-- The one-referent display, Fig. 2A: an apple on a towel, a frog, an empty towel, an empty
box. -/
def oneReferent : Display := ![⟨.apple, some 1⟩, ⟨.towel, none⟩, ⟨.frog, none⟩, ⟨.towel, none⟩,
  ⟨.box, none⟩]

/-- The two-referent display of Experiment 1, Fig. 1B with one apple by itself: an apple on a
towel, a second apple, an empty towel, an empty box. -/
def twoReferent : Display := ![⟨.apple, some 1⟩, ⟨.towel, none⟩, ⟨.apple, none⟩, ⟨.towel, none⟩,
  ⟨.box, none⟩]

/-! ### Descriptions and the maxim -/

/-- A referring expression of the instructions: a bare noun, a noun with a prepositional-phrase
modifier naming what the referent rests on, or *the other* noun, which excludes the object the
target rests on. -/
inductive Description
  | bare (k : Kind)
  | on (k loc : Kind)
  | other (k : Kind)
  deriving DecidableEq, Repr, Fintype

namespace Description

/-- The noun of a description. -/
def kind : Description → Kind
  | .bare k | .on k _ | .other k => k

/-- The bare noun a description is measured against. -/
def bareOf (d : Description) : Description := .bare d.kind

@[simp] theorem bareOf_bareOf (d : Description) : d.bareOf.bareOf = d.bareOf := rfl

/-- The paper's order on descriptions: a bare noun is below its modified forms and nothing
else is comparable. -/
instance : Preorder Description where
  le d₁ d₂ := d₁ = d₂ ∨ d₁ = d₂.bareOf
  le_refl _ := .inl rfl
  le_trans := by rintro _ _ _ (rfl | rfl) (rfl | rfl) <;> simp

instance : DecidableLE Description :=
  fun d₁ d₂ ↦ inferInstanceAs (Decidable (d₁ = d₂ ∨ d₁ = d₂.bareOf))

theorem lt_iff {d' d : Description} : d' < d ↔ d' = d.bareOf ∧ d ≠ d.bareOf := by
  simp only [lt_iff_le_not_ge]
  change (d' = d ∨ d' = d.bareOf) ∧ ¬ (d = d' ∨ d = d'.bareOf) ↔ _
  constructor
  · rintro ⟨rfl | rfl, h⟩
    · exact absurd (.inl rfl) h
    · exact ⟨rfl, fun h' ↦ h (.inl h')⟩
  · rintro ⟨rfl, h⟩
    exact ⟨.inr rfl, fun h' ↦ h (h'.elim id fun h' ↦ h'.trans (bareOf_bareOf _))⟩

end Description

/-- The objects a description holds of in a display, *other* read relative to the target
`t`. -/
def extension (D : Display) (t : Fin 5) : Description → Set (Fin 5)
  | .bare k => {i | (D i).kind = k}
  | .on k loc => {i | (D i).kind = k ∧ ∃ j, (D i).support = some j ∧ (D j).kind = loc}
  | .other k => {i | (D i).kind = k ∧ (D t).support ≠ some i}

instance (D : Display) (t : Fin 5) (d : Description) : DecidablePred (· ∈ extension D t d) :=
  fun _ ↦ by cases d <;> unfold extension <;> infer_instance

/-- The description lets the addressee identify the intended referent `r` against every other
object of the display. -/
abbrev Identifies (D : Display) (t r : Fin 5) (d : Description) : Prop :=
  Distinguishes (extension D t) (Finset.univ.erase r) r d

/-- The Quantity violation of a description of `r`, if any: an under-description does not
identify `r`, and an over-description identifies it with a modifier its bare noun does not
need. -/
abbrev violation (D : Display) (t r : Fin 5) (d : Description) : Option QuantityViolation :=
  quantityViolation (extension D t) (Finset.univ.erase r) r d

/-- A modified description that identifies its referent over-describes it exactly when the bare
noun already identifies it. -/
theorem violation_eq_over_iff {D : Display} {t r : Fin 5} {d : Description}
    (hd : Identifies D t r d) (hb : d ≠ d.bareOf) :
    violation D t r d = some .overInformative ↔ Identifies D t r d.bareOf := by
  simp [violation, quantityViolation_eq_over_iff, Description.lt_iff, hd, hb]

/-- With one apple, *the apple* identifies it and *the apple on the towel* over-describes it. -/
theorem oneReferent_target :
    violation oneReferent 0 0 (.bare .apple) = none ∧
      violation oneReferent 0 0 (.on .apple .towel) = some .overInformative := by
  decide

/-- With two apples, *the apple* under-describes and the modifier is required. -/
theorem twoReferent_target :
    violation twoReferent 0 0 (.bare .apple) = some .underInformative ∧
      violation twoReferent 0 0 (.on .apple .towel) = none := by
  decide

/-- The destinations: *the towel* under-describes the empty towel in either display, as the
apple already rests on a towel, *the other towel* identifies it, and *the box* is identified
bare. -/
theorem destinations :
    ∀ D ∈ [oneReferent, twoReferent],
      violation D 0 3 (.bare .towel) = some .underInformative ∧
        violation D 0 3 (.other .towel) = none ∧ violation D 0 4 (.bare .box) = none := by
  decide

/-! ### The instructions of Table 1 -/

/-- An instruction, *Put the apple … in/on the …*: the target description and the destination
description. -/
structure Instruction where
  target : Description
  destination : Description
  deriving DecidableEq, Repr

/-- The target descriptions as named in the rows. -/
def targetTable : List (String × Description) :=
  [("bare", .bare .apple), ("modified", .on .apple .towel)]

/-- The destination descriptions as named in the rows. -/
def destinationTable : List (String × Description) :=
  [("towel", .bare .towel), ("otherTowel", .other .towel), ("box", .bare .box)]

/-- An instruction from a row of Table 1. -/
def Instruction.ofExample (ex : LinguisticExample) : Option Instruction := do
  pure ⟨← ex.parse? "target" targetTable, ← ex.parse? "destination" destinationTable⟩

theorem ofExample_isSome :
    ∀ ex ∈ Examples.all, (ex.feature? "target").isSome → (Instruction.ofExample ex).isSome := by
  decide

/-- The four instructions (3)–(6). -/
def instructions : List Instruction := Examples.all.filterMap Instruction.ofExample

/-- The destination matches the target's current location, a towel. -/
def Instruction.Matching (ins : Instruction) : Prop := ins.destination.kind = .towel

/-- The intended destination in either display: the empty towel or the box. -/
def Instruction.goal (ins : Instruction) : Fin 5 := if ins.destination.kind = .towel then 3 else 4

/-- The Quantity violations of an instruction over a display, of its target and of its
destination. -/
def Instruction.violations (D : Display) (ins : Instruction) :
    Option QuantityViolation × Option QuantityViolation :=
  (violation D 0 0 ins.target, violation D 0 ins.goal ins.destination)

/-- Over the one-referent display, the modified target of (5) and (6) is an over-description and
the bare destination of (3) an under-description; (4) is concise. -/
theorem instructions_oneReferent :
    ∀ ins ∈ instructions,
      ins.violations oneReferent =
        (if ins.target = .bare .apple then none else some .overInformative,
          if ins.destination = .bare .towel then some .underInformative else none) := by
  decide

/-- Over the two-referent display, the bare target of (3) and (4) is an under-description and
the modifier of (5) and (6) is required. -/
theorem instructions_twoReferent :
    ∀ ins ∈ instructions,
      ins.violations twoReferent =
        (if ins.target = .bare .apple then some .underInformative else none,
          if ins.destination = .bare .towel then some .underInformative else none) := by
  decide

end EngelhardtEtAl2006
