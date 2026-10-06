module

public import Linglib.Semantics.Tense.Compositional
public import Linglib.Semantics.Tense.Perspective
public import Linglib.Logic.Modal.Basic

/-!
# Quantificational tense

Read quantificationally, a tense quantifies over the times its cell admits: the past holds of a
predicate at a time when the predicate holds at some earlier time, as in the tense logic of
Prior. Each comparison cell of `Semantics/Tense/Defs.lean` is read as a relation between times,
relating a time to the times standing to it in one of the cell's positions (`Tense.toSetRel`),
and the quantificational tense of the cell is possibility `◇` along it: `◇[toSetRel ⟦past⟧] P t`
says that `P` held at some time before `t`. The laws of `Logic/Modal` then apply. The relation
is given on points and on intervals, where positions are those of `Perspective.Presup`.

A referential tense, a pronoun whose time the context supplies (`Tense.constrain`), is the
quantificational tense restricted to that one time; Ogihara reconciles the two analyses in this
way.

## Main definitions

* `Tense.toSetRel`: a cell read as a relation between times.
* `Tense.Perspective.toSetRel`: a cell read as a relation between intervals.

## Main statements

* `Tense.diamond_toSetRel_past`: the quantificational past holds when the predicate held at
  some earlier time.
* `Tense.diamond_toSetRel_present`: the quantificational present is the identity.
* `Tense.diamond_diamond_toSetRel`: a quantificational tense under another is the
  quantificational tense of the composed cell.
* `Tense.diamond_toSetRel_eq_and`: restricted to one time, the quantificational tense is the
  referential tense.

## References

* [prior-1967]
* [partee-1973]
* [ogihara-1989]
-/

@[expose] public section

namespace Tense

open Semantics ModalLogic
open scoped SetRel

variable {T : Type*} [LinearOrder T] {C D : Finset Ordering} {P : T → Prop} {t t' : T}

/-- `toSetRel C` is the cell `C` read as a relation, relating a time to the times standing to it
in one of the cell's positions. -/
def toSetRel (C : Finset Ordering) : SetRel T T := {p | compare p.2 p.1 ∈ C}

@[simp] theorem mem_toSetRel : t ~[toSetRel C] t' ↔ compare t' t ∈ C := .rfl

instance : Decidable (t ~[toSetRel C] t') := inferInstanceAs (Decidable (compare t' t ∈ C))

@[simp] theorem diamond_toSetRel_past : ◇[toSetRel ⟦past⟧] P t ↔ ∃ t' < t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_future :
    ◇[toSetRel ⟦future⟧] P t ↔ ∃ t' > t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_toSetRel_present (P : T → Prop) :
    ◇[toSetRel ⟦present⟧] P = P :=
  funext fun _ ↦ propext (by simp [Diamond])

theorem toSetRel_comp_subset (C D : Finset Ordering) :
    toSetRel C ○ toSetRel D ⊆ (toSetRel (comp D C) : SetRel T T) :=
  fun _ ⟨_, h₁, h₂⟩ ↦ compare_mem_comp h₂ h₁

/-- A quantificational tense under another is the quantificational tense of the composed cell. -/
theorem diamond_diamond_toSetRel (h : ◇[toSetRel C] (◇[toSetRel D] P) t) :
    ◇[toSetRel (comp D C)] P t :=
  diamond_restrict P (toSetRel_comp_subset C D) t ((congrFun (diamond_comp _ _ P) t).mpr h)

/-- Restricted to the time `r`, the quantificational tense of a cell is its referential tense. -/
theorem diamond_toSetRel_eq_and {W : Type*} (P : Reference.Index W T → Prop) (w : W)
    (r t : T) : ◇[toSetRel C] (fun t' ↦ t' = r ∧ P (w, t')) t ↔ constrain C P (w, r) (w, t) :=
  ⟨fun ⟨_, hv, e, hP⟩ ↦ e ▸ ⟨hv, hP⟩, fun ⟨hv, hP⟩ ↦ ⟨r, hv, rfl, hP⟩⟩

namespace Perspective

variable {π r : NonemptyInterval T} {Q : NonemptyInterval T → Prop}

/-- `Perspective.toSetRel C` is the cell `C` read as a relation on intervals, relating a
perspective to the intervals standing to it in one of the cell's positions. -/
def toSetRel (C : Finset Ordering) : SetRel (NonemptyInterval T) (NonemptyInterval T) :=
  {p | Presup C p.1 p.2}

@[simp] theorem mem_toSetRel : π ~[toSetRel C] r ↔ Presup C π r := .rfl

instance : Decidable (π ~[toSetRel C] r) := inferInstanceAs (Decidable (Presup C π r))

@[simp] theorem diamond_toSetRel_past :
    ◇[toSetRel ⟦past⟧] Q π ↔ ∃ r, r.precedes π ∧ Q r := by
  simp [Diamond]

/-- On point intervals the relation of a cell is its relation on points. -/
theorem pure_mem_toSetRel {p t : T} :
    .pure p ~[toSetRel C] .pure t ↔ p ~[Tense.toSetRel C] t := by
  simp

end Perspective

end Tense
