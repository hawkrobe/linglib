module

public import Linglib.Semantics.Tense.Compositional
public import Linglib.Semantics.Tense.Perspective
public import Linglib.Logic.Modal.Basic

/-!
# Quantificational tense

Read quantificationally, a tense quantifies over the times its cell admits: the past holds of a
predicate at a time when the predicate holds at some earlier time, as in the tense logic of
Prior. Each comparison cell of `Semantics/Tense/Defs.lean` has an accessibility relation, which
relates a time to the times standing to it in one of the cell's positions, and the quantificational
tense of the cell is possibility `◇` along it, so the laws of `Logic/Modal` apply. The relation
is given on points and on intervals, where positions are those of `Perspective.Presup`.

A referential tense, a pronoun whose time the context supplies (`Tense.constrain`), is the
quantificational tense restricted to that one time; Ogihara reconciles the two analyses in this
way.

## Main definitions

* `Tense.accessibility`: the relation of a cell on points.
* `Tense.Perspective.accessibility`: the relation of a cell on intervals.

## Main statements

* `Tense.diamond_accessibility_past`: the quantificational past holds when the predicate held at
  some earlier time.
* `Tense.diamond_accessibility_present`: the quantificational present is the identity.
* `Tense.diamond_diamond_accessibility`: a quantificational tense under another is the
  quantificational tense of the composed cell.
* `Tense.diamond_accessibility_eq_and`: restricted to one time, the quantificational tense is the
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

/-- The accessibility relation of a cell relates a time to the times standing to it in one of
the cell's positions. -/
def accessibility (C : Finset Ordering) : SetRel T T := {p | compare p.2 p.1 ∈ C}

@[simp] theorem mem_accessibility : t ~[accessibility C] t' ↔ compare t' t ∈ C := .rfl

instance : Decidable (t ~[accessibility C] t') := inferInstanceAs (Decidable (compare t' t ∈ C))

@[simp] theorem diamond_accessibility_past : ◇[accessibility ⟦past⟧] P t ↔ ∃ t' < t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_accessibility_future :
    ◇[accessibility ⟦future⟧] P t ↔ ∃ t' > t, P t' := by
  simp [Diamond]

@[simp] theorem diamond_accessibility_present (P : T → Prop) :
    ◇[accessibility ⟦present⟧] P = P :=
  funext fun _ ↦ propext (by simp [Diamond])

theorem accessibility_comp_subset (C D : Finset Ordering) :
    accessibility C ○ accessibility D ⊆ (accessibility (comp D C) : SetRel T T) :=
  fun _ ⟨_, h₁, h₂⟩ ↦ compare_mem_comp h₂ h₁

/-- A quantificational tense under another is the quantificational tense of the composed cell. -/
theorem diamond_diamond_accessibility (h : ◇[accessibility C] (◇[accessibility D] P) t) :
    ◇[accessibility (comp D C)] P t :=
  diamond_restrict P (accessibility_comp_subset C D) t ((congrFun (diamond_comp _ _ P) t).mpr h)

/-- Restricted to the time `r`, the quantificational tense of a cell is its referential tense. -/
theorem diamond_accessibility_eq_and {W : Type*} (P : Reference.Index W T → Prop) (w : W)
    (r t : T) : ◇[accessibility C] (fun t' ↦ t' = r ∧ P (w, t')) t ↔ constrain C P (w, r) (w, t) :=
  ⟨fun ⟨_, hv, e, hP⟩ ↦ e ▸ ⟨hv, hP⟩, fun ⟨hv, hP⟩ ↦ ⟨r, hv, rfl, hP⟩⟩

namespace Perspective

variable {π r : NonemptyInterval T} {Q : NonemptyInterval T → Prop}

/-- The accessibility relation of a cell on intervals relates a perspective to the intervals
standing to it in one of the cell's positions. -/
def accessibility (C : Finset Ordering) : SetRel (NonemptyInterval T) (NonemptyInterval T) :=
  {p | Presup C p.1 p.2}

@[simp] theorem mem_accessibility : π ~[accessibility C] r ↔ Presup C π r := .rfl

instance : Decidable (π ~[accessibility C] r) := inferInstanceAs (Decidable (Presup C π r))

@[simp] theorem diamond_accessibility_past :
    ◇[accessibility ⟦past⟧] Q π ↔ ∃ r, r.precedes π ∧ Q r := by
  simp [Diamond]

/-- On point intervals the relation of a cell is its relation on points. -/
theorem pure_mem_accessibility {p t : T} :
    .pure p ~[accessibility C] .pure t ↔ p ~[Tense.accessibility C] t := by
  simp

end Perspective

end Tense
