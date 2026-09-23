module

public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Semantics.Mood.Defs
public import Linglib.Discourse.CommonGround

/-!
# Indicative conditionals in a context

This file defines the contextual constraint of [stalnaker-1975] on selection functions. The
indicative and the subjunctive conditional share the truth condition of the selection
conditional, and an indicative requires its selection function to stay inside the context set
whenever the antecedent is compatible with it, a requirement the subjunctive suspends. Within a
context meeting the constraint the indicative conditional holds wherever the material conditional
holds throughout the context, without being identified with it.

## Main definitions

* `pragmaticConstraint`: the selection function stays in the context set when it can.
* `SelectionFunction.restrict`: a selection function restricted to a context.
* `Mood.admissibleSelection`: the selection functions each mood admits.

## References

* [R. C. Stalnaker, *Indicative conditionals* (1975)][stalnaker-1975]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [R. C. Stalnaker, *A Defense of Conditional Excluded Middle* (1981)][stalnaker-1981]
-/

@[expose] public section


namespace Conditional

open Mood (Grammatical)
open _root_.Conditional (SelectionFunction selectionPrefers)

/-! ### The pragmatic constraint -/

/-- The pragmatic constraint of [stalnaker-1975] on a selection function relative to a context set
`C`. At a world of `C`, an antecedent true somewhere in `C` selects a world of `C`, which
Stalnaker glosses as the worlds of the context set being closer to each other than to any world
outside it. -/
def pragmaticConstraint {W : Type*} (s : SelectionFunction W)
    (C : Set W) : Prop :=
  ∀ w (A : Set W), w ∈ C → (∃ w' ∈ A, w' ∈ C) → s.sel w A ∈ C

open Classical in
/-- The restriction of a selection function to a context, which at a context world selects among
the context's antecedent-worlds when there are any and otherwise selects as before. -/
noncomputable def SelectionFunction.restrict {W : Type*} (s : SelectionFunction W)
    (C : Set W) : SelectionFunction W where
  sel w A := if w ∈ C ∧ (A ∩ C).Nonempty then s.sel w (A ∩ C) else s.sel w A
  inclusion w A hA := by
    split_ifs with h
    · exact (s.inclusion w (A ∩ C) h.2).1
    · exact s.inclusion w A hA
  centering w A hw := by
    split_ifs with h
    · exact s.centering w (A ∩ C) ⟨hw, h.1⟩
    · exact s.centering w A hw

theorem SelectionFunction.restrict_sel_of_mem {W : Type*} (s : SelectionFunction W) (C : Set W)
    {w : W} {A : Set W} (hw : w ∈ C) (hA : (A ∩ C).Nonempty) :
    (s.restrict C).sel w A = s.sel w (A ∩ C) := by
  simp [SelectionFunction.restrict, hw, hA]

theorem SelectionFunction.restrict_sel_of_notMem {W : Type*} (s : SelectionFunction W)
    (C : Set W) {w : W} (A : Set W) (hw : w ∉ C) : (s.restrict C).sel w A = s.sel w A := by
  simp [SelectionFunction.restrict, hw]

/-- The restriction of a selection function to a context obeys the pragmatic constraint for
that context. -/
theorem pragmaticConstraint_restrict {W : Type*} (s : SelectionFunction W) (C : Set W) :
    pragmaticConstraint (s.restrict C) C := fun w A hw hA ↦ by
  have hAC : (A ∩ C).Nonempty := let ⟨v, hvA, hvC⟩ := hA; ⟨v, hvA, hvC⟩
  rw [SelectionFunction.restrict_sel_of_mem s C hw hAC]
  exact (s.inclusion w (A ∩ C) hAC).2

/-- The selection functions a mood admits in a context ([stalnaker-1975]). The indicative requires
the pragmatic constraint and the subjunctive suspends it, so the moods differ in the pairing of
selection function and context rather than in the truth condition. -/
def Mood.admissibleSelection {W : Type*} (m : Grammatical) (s : SelectionFunction W)
    (C : Set W) : Prop :=
  match m with
  | .indicative  => pragmaticConstraint s C
  | .subjunctive => True

/-- At a context world, for an antecedent compatible with the context and a selection function
meeting the pragmatic constraint, the selection conditional holds whenever the material
conditional holds throughout the context. This is one direction of the contextual equivalence
of indicative and material conditionals that [stalnaker-1975] §IV defends. -/
theorem mem_selectionConditional_of_forall_mem {W : Type*} (s : SelectionFunction W)
    {C p q : Set W} {w : W} (hw : w ∈ C) (hopen : ∃ w' ∈ p, w' ∈ C)
    (hC : pragmaticConstraint s C) (himp : ∀ w' ∈ C, w' ∈ p → w' ∈ q) :
    w ∈ selectionConditional s p q := by
  obtain ⟨v, hv, -⟩ := id hopen
  rw [mem_selectionConditional_of_nonempty s ⟨v, hv⟩]
  exact himp _ (hC w p hw hopen) (s.inclusion w p ⟨v, hv⟩)

end Conditional
