/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.SyntacticObject.Derivation
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm

/-!
# Freezing

A constituent a derivation has moved is an island for later extraction, the freezing effect that
descends from [ross-1967]'s Sentential Subject Constraint and that [chung-2006] makes the test
of VP-raising analyses of VOS order: whatever a raised VP still contains cannot be extracted,
whatever left it before it raised can. `Frozen d x` says that `x` sits inside some mover of `d`.
Movers carry the traces of what evacuated them earlier, not the evacuees, so an evacuee is not
frozen by the constituent it left; and a mover is itself available to move again. Freezing is
monotone under extending the derivation and blind to the sides of External Merge.

## Main definitions

* `Minimalist.SyntacticObject.Derivation.Frozen`

## Main results

* `Minimalist.SyntacticObject.Derivation.frozen_append_iff`: extending a derivation freezes
  what its new movers contain and nothing else.
* `Minimalist.SyntacticObject.Derivation.Frozen.append`, `frozen_leftward_iff`.

## References

* [ross-1967]
* [chung-2006]
-/

namespace Minimalist.SyntacticObject.Derivation

variable {d : Derivation} {steps : List Step} {x : SyntacticObject}

/-- `x` sits inside a constituent `d` has moved. -/
def Frozen (d : Derivation) (x : SyntacticObject) : Prop := ∃ m ∈ d.movedItems, contains m x

instance (d : Derivation) (x : SyntacticObject) : Decidable (d.Frozen x) := by
  unfold Frozen; infer_instance

/-- Extending a derivation freezes what its new movers contain and nothing else. -/
theorem frozen_append_iff :
    (d.append steps).Frozen x ↔
      d.Frozen x ∨ ∃ m ∈ steps.filterMap Step.mover?, contains m x := by
  simp [Frozen, movedItems_append, or_and_right, exists_or]

/-- Freezing is monotone under extension. -/
theorem Frozen.append (h : d.Frozen x) : (d.append steps).Frozen x :=
  frozen_append_iff.2 (Or.inl h)

/-- Freezing is blind to the sides of External Merge. -/
@[simp] theorem frozen_leftward_iff : d.leftward.Frozen x ↔ d.Frozen x := by
  unfold Frozen; rw [movedItems_leftward]

end Minimalist.SyntacticObject.Derivation
