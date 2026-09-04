/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Linearization.Replay
import Linglib.Syntax.Minimalist.SyntacticObject.Subterm

/-!
# Binding at a stage of the derivation

Movement reorders c-command, and binding may be evaluated before or after it: reconstruction.
`CCommandsAt d n x y` says that `x` c-commands `y` in the object the replay of `d` reaches after
`n` steps, which by faithfulness is `d.stageAt n` itself, so the predicate decides a fact about
the unordered syntactic object; a stage whose replay fails c-commands nothing. `BindsAtSurface`
evaluates binding at the last stage and `BindsAtSomeStage` at any, the derivational binding
condition under which a sentence is well formed as soon as some stage satisfies it
([cole-hermon-2008], fn. 28), reconstruction to any position the mover passed through. Binding
at some stage is monotone under extending the derivation; binding at the surface is not.

## Main definitions

* `Minimalist.SyntacticObject.Derivation.CCommandsAt`, `BindsAtSurface`, `BindsAtSomeStage`

## Main results

* `Minimalist.SyntacticObject.Derivation.CCommandsAt.cCommandsIn_stageAt`: the predicate speaks
  of the derivation's own stage.
* `Minimalist.SyntacticObject.Derivation.cCommandsAt_append_of_le`, `BindsAtSomeStage.append`.

## References

* [cole-hermon-2008]
-/

namespace Minimalist.SyntacticObject.Derivation

variable {d : Derivation} {steps : List Step} {n : Nat} {x y : SyntacticObject}

/-- `x` c-commands `y` at stage `n` of `d`: in the ordered object the replay reaches after `n`
steps. -/
def CCommandsAt (d : Derivation) (n : Nat) (x y : SyntacticObject) : Prop :=
  ∃ p ∈ (d.take n).externalize?, cCommandsIn p x y

instance (d : Derivation) (n : Nat) (x y : SyntacticObject) :
    Decidable (d.CCommandsAt n x y) := by
  unfold CCommandsAt; infer_instance

/-- The stage the predicate looks at is the derivation's own. -/
theorem CCommandsAt.cCommandsIn_stageAt (h : d.CCommandsAt n x y) :
    cCommandsIn (d.stageAt n) x y :=
  let ⟨_, hp, hc⟩ := h
  d.externalize?_take_faithful n hp ▸ hc

/-- The early stages of an extended derivation are the original's. -/
theorem cCommandsAt_append_of_le (h : n ≤ d.length) :
    (d.append steps).CCommandsAt n x y ↔ d.CCommandsAt n x y := by
  rw [CCommandsAt, CCommandsAt, take_append_of_le h]

/-- Surface binding: c-command at the last stage. -/
abbrev BindsAtSurface (d : Derivation) (x y : SyntacticObject) : Prop :=
  d.CCommandsAt d.length x y

/-- Derivational binding: c-command at some stage. -/
def BindsAtSomeStage (d : Derivation) (x y : SyntacticObject) : Prop :=
  ∃ n ≤ d.length, d.CCommandsAt n x y

instance (d : Derivation) (x y : SyntacticObject) : Decidable (d.BindsAtSomeStage x y) := by
  unfold BindsAtSomeStage; infer_instance

/-- Binding at the surface is binding at some stage. -/
theorem BindsAtSurface.bindsAtSomeStage (h : d.BindsAtSurface x y) : d.BindsAtSomeStage x y :=
  ⟨d.length, le_rfl, h⟩

/-- Binding at some stage is monotone under extension. -/
theorem BindsAtSomeStage.append (h : d.BindsAtSomeStage x y) :
    (d.append steps).BindsAtSomeStage x y :=
  let ⟨n, hn, hc⟩ := h
  ⟨n, by rw [length_append]; exact hn.trans (Nat.le_add_right _ _),
    (cCommandsAt_append_of_le hn).2 hc⟩

end Minimalist.SyntacticObject.Derivation
