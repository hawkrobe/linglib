/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Prod
import Linglib.Semantics.Modality.Kratzer.Operators

/-!
# Kratzer (1981): The Notional Category of Modality

This file formalizes the paper's practical-inference example, on the modal base and ordering
source semantics of `Modality.Kratzer.Operators`. Someone wants two things, to become mayor
and to avoid the pub, while the circumstances are such that they become mayor only if they go
to the pub. The circumstances supply the modal base and the desires the ordering source, and
the two ideals pull apart: a world where the speaker goes to the pub and becomes mayor and one
where they stay home and do not are incomparable, so the ordering is not connected. Of the
five conclusions the paper considers, the three necessities and impossibilities (that the
speaker should go to the pub, should avoid it, and could become mayor without it) fail, while
the two possibilities (that they could go and could avoid going) hold, under the paper's
limit-free necessity and its dual possibility.

## Implementation notes

The worlds are the four combinations of becoming mayor and going to the pub, so every claim
is decided once the modal base, the ordering source, and the operators are unfolded. The
example also fixes the reading of `bestWorlds`: the world that is at least as good as every
accessible world does not exist here, so the minimality reading, on which the best worlds are
the two ideal-realizing ones, is the one that agrees with the limit-free operators.

## References

* [kratzer-1981]
* [kratzer-2012] — Chapter 2, the revised version of the paper
-/

namespace Kratzer1981

open Modality.Kratzer

/-- A world: does the speaker become mayor, and go to the pub regularly? -/
abbrev World := Bool × Bool

/-- The evaluation world, arbitrary since the backgrounds are constant. -/
def w₀ : World := (false, false)

/-- The relevant circumstances: the speaker becomes mayor only by going to the pub. -/
def circumstances : ModalBase World := Function.const World [λ w => w.1 = true → w.2 = true]

/-- What the speaker wants: to become mayor, and to avoid the pub. -/
def desires : OrderingSource World :=
  Function.const World [λ w => w.1 = true, λ w => w.2 = false]

/-- Decide a claim about the backgrounds and the ordering over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| (simp only [accessibleWorlds, propIntersection, atLeastAsGoodAs_iff, circumstances,
      desires, Function.const_apply, Set.mem_ofPred_eq, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true]; decide))

/-- The paper's clause (c): the world of going to the pub and becoming mayor and the world of
staying home are incomparable, so the ordering is not connected. -/
theorem mayor_pub_incomparable :
    ¬ atLeastAsGoodAs (desires w₀) (true, true) (false, false) ∧
      ¬ atLeastAsGoodAs (desires w₀) (false, false) (true, true) := by
  decide_worlds

/-- Clause (f): the accessible world where the speaker goes to the pub and still fails to
become mayor is strictly worse than either ideal-realizing world. -/
theorem pub_no_mayor_worst :
    ∀ v ∈ ({(true, true), (false, false)} : Set World),
      atLeastAsGoodAs (desires w₀) v (false, true) ∧
        ¬ atLeastAsGoodAs (desires w₀) (false, true) v := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  decide_worlds

/-- No accessible world is at least as good as every accessible world: on the dominance
reading of "best" the example would have no best world at all. -/
theorem no_dominant_world :
    ¬ ∃ w ∈ accessibleWorlds circumstances w₀,
      ∀ v ∈ accessibleWorlds circumstances w₀, atLeastAsGoodAs (desires w₀) w v := by
  decide_worlds

/-- The best worlds are the two ideal-realizing ones. -/
theorem mem_bestWorlds_iff (w : World) :
    w ∈ bestWorlds circumstances desires w₀ ↔ w = (true, true) ∨ w = (false, false) := by
  revert w
  simp only [bestWorlds, Core.Order.Normality.mem_optimal, kratzerNormality,
    Core.Order.Normality.fromProps, Preorder.ofCriteria_le_iff]
  decide_worlds

/-- The example satisfies the Limit Assumption, so the paper's limit-free operators are
quantification over `bestWorlds`. -/
theorem limitAssumption : LimitAssumption circumstances desires w₀ := by
  simp only [LimitAssumption, mem_bestWorlds_iff]
  decide_worlds

/-- Decide a verdict of the limit-free operators through the best worlds. -/
scoped macro "decide_verdict" : tactic =>
  `(tactic| (simp only [humanPossibility, humanNecessity_iff_necessity limitAssumption,
      necessity, ModalLogic.box, kratzerBestR, mem_bestWorlds_iff, forall_eq_or_imp,
      forall_eq]; decide))

/-- Conclusion one fails: the speaker need not go to the pub. -/
theorem not_must_pub : ¬ humanNecessity circumstances desires (·.2 = true) w₀ := by
  decide_verdict

/-- Conclusion two fails: the speaker need not avoid the pub. -/
theorem not_must_avoid : ¬ humanNecessity circumstances desires (·.2 = false) w₀ := by
  decide_verdict

/-- Conclusion three fails: becoming mayor without the pub is not even accessible, and wishes
cannot override facts. -/
theorem not_can_mayor_without_pub :
    ¬ humanPossibility circumstances desires (λ w => w.1 = true ∧ w.2 = false) w₀ := by
  decide_verdict

/-- Conclusion four holds: the speaker could go to the pub. -/
theorem can_pub : humanPossibility circumstances desires (·.2 = true) w₀ := by
  decide_verdict

/-- Conclusion five holds: the speaker could avoid the pub. -/
theorem can_avoid : humanPossibility circumstances desires (·.2 = false) w₀ := by
  decide_verdict

end Kratzer1981
