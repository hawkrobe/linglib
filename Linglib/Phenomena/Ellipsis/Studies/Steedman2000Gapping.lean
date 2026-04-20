import Linglib.Theories.Syntax.CCG.Gapping
import Linglib.Phenomena.Ellipsis.Gapping

/-!
# CCG Gapping Bridge
@cite{ross-1970} @cite{steedman-2000}

Connects CCG category theory (from `Theories.Syntax.CCG.Gapping`) to
empirical gapping data (from `Phenomena.Ellipsis.Gapping`).

Proves that:
1. Gapping direction follows from lexical verb categories and word order
2. Ross's generalization emerges from CCG's Principles of Consistency and Inheritance
3. Dutch allows both gapping directions due to mixed word order

-/

namespace Phenomena.Ellipsis.CCG_GappingBridge

open CCG
open CCG.Gapping
open Phenomena.Ellipsis.Gapping

-- Word Order and Gapping Direction

/--
Can arguments type-raise to backward categories (T\(T/NP))?
This requires VSO/SVO verbs in the language.
-/
def HasBackwardRaising : WordOrder → Prop
  | .VSO => True
  | .SVO => True
  | .VOS => True
  | _ => False

instance : DecidablePred HasBackwardRaising := fun w => by
  cases w <;> unfold HasBackwardRaising <;> infer_instance

/--
Can arguments type-raise to forward categories (T/(T\NP))?
This requires SOV/OVS verbs in the language.
-/
def HasForwardRaising : WordOrder → Prop
  | .SOV => True
  | .OVS => True
  | .OSV => True
  | _ => False

instance : DecidablePred HasForwardRaising := fun w => by
  cases w <;> unfold HasForwardRaising <;> infer_instance

/--
Gapping direction follows from available type-raised categories.

Forward gapping: gapped conjunct is leftward-looking (needs verb to left)
  -> requires backward type-raising (T\(T/NP))
  -> requires VSO/SVO verbs

Backward gapping: gapped conjunct is rightward-looking (needs verb to right)
  -> requires forward type-raising (T/(T\NP))
  -> requires SOV verbs
-/
def predictedGappingPattern (order : WordOrder) : GappingPattern :=
  ⟨HasBackwardRaising order, HasForwardRaising order⟩

-- Ross's Generalization from CCG Principles

/--
Ross's generalization emerges from CCG's Principles of Consistency and Inheritance:
the predicted pattern allows the same directions as Ross's original generalization.
-/
theorem ross_from_ccg_principles :
    ∀ order : WordOrder,
      ((predictedGappingPattern order).allowsForward ↔
        (rossOriginal order).allowsForward) ∧
      ((predictedGappingPattern order).allowsBackward ↔
        (rossOriginal order).allowsBackward) := by
  intro order
  cases order <;>
    refine ⟨?_, ?_⟩ <;>
    simp [predictedGappingPattern, rossOriginal, HasBackwardRaising,
          HasForwardRaising, GappingPattern.forwardOnly,
          GappingPattern.backwardOnly]

/--
SVO patterns with VSO (forward gapping), not SOV (backward gapping):
both license forward but not backward.
-/
theorem svo_patterns_with_vso :
    ((predictedGappingPattern .SVO).allowsForward ↔
      (predictedGappingPattern .VSO).allowsForward) ∧
    ((predictedGappingPattern .SVO).allowsBackward ↔
      (predictedGappingPattern .VSO).allowsBackward) := by
  refine ⟨?_, ?_⟩ <;>
    simp [predictedGappingPattern, HasBackwardRaising, HasForwardRaising]

/--
English has no SOV verb category, so forward type-raising is not available.

Without T/(T\NP), we cannot build a rightward-looking gapped conjunct.
Hence "*Warren, potatoes and Dexter ate bread" is ungrammatical.
-/
theorem no_backward_gapping_in_english :
    ¬ HasForwardRaising .SVO := id

-- Dutch: Both Directions

/--
Dutch has both VSO main verbs and SOV subordinate verbs.
Therefore, Dutch licenses both type-raising directions.
-/
def dutchProfile : WordOrderProfile := dutch

/--
Dutch allows both forward and backward gapping.
-/
theorem dutch_allows_both_gapping :
    (rossRevised dutchProfile).allowsForward ∧
    (rossRevised dutchProfile).allowsBackward := by
  refine ⟨trivial, ?_⟩
  exact Or.inr trivial

end Phenomena.Ellipsis.CCG_GappingBridge
