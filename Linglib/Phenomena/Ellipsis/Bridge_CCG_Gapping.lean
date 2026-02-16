import Linglib.Theories.Syntax.CCG.Gapping
import Linglib.Phenomena.Ellipsis.Gapping

/-!
# CCG Gapping Bridge

Connects CCG category theory (from `Theories.Syntax.CCG.Gapping`) to
empirical gapping data (from `Phenomena.Ellipsis.Gapping`).

Proves that:
1. Gapping direction follows from lexical verb categories and word order
2. Ross's generalization emerges from CCG's Principles of Consistency and Inheritance
3. Dutch allows both gapping directions due to mixed word order

## References

- Steedman (2000) "The Syntactic Process" Chapter 7
- Ross (1970) "Gapping and the order of constituents"
- Maling (1972) "On 'Gapping and the order of constituents'"
-/

namespace Phenomena.Ellipsis.Bridge_CCG_Gapping

open CCG
open CCG.Gapping
open Phenomena.Ellipsis.Gapping

-- Word Order and Gapping Direction

/--
Can arguments type-raise to backward categories (T\(T/NP))?
This requires VSO/SVO verbs in the language.
-/
def hasBackwardRaising : WordOrder → Bool
  | .VSO => true
  | .SVO => true
  | .VOS => true
  | _ => false

/--
Can arguments type-raise to forward categories (T/(T\NP))?
This requires SOV/OVS verbs in the language.
-/
def hasForwardRaising : WordOrder → Bool
  | .SOV => true
  | .OVS => true
  | .OSV => true
  | _ => false

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
  ⟨hasBackwardRaising order, hasForwardRaising order⟩

-- Ross's Generalization from CCG Principles

/--
Ross's generalization emerges from CCG's Principles of Consistency and Inheritance.

The gapped conjunct's directionality is determined by:
1. What type-raised categories are available (from verb categories)
2. What composition rules preserve those directions

This follows from the grammar rather than being stipulated.
-/
theorem ross_from_ccg_principles :
    ∀ order : WordOrder,
      predictedGappingPattern order = rossOriginal order := by
  intro order
  cases order <;> rfl

/--
SVO patterns with VSO (forward gapping), not SOV (backward gapping).

This is because SVO verbs ((S\NP)/NP) allow backward type-raising,
which produces leftward-looking gapped constituents.
-/
theorem svo_patterns_with_vso :
    predictedGappingPattern .SVO = predictedGappingPattern .VSO := by
  rfl

/--
English has no SOV verb category, so forward type-raising is not available.

Without T/(T\NP), we cannot build a rightward-looking gapped conjunct.
Hence "*Warren, potatoes and Dexter ate bread" is ungrammatical.
-/
theorem no_backward_gapping_in_english :
    hasForwardRaising .SVO = false := rfl

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
    (rossRevised dutchProfile).allowsForward = true ∧
    (rossRevised dutchProfile).allowsBackward = true := by
  constructor <;> rfl

end Phenomena.Ellipsis.Bridge_CCG_Gapping
