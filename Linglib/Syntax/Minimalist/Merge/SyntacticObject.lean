/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.Minimalist.Merge.Internal
import Linglib.Syntax.Minimalist.Workspace.Basic

/-!
# Merge on the syntactic-object carrier

Merge on the carrier is the bare binary node `SyntacticObject.merge` with root label
`Sum.inr none`. This file identifies it with the algebraic Merge operator of `Merge/Basic.lean` on
workspaces lifted along `of'`: External Merge of two objects is `mergeOp_pair`, and Internal
Merge of a mover with its remainder is the two-stage composition `mergeOp_im_composition`, given
the unique Δ^ρ cut extracting the mover.

## Main results

* `Minimalist.SyntacticObject.mergeOp_node`: External Merge on the carrier is `mergeOp`.
* `Minimalist.SyntacticObject.mergeOp_node_im`: Internal Merge on the carrier is
  `mergeOp ∘ mergeOpUnit`.

## References

* [marcolli-chomsky-berwick-2025], §1.4 (Lemma 1.4.1, Proposition 1.4.2)
-/

namespace Minimalist.SyntacticObject

open RoseTree RoseTree.Nonplanar ConnesKreimer

/-- External Merge on the carrier is the algebraic Merge with the bare root label on the
    two-object workspace. -/
theorem mergeOp_node (S S' : SyntacticObject) :
    Merge.mergeOp (R := ℤ) (Sum.inr none) S.val S'.val
        (of' ({S.val, S'.val} : Forest (Nonplanar Vertex)))
      = of' (R := ℤ) ({(merge S S').val} : Forest (Nonplanar Vertex)) := by
  rw [Merge.mergeOp_pair, merge_val]

/-- Internal Merge on the carrier is the two-stage algebraic Merge, given the unique Δ^ρ cut `p0`
    of `T` extracting `mover` with remainder `remainder`. -/
theorem mergeOp_merge_im (mover remainder T : SyntacticObject)
    (p0 : Forest (Nonplanar Vertex) × Nonplanar Vertex)
    (h_filter : (cutSummandsN T.val).filter
        (fun p => p.1 = ({mover.val} : Forest (Nonplanar Vertex))) = {p0})
    (h_remainder : p0.2 = remainder.val)
    (hT : T.val ≠ mover.val) :
    Merge.mergeOp (R := ℤ) (Sum.inr none) remainder.val mover.val
        (Merge.mergeOpUnit (R := ℤ) mover.val
          (of' ({T.val} : Forest (Nonplanar Vertex))))
      = of' (R := ℤ)
          ({(merge remainder mover).val} : Forest (Nonplanar Vertex)) := by
  rw [Merge.mergeOp_im_composition (Sum.inr none) mover.val T.val remainder.val
        p0 h_filter h_remainder hT, merge_val]

end Minimalist.SyntacticObject
