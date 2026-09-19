import Mathlib.ModelTheory.Order

/-!
# The theory of total preorders

This file defines the first-order theory of total preorders in an ordered language, which is
`preorderTheory` together with the totality sentence. It sits strictly between `preorderTheory`
and `linearOrderTheory`, one antisymmetry axiom short of the latter. A preorder whose `≤` is
total models it, and every model of it is a model of `preorderTheory`. `[UPSTREAM]` candidate
for `Mathlib.ModelTheory.Order`.

## Main declarations

* `FirstOrder.Language.totalPreorderTheory`: the theory of total preorders.
* `FirstOrder.Language.model_totalPreorder`: a total preorder is a model of the theory.
-/

namespace FirstOrder.Language

variable (L : Language) [IsOrdered L]

/-- The theory of total preorders is `preorderTheory` together with totality. -/
def totalPreorderTheory : L.Theory :=
  insert leSymb.total L.preorderTheory

variable {L} {M : Type*} [L.Structure M]

instance [h : M ⊨ L.totalPreorderTheory] : M ⊨ L.preorderTheory :=
  h.mono (Set.subset_insert _ _)

/-- A preorder whose `≤` is total is a model of the theory of total preorders. -/
instance model_totalPreorder [Preorder M] [Std.Total (α := M) (· ≤ ·)] [L.OrderedStructure M] :
    M ⊨ L.totalPreorderTheory := by
  simp only [totalPreorderTheory, Theory.model_insert_iff, Relations.realize_total, relMap_leSymb,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, model_preorder, and_true]
  exact ⟨Std.Total.total⟩

/-- A linear order models the theory of total preorders. -/
instance [h : M ⊨ L.linearOrderTheory] : M ⊨ L.totalPreorderTheory :=
  Theory.model_insert_iff.2 ⟨(Theory.model_insert_iff.1 h).1, inferInstance⟩

end FirstOrder.Language
