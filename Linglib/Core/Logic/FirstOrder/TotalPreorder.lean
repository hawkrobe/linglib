import Mathlib.ModelTheory.Order
import Linglib.Core.Order.TotalPreorder

/-!
# The model theory of total preorders

The theory of total preorders in mathlib's `Language.order` — `preorderTheory`
plus the totality sentence, one antisymmetry axiom short of
`linearOrderTheory` — and the round-trip between its models and the working
bundle `Core.Order.TotalPreorder`. The canonical semantic-ordering object is
the model-theoretic one (a `Language.order.Structure` satisfying this theory,
the same shape as every other model in the first-order substrate); the bundle
is its decidable, proof-transparent presentation, and `toStructure`/`ofModel`
exchange the two.
-/

namespace FirstOrder.Language

variable (L : Language) [IsOrdered L]

/-- The theory of total preorders: `preorderTheory` plus totality. Sits
strictly between `preorderTheory` and `linearOrderTheory` (antisymmetry). -/
def totalPreorderTheory : L.Theory :=
  insert leSymb.total L.preorderTheory

variable {L} {M : Type*}

instance [L.Structure M] [h : M ⊨ L.totalPreorderTheory] :
    M ⊨ L.preorderTheory :=
  h.mono (Set.subset_insert _ _)

end FirstOrder.Language

namespace Core.Order.TotalPreorder

open FirstOrder FirstOrder.Language

variable {α : Type*}

/-- The `Language.order`-structure a bundle presents: `leSymb` is `ord.le`. -/
@[implicit_reducible] def toStructure (ord : Core.Order.TotalPreorder α) :
    Language.order.Structure α :=
  @orderStructure α ⟨ord.le⟩

/-- The presented structure models the total-preorder theory: the bundle is a
decidable presentation of the model-theoretic object. -/
theorem toStructure_model (ord : Core.Order.TotalPreorder α) :
    letI := ord.toStructure
    α ⊨ Language.order.totalPreorderTheory := by
  letI := ord.toStructure
  refine Theory.model_iff _ |>.mpr fun φ hφ => ?_
  simp only [Language.totalPreorderTheory, Language.preorderTheory,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
  rcases hφ with rfl | rfl | rfl
  · rw [Relations.realize_total]
    exact ⟨fun a b => ord.le_total a b⟩
  · rw [Relations.realize_reflexive]
    exact ⟨ord.le_refl⟩
  · rw [Relations.realize_transitive]
    exact ⟨fun a b c => ord.le_trans a b c⟩

/-- A decidable model of the total-preorder theory presents a bundle: the two
presentations round-trip. -/
def ofModel [Language.order.Structure α]
    [h : α ⊨ Language.order.totalPreorderTheory]
    [DecidableRel (fun a b : α =>
      Structure.RelMap (leSymb : Language.order.Relations 2) ![a, b])] :
    Core.Order.TotalPreorder α where
  le a b := Structure.RelMap (leSymb : Language.order.Relations 2) ![a, b]
  isPreorder :=
    { refl := (Relations.realize_reflexive.mp <|
        Theory.model_iff _ |>.mp
          (inferInstance : α ⊨ Language.order.preorderTheory) _ <|
          by simp [Language.preorderTheory]).refl
      trans := (Relations.realize_transitive.mp <|
        Theory.model_iff _ |>.mp
          (inferInstance : α ⊨ Language.order.preorderTheory) _ <|
          by simp [Language.preorderTheory]).trans }
  total := Relations.realize_total.mp <|
    Theory.model_iff _ |>.mp h _ <| by simp [Language.totalPreorderTheory]
  decRel := inferInstance

end Core.Order.TotalPreorder
