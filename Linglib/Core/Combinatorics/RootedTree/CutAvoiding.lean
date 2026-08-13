import Linglib.Core.Combinatorics.RootedTree.Cut

open RoseTree RoseTree.Nonplanar

/-!
# Cut-avoiding trees
[marcolli-chomsky-berwick-2025] [foissy-2002]

A tree `T` *avoids* a target `X` when `T ≠ X` and no Δ^ρ cut summand of `T`
extracts `X` as a crown component (`CutAvoiding`), together with the
componentwise closure to forests (`CutAvoidingForest`).
-/

namespace ConnesKreimer

variable {α : Type*}

/-- A tree `T` *avoids* the target `X` in the nonplanar Δ^ρ coproduct: `T ≠ X` and
    no cut summand of `T` extracts `X` as a crown component. Equivalently, no
    summand `of' M ⊗ ofTree R` of `Δ^ρ T` has `X ∈ M`. -/
@[mk_iff]
structure CutAvoiding (X T : Nonplanar α) : Prop where
  /-- `T` is not literally the target `X`. -/
  ne_self : T ≠ X
  /-- No cut summand of `T` has `X` in its crown forest. -/
  no_cut  : ∀ p ∈ cutSummandsN T, X ∉ p.1

/-- A workspace `W : Multiset (Nonplanar α)` is `F`-avoiding (component-wise): every
    component `T` of `W` avoids every target `X` in the forest `F`. -/
def CutAvoidingForest (F W : Multiset (Nonplanar α)) : Prop :=
  ∀ T ∈ W, ∀ X ∈ F, CutAvoiding X T

namespace CutAvoidingForest

variable {F W : Multiset (Nonplanar α)}

/-- Empty workspace is trivially `F`-avoiding for any target forest `F`. -/
lemma empty (F : Multiset (Nonplanar α)) :
    CutAvoidingForest F (0 : Multiset (Nonplanar α)) :=
  fun _ h => absurd h (Multiset.notMem_zero _)

/-- Cons preservation: if `T ::ₘ W` is `F`-avoiding then so is `W`. -/
lemma of_cons {T : Nonplanar α} (h : CutAvoidingForest F (T ::ₘ W)) :
    CutAvoidingForest F W :=
  fun U hU => h U (Multiset.mem_cons_of_mem hU)

/-- Cons head: if `T ::ₘ W` is `F`-avoiding then `T` avoids every `X ∈ F`. -/
lemma head {T : Nonplanar α} (h : CutAvoidingForest F (T ::ₘ W)) :
    ∀ X ∈ F, CutAvoiding X T :=
  h T (Multiset.mem_cons_self _ _)

/-- Workspace-level: no target `X ∈ F` is a member of the workspace `W`. -/
lemma not_mem (h : CutAvoidingForest F W) : ∀ X ∈ F, X ∉ W := by
  intro X hX hX_mem
  exact (h X hX_mem X hX).ne_self rfl

/-- Workspace-level: no cut summand of any component `T ∈ W` extracts any target
    `X ∈ F` as a crown component. -/
lemma no_cut (h : CutAvoidingForest F W) :
    ∀ T ∈ W, ∀ X ∈ F, ∀ p ∈ cutSummandsN T, X ∉ p.1 :=
  fun T hT X hX => (h T hT X hX).no_cut

end CutAvoidingForest

end ConnesKreimer
