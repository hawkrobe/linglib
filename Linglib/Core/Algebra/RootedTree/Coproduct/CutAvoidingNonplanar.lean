import Linglib.Core.Algebra.RootedTree.Coproduct.PruningNonplanar

/-!
# Cut-avoiding trees in the nonplanar Connes–Kreimer coproduct
[marcolli-chomsky-berwick-2025] [foissy-2002]

A pure structural condition on `Nonplanar α`: when does a tree `T` *avoid* a
target `X`? Answer: `T ≠ X` and no Δ^ρ cut summand of `T` extracts `X` as a crown
component — equivalently, no summand `of' M ⊗ ofTree R` of the deletion coproduct
`Δ^ρ T` has `X ∈ M`.

This is the `cutSummandsN`-based re-derivation of the legacy `CutAvoiding`
(stated over `CutShape`/`TraceTree` in
`Core/Combinatorics/RootedTree/CutAvoiding.lean`), matching the n-ary cut-multiset
shape. The predicate is generic over the leaf alphabet `α` and has nothing to do
with any particular linguistic theory; it is a relation between trees in the
Connes–Kreimer combinatorial substrate.

## Contents

- `CutAvoidingN X T`: per-target, per-tree predicate.
- `CutAvoidingForestN F W`: per-target-forest, per-workspace predicate (every
  component of `W` avoids every element of `F`).
- Namespace lemmas: `CutAvoidingForestN.{empty, of_cons, head, not_mem, no_cut,
  head_pair, not_mem_pair}`.

Consumed by `Minimalist.Merge.mergeOp_factor_out_singleton` /
`mergeOp_pair_residual` (MCB Lemma 1.4.1 Case 1).
-/

namespace RootedTree.ConnesKreimer

variable {α : Type*}

/-- A tree `T` *avoids* the target `X` in the nonplanar Δ^ρ coproduct: `T ≠ X` and
    no cut summand of `T` extracts `X` as a crown component. Equivalently, no
    summand `of' M ⊗ ofTree R` of `Δ^ρ T` has `X ∈ M`. -/
structure CutAvoidingN (X T : Nonplanar α) : Prop where
  /-- `T` is not literally the target `X`. -/
  ne_self : T ≠ X
  /-- No cut summand of `T` has `X` in its crown forest. -/
  no_cut  : ∀ p ∈ cutSummandsN T, X ∉ p.1

/-- A workspace `W : Forest (Nonplanar α)` is `F`-avoiding (component-wise): every
    component `T` of `W` avoids every target `X` in the forest `F`. -/
def CutAvoidingForestN (F W : Forest (Nonplanar α)) : Prop :=
  ∀ T ∈ W, ∀ X ∈ F, CutAvoidingN X T

namespace CutAvoidingForestN

variable {F W : Forest (Nonplanar α)}

/-- Empty workspace is trivially `F`-avoiding for any target forest `F`. -/
lemma empty (F : Forest (Nonplanar α)) :
    CutAvoidingForestN F (0 : Forest (Nonplanar α)) :=
  fun _ h => absurd h (Multiset.notMem_zero _)

/-- Cons preservation: if `T ::ₘ W` is `F`-avoiding then so is `W`. -/
lemma of_cons {T : Nonplanar α} (h : CutAvoidingForestN F (T ::ₘ W)) :
    CutAvoidingForestN F W :=
  fun U hU => h U (Multiset.mem_cons_of_mem hU)

/-- Cons head: if `T ::ₘ W` is `F`-avoiding then `T` avoids every `X ∈ F`. -/
lemma head {T : Nonplanar α} (h : CutAvoidingForestN F (T ::ₘ W)) :
    ∀ X ∈ F, CutAvoidingN X T :=
  h T (Multiset.mem_cons_self _ _)

/-- Workspace-level: no target `X ∈ F` is a member of the workspace `W`. -/
lemma not_mem (h : CutAvoidingForestN F W) : ∀ X ∈ F, X ∉ W := by
  intro X hX hX_mem
  exact (h X hX_mem X hX).ne_self rfl

/-- Workspace-level: no cut summand of any component `T ∈ W` extracts any target
    `X ∈ F` as a crown component. -/
lemma no_cut (h : CutAvoidingForestN F W) :
    ∀ T ∈ W, ∀ X ∈ F, ∀ p ∈ cutSummandsN T, X ∉ p.1 :=
  fun T hT X hX => (h T hT X hX).no_cut

/-- For a workspace `T ::ₘ W` avoiding the pair-target forest `{S, S'}`, extract
    both per-tree avoidances at `T`. Convenience for the two-operand Merge case. -/
lemma head_pair {S S' T : Nonplanar α} {W : Forest (Nonplanar α)}
    (h : CutAvoidingForestN ({S, S'} : Forest (Nonplanar α)) (T ::ₘ W)) :
    CutAvoidingN S T ∧ CutAvoidingN S' T :=
  let h_av := CutAvoidingForestN.head h
  ⟨h_av S (Multiset.mem_cons_self _ _),
   h_av S' (by
     show S' ∈ S ::ₘ ({S'} : Forest (Nonplanar α))
     exact Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl))⟩

/-- For a workspace `W` avoiding the pair-target forest `{S, S'}`, neither target
    is a member of `W`. Convenience for the two-operand Merge case. -/
lemma not_mem_pair {S S' : Nonplanar α} {W : Forest (Nonplanar α)}
    (h : CutAvoidingForestN ({S, S'} : Forest (Nonplanar α)) W) : S ∉ W ∧ S' ∉ W :=
  ⟨h.not_mem S (Multiset.mem_cons_self _ _),
   h.not_mem S' (by
     show S' ∈ S ::ₘ ({S'} : Forest (Nonplanar α))
     exact Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl))⟩

end CutAvoidingForestN

end RootedTree.ConnesKreimer
