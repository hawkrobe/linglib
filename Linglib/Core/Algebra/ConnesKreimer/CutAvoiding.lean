import Linglib.Core.Combinatorics.RootedTree.AdmissibleCut

/-!
# Cut-avoiding trees in the Connes-Kreimer coproduct
@cite{marcolli-chomsky-berwick-2025} @cite{foissy-2002}

A pure structural condition on `TraceTree α β`: when does a tree `T` "avoid"
a target `X`? Answer: `T ≠ X` and no admissible cut on `T` extracts `X` as
a subforest element. Equivalently — interpreted in the Connes-Kreimer Hopf
algebra — no summand `M ⊗ R` of the deletion coproduct `Δ^d T` has `X ∈ M`.

This predicate has nothing to do with any particular linguistic theory; it
is a relation between trees in the Connes-Kreimer combinatorial substrate.
Generic over leaf alphabet `α` and trace alphabet `β`. Defined here so that
any consumer (Minimalism-style algebraic Merge per
@cite{marcolli-chomsky-berwick-2025}, TAG-via-Hopf, categorial-grammar
combinators, renormalization-style "avoid these counterterms") can reuse it.

## Contents

- `CutAvoiding X T`: per-target, per-tree predicate.
- `CutAvoidingForest F W`: per-target-forest, per-workspace predicate
  (every component of `W` avoids every element of `F`).
- Namespace lemmas: `CutAvoidingForest.empty`, `CutAvoidingForest.of_cons`,
  `CutAvoidingForest.head`, `CutAvoidingForest.not_mem`,
  `CutAvoidingForest.no_cut`.
-/

namespace ConnesKreimer

variable {α β : Type*} [DecidableEq α]

/-- A tree `T` *avoids* the target `X` in the Connes-Kreimer coproduct:
    `T ≠ X` and no admissible cut on `T` extracts `X` as a subforest
    element. Equivalently, no summand `M ⊗ R` of `Δ^d T` has `X ∈ M`. -/
structure CutAvoiding (X T : TraceTree α β) : Prop where
  /-- `T` is not literally the target `X`. -/
  ne_self : T ≠ X
  /-- No admissible cut on `T` extracts `X` as a subforest element. -/
  no_cut  : ∀ c : CutShape T, X ∉ CutShape.cutForest c

/-- A workspace `W : TraceForest α β` is `F`-avoiding (component-wise):
    every component `T` of `W` avoids every target `X` in the forest `F`. -/
def CutAvoidingForest (F W : TraceForest α β) : Prop :=
  ∀ T ∈ W, ∀ X ∈ F, CutAvoiding X T

namespace CutAvoidingForest

variable {F W : TraceForest α β}

/-- Empty workspace is trivially `F`-avoiding for any target forest `F`. -/
lemma empty (F : TraceForest α β) : CutAvoidingForest F (0 : TraceForest α β) :=
  fun _ h => by simp at h

/-- Cons preservation: if `T ::ₘ W` is `F`-avoiding then so is `W`. -/
lemma of_cons {T : TraceTree α β} (h : CutAvoidingForest F (T ::ₘ W)) :
    CutAvoidingForest F W :=
  fun U hU => h U (Multiset.mem_cons_of_mem hU)

/-- Cons head: if `T ::ₘ W` is `F`-avoiding then `T` avoids every `X ∈ F`. -/
lemma head {T : TraceTree α β} (h : CutAvoidingForest F (T ::ₘ W)) :
    ∀ X ∈ F, CutAvoiding X T :=
  h T (Multiset.mem_cons_self _ _)

/-- Workspace-level: no target `X ∈ F` is a member of the workspace `W`. -/
lemma not_mem (h : CutAvoidingForest F W) : ∀ X ∈ F, X ∉ W := by
  intros X hX hX_mem
  exact (h X hX_mem X hX).ne_self rfl

/-- Workspace-level: no admissible cut on any component `T ∈ W` extracts
    any target `X ∈ F`. -/
lemma no_cut (h : CutAvoidingForest F W) :
    ∀ T ∈ W, ∀ X ∈ F, ∀ c : CutShape T, X ∉ CutShape.cutForest c :=
  fun T hT X hX => (h T hT X hX).no_cut

/-- For a workspace `T ::ₘ W` avoiding the pair-target forest `{S, S'}`,
    extract both per-tree avoidances at `T`. Convenience lemma for the
    common two-target case (e.g., MCB algebraic Merge with operands `S, S'`). -/
lemma head_pair {S S' T : TraceTree α β} {W : TraceForest α β}
    (h : CutAvoidingForest ({S, S'} : TraceForest α β) (T ::ₘ W)) :
    CutAvoiding S T ∧ CutAvoiding S' T :=
  let h_av := CutAvoidingForest.head h
  ⟨h_av S (Multiset.mem_cons_self _ _),
   h_av S' (by
     show S' ∈ S ::ₘ ({S'} : TraceForest α β)
     exact Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl))⟩

/-- For a workspace `W` avoiding the pair-target forest `{S, S'}`, neither
    target is a member of `W`. Convenience for the two-target case. -/
lemma not_mem_pair {S S' : TraceTree α β} {W : TraceForest α β}
    (h : CutAvoidingForest ({S, S'} : TraceForest α β) W) : S ∉ W ∧ S' ∉ W :=
  ⟨h.not_mem S (Multiset.mem_cons_self _ _),
   h.not_mem S' (by
     show S' ∈ S ::ₘ ({S'} : TraceForest α β)
     exact Multiset.mem_cons_of_mem (Multiset.mem_singleton.mpr rfl))⟩

end CutAvoidingForest

end ConnesKreimer
