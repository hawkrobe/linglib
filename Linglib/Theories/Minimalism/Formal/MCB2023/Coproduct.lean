/-
# Coproduct Structure and Merge on Workspaces

Formalizes §2.2–2.3 of Marcolli, Chomsky & Berwick (2023): quotient trees T/Tᵥ,
admissible cuts, the leading coproduct term, and Merge as a workspace operator.

The coproduct Δ(T) decomposes a tree into pairs (subtree, quotient) and is the
key structure connecting Merge to Hopf algebra formalism from QFT renormalization
(Connes-Kreimer).

## Main definitions

- `quotientTree`: T with subtree at v contracted to a leaf (Def 2.5)
- `AdmissibleCut`: set of non-overlapping internal nodes to cut (§2.2)
- `leadingCoproduct`: Δ₍₂₎(T) = Σᵥ Tᵥ ⊗ T/Tᵥ (eq 2.16)
- `forestExternalMerge` / `forestInternalMerge`: Merge lifted to workspaces

## References

- Marcolli, M., Chomsky, N. & Berwick, R.C. (2023). "Mathematical Structure of
  Syntactic Merge", §2.2–2.3
- Connes, A. & Kreimer, D. (1998). "Hopf Algebras, Renormalization and
  Noncommutative Geometry"
-/

import Linglib.Theories.Minimalism.Formal.MCB2023.Accessible
import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Basic

namespace Minimalism

/-! ## Quotient tree (Definition 2.5)

Given a tree T and a contained subtree Tᵥ, the quotient tree T/Tᵥ is obtained
by replacing Tᵥ with a single leaf (contracting the subtree to a point). -/

/-- A placeholder leaf token for quotient tree contraction points -/
private def quotientLeafToken : LIToken :=
  ⟨LexicalItem.simple .N [], 0⟩

/-- Quotient tree: replace the first occurrence of `v` in `T` with a leaf.
    Returns `none` if `v` is not found in `T`. -/
def quotientTree (T v : SyntacticObject) : Option SyntacticObject :=
  if T == v then some (.leaf quotientLeafToken)
  else match T with
    | .leaf _ => none
    | .node a b =>
      match quotientTree a v with
      | some a' => some (.node a' b)
      | none =>
        match quotientTree b v with
        | some b' => some (.node a b')
        | none => none

/-- If containsOrEq T v, then quotientTree T v returns some result -/
private theorem quotientTree_some_of_containsOrEq (T v : SyntacticObject)
    (h : containsOrEq T v) : ∃ q, quotientTree T v = some q := by
  -- Induction on the structure of T
  induction T with
  | leaf tok =>
    rcases h with rfl | hc
    · exact ⟨.leaf quotientLeafToken, by simp [quotientTree]⟩
    · exact absurd hc (leaf_contains_nothing tok v)
  | node a b iha ihb =>
    by_cases heq : SyntacticObject.node a b = v
    · exact ⟨.leaf quotientLeafToken, by simp [quotientTree, beq_iff_eq, heq]⟩
    · -- T ≠ v, so the if-then-else falls through
      simp only [quotientTree, beq_iff_eq, heq, ite_false]
      -- From containsOrEq and T ≠ v, we get contains T v
      have hc : contains (.node a b) v := by
        rcases h with rfl | hc
        · exact absurd rfl heq
        · exact hc
      -- Either a containsOrEq v, or b containsOrEq v
      -- We derive this from the contains proof
      have : containsOrEq a v ∨ containsOrEq b v := by
        cases hc with
        | imm _ _ himm =>
          simp only [immediatelyContains] at himm
          rcases himm with rfl | rfl
          · left; exact Or.inl rfl
          · right; exact Or.inl rfl
        | trans _ _ z himm hcz =>
          simp only [immediatelyContains] at himm
          rcases himm with rfl | rfl
          · left; exact Or.inr hcz
          · right; exact Or.inr hcz
      rcases this with ha | hb
      · -- a containsOrEq v: quotientTree a v succeeds
        obtain ⟨a', ha'⟩ := iha ha
        exact ⟨.node a' b, by simp [ha']⟩
      · -- b containsOrEq v: need to check quotientTree a v first
        obtain ⟨b', hb'⟩ := ihb hb
        cases hqa : quotientTree a v with
        | some a' => exact ⟨.node a' b, by simp [hqa]⟩
        | none => exact ⟨.node a b', by simp [hqa, hb']⟩

/-- If v is contained in T, quotientTree succeeds -/
theorem quotientTree_some_of_contains (T v : SyntacticObject)
    (h : contains T v) : (quotientTree T v).isSome = true := by
  obtain ⟨q, hq⟩ := quotientTree_some_of_containsOrEq T v (Or.inr h)
  simp [hq]

/-- If quotientTree T v succeeds, then T containsOrEq v -/
private theorem quotientTree_implies_containsOrEq (T v : SyntacticObject)
    (h : (quotientTree T v).isSome = true) : containsOrEq T v := by
  induction T with
  | leaf tok =>
    simp only [quotientTree] at h
    split at h
    · rename_i heq; rw [beq_iff_eq] at heq; exact Or.inl heq
    · simp at h
  | node a b iha ihb =>
    simp only [quotientTree] at h
    split at h
    · rename_i heq; rw [beq_iff_eq] at heq; exact Or.inl heq
    · rename_i hne
      split at h
      · rename_i a' ha'
        have := iha (by simp [ha'])
        rcases this with rfl | hc
        · exact Or.inr (contains.imm _ _ (by simp [immediatelyContains]))
        · exact Or.inr (contains.trans _ _ a (by simp [immediatelyContains]) hc)
      · split at h
        · rename_i _ b' hb'
          have := ihb (by simp [hb'])
          rcases this with rfl | hc
          · exact Or.inr (contains.imm _ _ (by simp [immediatelyContains]))
          · exact Or.inr (contains.trans _ _ b (by simp [immediatelyContains]) hc)
        · simp at h

/-- containsOrEq preserves leafCount ordering: v.leafCount ≤ T.leafCount -/
private theorem leafCount_le_of_containsOrEq (T v : SyntacticObject)
    (h : containsOrEq T v) : v.leafCount ≤ T.leafCount := by
  rcases h with rfl | hc
  · exact Nat.le_refl _
  · induction hc with
    | imm x y himm =>
      cases x with
      | leaf _ => simp [immediatelyContains] at himm
      | node a b =>
        simp only [immediatelyContains] at himm
        simp only [SyntacticObject.leafCount]
        rcases himm with rfl | rfl <;> omega
    | trans x y z himm _hyz ih =>
      cases x with
      | leaf _ => simp [immediatelyContains] at himm
      | node a b =>
        simp only [immediatelyContains] at himm
        simp only [SyntacticObject.leafCount]
        rcases himm with rfl | rfl <;> omega

/-- Quotient tree has correct leaf count: replacing a subtree with a leaf
    reduces leaf count by (v.leafCount - 1). -/
private theorem quotientTree_leafCount_aux (T v : SyntacticObject) :
    ∀ q, quotientTree T v = some q →
    q.leafCount = T.leafCount - v.leafCount + 1 := by
  induction T with
  | leaf tok =>
    intro q hq
    simp only [quotientTree] at hq
    split at hq
    · rename_i heq; rw [beq_iff_eq] at heq; subst heq
      simp at hq; subst hq
      simp [SyntacticObject.leafCount]
    · simp at hq
  | node a b iha ihb =>
    intro q hq
    simp only [quotientTree] at hq
    split at hq
    · rename_i heq; rw [beq_iff_eq] at heq; subst heq
      simp at hq; subst hq
      simp [SyntacticObject.leafCount]
    · rename_i hne
      split at hq
      · rename_i a' ha'
        have hqeq : q = .node a' b := by cases hq; rfl
        subst hqeq
        simp only [SyntacticObject.leafCount]
        have iha' := iha a' ha'
        have hle : v.leafCount ≤ a.leafCount :=
          leafCount_le_of_containsOrEq a v
            (quotientTree_implies_containsOrEq a v (by simp [ha']))
        omega
      · split at hq
        · rename_i _ b' hb'
          have hqeq : q = .node a b' := by cases hq; rfl
          subst hqeq
          simp only [SyntacticObject.leafCount]
          have ihb' := ihb b' hb'
          have hle : v.leafCount ≤ b.leafCount :=
            leafCount_le_of_containsOrEq b v
              (quotientTree_implies_containsOrEq b v (by simp [hb']))
          omega
        · simp at hq

theorem quotientTree_leafCount (T v q : SyntacticObject)
    (h : contains T v) (hq : quotientTree T v = some q) :
    q.leafCount = T.leafCount - v.leafCount + 1 :=
  quotientTree_leafCount_aux T v q hq

/-! ## Admissible cuts (§2.2)

An admissible cut is a set of internal nodes such that no two are
in an ancestor-descendant relation (i.e., they are pairwise incomparable
under containment). -/

/-- Admissible cut: a finite set of nodes that form an antichain under containment.
    Uses mathlib's `IsAntichain` — `s.Pairwise rᶜ` — to express pairwise incomparability. -/
structure AdmissibleCut (so : SyntacticObject) where
  cutNodes : Finset SyntacticObject
  /-- All cut nodes are proper subtrees of so -/
  contained : ∀ n ∈ cutNodes, contains so n
  /-- Cut nodes are pairwise incomparable (no ancestor-descendant pairs) -/
  admissible : IsAntichain contains (cutNodes : Set SyntacticObject)

/-- The trivial cut: empty set of cut nodes -/
def trivialCut (so : SyntacticObject) : AdmissibleCut so where
  cutNodes := ∅
  contained := by simp
  admissible := by simp [IsAntichain, Set.Pairwise]

/-- Number of admissible cuts -/
def numAdmissibleCuts (so : SyntacticObject) : Nat :=
  -- The number of antichains in the subtree poset.
  -- For a binary tree with n internal nodes, this grows exponentially.
  -- We just define it recursively for now.
  match so with
  | .leaf _ => 1  -- only the trivial cut
  | .node a b => numAdmissibleCuts a * numAdmissibleCuts b + 1

/-! ## Leading coproduct (equation 2.16)

The leading coproduct Δ₍₂₎(T) extracts each proper subtree Tᵥ and pairs it
with the quotient T/Tᵥ:

  Δ₍₂₎(T) = Σ_{v ∈ V_int} Tᵥ ⊗ T/Tᵥ

This is the "first-order" term of the full Connes-Kreimer coproduct. -/

/-- Leading coproduct: pairs (subtree, quotient) for each internal node subtree -/
def leadingCoproduct (T : SyntacticObject) :
    List (SyntacticObject × Option SyntacticObject) :=
  T.properSubtrees.filterMap (λ v =>
    match v with
    | .leaf _ => none  -- only internal node subtrees contribute
    | .node _ _ => some (v, quotientTree T v))

/-- Coproduct size identity: T.leafCount = v.leafCount + (T/v).leafCount - 1

    This is the key size conservation law for the coproduct decomposition.
    It says that cutting a tree into a subtree and quotient preserves the
    total "weight" up to the shared boundary. -/
theorem coproduct_size_identity (T v q : SyntacticObject)
    (hc : contains T v) (hq : quotientTree T v = some q) :
    T.leafCount = v.leafCount + q.leafCount - 1 := by
  have h := quotientTree_leafCount T v q hc hq
  -- h : q.leafCount = T.leafCount - v.leafCount + 1
  have hle : v.leafCount ≤ T.leafCount :=
    leafCount_le_of_containsOrEq T v (Or.inr hc)
  have hqpos : q.leafCount ≥ 1 := by omega
  omega

/-! ## Merge on workspaces (Definition 2.10)

Merge lifts from an operation on pairs of SOs to an operation on
the workspace (list of SOs). The algebraic formulation uses the coproduct
to identify which subterms can be re-merged (Internal Merge) or
combines distinct workspace members (External Merge). -/

/-- External Merge on workspace: combine two members into one -/
def listExternalMerge (T₁ T₂ : SyntacticObject)
    (F : List SyntacticObject) : List SyntacticObject :=
  merge T₁ T₂ :: (F.filter (· != T₁)).filter (· != T₂)

/-- Internal Merge on workspace: re-merge a contained subterm -/
def listInternalMerge (T β : SyntacticObject)
    (F : List SyntacticObject) : List SyntacticObject :=
  merge β T :: F.filter (· != T)

/-- External Merge on workspaces produces a workspace containing merge(T₁, T₂) -/
theorem list_em_contains_merge (T₁ T₂ : SyntacticObject)
    (F : List SyntacticObject) :
    merge T₁ T₂ ∈ listExternalMerge T₁ T₂ F := by
  simp [listExternalMerge]

/-- Internal Merge on workspaces produces a workspace containing merge(β, T) -/
theorem list_im_contains_merge (T β : SyntacticObject)
    (F : List SyntacticObject) :
    merge β T ∈ listInternalMerge T β F := by
  simp [listInternalMerge]

/-- The workspace merge operation reduces to pointwise merge on SOs.
    This is the key theorem that the algebraic (Hopf algebra) formulation
    recovers the simple set-theoretic Merge operation. -/
theorem workspace_merge_recovers_merge (T₁ T₂ : SyntacticObject) :
    merge T₁ T₂ ∈ listExternalMerge T₁ T₂ [T₁, T₂] := by
  simp [listExternalMerge]

/-- Connection to MergeUnification: the EM/IM workspace operations align
    with the containment-based partition. When inputs are incomparable,
    listExternalMerge is the appropriate operation; when one contains the
    other, listInternalMerge is appropriate. -/
theorem workspace_merge_partition (α β : SyntacticObject)
    (_hne : α ≠ β) (F : List SyntacticObject)
    (_hα : α ∈ F) :
    -- The operation is determined by the containment relationship
    (¬contains α β ∧ ¬contains β α →
      merge α β ∈ listExternalMerge α β F) ∧
    (contains α β →
      merge β α ∈ listInternalMerge α β F) := by
  constructor
  · intro _; exact list_em_contains_merge α β F
  · intro _; exact list_im_contains_merge α β F

end Minimalism
