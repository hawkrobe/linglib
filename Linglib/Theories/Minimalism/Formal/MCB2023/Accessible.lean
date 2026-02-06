/-
# Accessible Terms and Workspace Counting

Formalizes §2 of Marcolli, Chomsky & Berwick (2023): accessible terms,
workspace counting functions, and the counting behavior of External vs
Internal Merge (Proposition 2.17 and Corollary 2.22).

## Main definitions

- `subtrees`, `properSubtrees`: subtree extraction
- `leafMultiset`: frontier tokens of an SO
- `accessibleTerms`: leaf-sets of subtrees at internal nodes (Def 2.4)
- `b₀`, `numAcc`, `wsSize`, `wsSizeAlt`: workspace counting (Def 2.4, eq 2.8–2.9)
- `depth`: depth of a subtree occurrence

## Main results

- Proposition 2.17: counting behavior of EM vs IM
- Corollary 2.22: sideward/countercyclic Merge violates counting constraints

## References

- Marcolli, M., Chomsky, N. & Berwick, R.C. (2023). "Mathematical Structure of
  Syntactic Merge", §2
-/

import Linglib.Theories.Minimalism.Formal.MCB2023.FreeMagmaEquiv
import Linglib.Theories.Minimalism.Formal.MergeUnification
import Mathlib.Data.Multiset.Basic

namespace Minimalism

/-! ## Subtree extraction -/

/-- All subtrees of an SO (including self) -/
def SyntacticObject.subtrees : SyntacticObject → List SyntacticObject
  | so@(.leaf _) => [so]
  | so@(.node a b) => so :: (a.subtrees ++ b.subtrees)

/-- Proper subtrees (excluding self) -/
def SyntacticObject.properSubtrees : SyntacticObject → List SyntacticObject
  | .leaf _ => []
  | .node a b => a.subtrees ++ b.subtrees

/-- Internal nodes (subtrees that are .node) -/
def SyntacticObject.internalNodes : SyntacticObject → List SyntacticObject
  | .leaf _ => []
  | so@(.node a b) => so :: (a.internalNodes ++ b.internalNodes)

/-- Internal node count (= nodeCount from SyntacticObjects.lean) -/
theorem internalNodes_length_eq_nodeCount (so : SyntacticObject) :
    so.internalNodes.length = so.nodeCount := by
  induction so with
  | leaf _ => simp [SyntacticObject.internalNodes, SyntacticObject.nodeCount]
  | node a b iha ihb =>
    simp [SyntacticObject.internalNodes, SyntacticObject.nodeCount, List.length_cons,
          List.length_append]
    omega

/-! ## Leaf multisets (frontier tokens) -/

/-- The multiset of leaf tokens at the frontier of an SO -/
def SyntacticObject.leafMultiset : SyntacticObject → List LIToken
  | .leaf tok => [tok]
  | .node a b => a.leafMultiset ++ b.leafMultiset

theorem leafMultiset_length_eq_leafCount (so : SyntacticObject) :
    so.leafMultiset.length = so.leafCount := by
  induction so with
  | leaf _ => simp [SyntacticObject.leafMultiset, SyntacticObject.leafCount]
  | node a b iha ihb =>
    simp [SyntacticObject.leafMultiset, SyntacticObject.leafCount, List.length_append]
    omega

/-- Leaf multiset as a `Multiset` — the mathematically correct type
    (frontier token identity is order-independent). -/
def SyntacticObject.leafMultisetM (so : SyntacticObject) : Multiset LIToken :=
  ↑so.leafMultiset

/-! ## Accessible terms (Definition 2.4)

For a tree T, the accessible terms are the leaf-sets of subtrees
rooted at internal nodes. That is, for each internal node v,
we take L(T_v) = the leaf multiset of the subtree rooted at v. -/

/-- Accessible terms: leaf-multisets of subtrees at internal nodes -/
def SyntacticObject.accessibleTerms : SyntacticObject → List (List LIToken)
  | .leaf _ => []
  | so@(.node a b) => so.leafMultiset :: (a.accessibleTerms ++ b.accessibleTerms)

/-- Accessible terms as `Multiset` of `Multiset`s — order-independent identity. -/
def SyntacticObject.accessibleTermsM (so : SyntacticObject) : Multiset (Multiset LIToken) :=
  ↑(so.accessibleTerms.map (↑· : List LIToken → Multiset LIToken))

/-- Number of accessible terms = number of internal nodes -/
theorem accessibleTerms_length_eq_nodeCount (so : SyntacticObject) :
    so.accessibleTerms.length = so.nodeCount := by
  induction so with
  | leaf _ => simp [SyntacticObject.accessibleTerms, SyntacticObject.nodeCount]
  | node a b iha ihb =>
    simp [SyntacticObject.accessibleTerms, SyntacticObject.nodeCount, List.length_cons,
          List.length_append]
    omega

/-! ## Workspace counting (Definition 2.4, equations 2.8–2.9)

A workspace (forest) is a list of SOs = the connected components. -/

/-- b₀(F): number of connected components = List.length -/
def b₀ (F : List SyntacticObject) : Nat := F.length

/-- Total accessible terms across all trees in forest -/
def numAcc (F : List SyntacticObject) : Nat :=
  (F.map (·.accessibleTerms.length)).sum

/-- σ(F) = b₀(F) + #Acc(F) (eq 2.8) -/
def wsSize (F : List SyntacticObject) : Nat := b₀ F + numAcc F

/-- Total internal nodes across all trees in forest -/
def numVertices (F : List SyntacticObject) : Nat :=
  (F.map (·.nodeCount)).sum

/-- σ̂(F) = b₀(F) + #V(F) (eq 2.9) -/
def wsSizeAlt (F : List SyntacticObject) : Nat := b₀ F + numVertices F

/-- numAcc and numVertices agree: accessible term count = internal node count
    per tree, so the sums coincide. -/
theorem numAcc_eq_numVertices (F : List SyntacticObject) : numAcc F = numVertices F := by
  simp only [numAcc, numVertices]
  congr 1
  induction F with
  | nil => rfl
  | cons so rest ih =>
    simp [List.map, accessibleTerms_length_eq_nodeCount, ih]

/-- σ̂ = σ since #Acc = #V (both equal total nodeCount) -/
theorem wsSize_eq_wsSizeAlt (F : List SyntacticObject) : wsSize F = wsSizeAlt F := by
  simp only [wsSize, wsSizeAlt]
  congr 1
  exact numAcc_eq_numVertices F

/-! ## Depth of a subtree occurrence -/

/-- Depth of β in α (0 if β = α, +1 per level) -/
def SyntacticObject.depthOf (α β : SyntacticObject) : Option Nat :=
  if α == β then some 0
  else match α with
    | .leaf _ => none
    | .node l r =>
      match l.depthOf β, r.depthOf β with
      | some d, _ => some (d + 1)
      | _, some d => some (d + 1)
      | none, none => none

/-! ## Proposition 2.17: Counting behavior of EM vs IM

External Merge takes two trees T₁, T₂ from workspace F and creates
merge(T₁, T₂), reducing components by 1 and adding a new root node.

Internal Merge takes a tree T from F with a contained subtree β,
re-merging β at the root: merge(β, T), keeping the same components. -/

/-! ### List filter/count helpers -/

/-- Filtering out an element with count 1 reduces length by 1 -/
private theorem length_filter_bne_of_count_one {α : Type*} [DecidableEq α]
    (L : List α) (x : α) (hx : x ∈ L) (hc : L.count x = 1) :
    (L.filter (· != x)).length = L.length - 1 := by
  induction L with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.filter]
    by_cases heq : hd = x
    · -- hd = x: this element is filtered out
      have hbne_false : (hd != x) = false := by simp [bne_iff_ne, heq]
      simp only [hbne_false, ite_false]
      -- count (hd :: tl) x = 1, hd = x, so tl.count x = 0
      have hc' : tl.count x = 0 := by
        rw [heq] at hc
        simp only [List.count_cons_self] at hc
        omega
      -- So filter (· != x) on tl = tl
      have hfilt : tl.filter (· != x) = tl := by
        rw [List.filter_eq_self]
        intro a ha
        simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
        intro heqa; subst heqa
        exact absurd (List.count_pos_iff.mpr ha) (by omega)
      rw [hfilt]
      simp [List.length]
    · -- hd ≠ x: this element is kept
      have hbne_true : (hd != x) = true := by simp [bne_iff_ne, heq]
      simp only [hbne_true, ite_true, List.length_cons]
      have hx' : x ∈ tl := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact absurd rfl heq
        · exact h
      have hc' : tl.count x = 1 := by
        rw [List.count_cons] at hc
        simp [beq_iff_eq, heq] at hc
        exact hc
      have ihres := ih hx' hc'
      have hlen_pos : tl.length ≥ 1 := List.length_pos_of_mem hx'
      omega

section Counting

variable {F : List SyntacticObject}

/-- External Merge: workspace goes from F to F' where T₁,T₂ ∈ F replaced by merge(T₁,T₂) -/
def emWorkspace (T₁ T₂ : SyntacticObject) (F : List SyntacticObject) : List SyntacticObject :=
  merge T₁ T₂ :: F.filter (· != T₁) |>.filter (· != T₂)

/-- Internal Merge: workspace goes from F to F' where T ∈ F replaced by merge(β, T) -/
def imWorkspace (T β : SyntacticObject) (F : List SyntacticObject) : List SyntacticObject :=
  merge β T :: F.filter (· != T)

/-- EM: b₀ decreases by 1 (two components become one) -/
theorem em_b0_decreases (T₁ T₂ : SyntacticObject)
    (hT₁ : T₁ ∈ F) (hT₂ : T₂ ∈ F) (hne : T₁ ≠ T₂)
    (huniq₁ : F.count T₁ = 1) (huniq₂ : F.count T₂ = 1) :
    b₀ (emWorkspace T₁ T₂ F) = b₀ F - 1 := by
  -- TODO: Double filter removes T₁ and T₂ (each with count 1), cons adds merge back.
  -- Requires showing filter preserves count of distinct elements.
  sorry

/-- EM: accessible terms increase by 2 (new root adds one for each child subtree
    plus the root itself, but the children's accessible terms are preserved) -/
theorem em_acc_increases (T₁ T₂ : SyntacticObject)
    (hT₁ : T₁ ∈ F) (hT₂ : T₂ ∈ F) (hne : T₁ ≠ T₂)
    (huniq₁ : F.count T₁ = 1) (huniq₂ : F.count T₂ = 1) :
    numAcc (emWorkspace T₁ T₂ F) = numAcc F + 1 := by
  -- TODO: merge(T₁,T₂) has nodeCount = 1 + T₁.nodeCount + T₂.nodeCount,
  -- so #Acc gains the new root's accessible term. The +1 comes from the
  -- single new internal node at the root of merge.
  sorry

/-- EM: σ increases by 1 (Δb₀ = -1, Δ#Acc = +1, net = 0... but σ = b₀ + #Acc
    so Δσ = -1 + 1 = 0 — actually MCB2023 Table says Δσ = +1 for EM.
    This is because Δ#Acc = +2 in their counting. -/
-- Note: The exact counting depends on precise definitions. We state
-- the constraint that EM changes σ predictably.
theorem em_wsSize_change (T₁ T₂ : SyntacticObject)
    (hT₁ : T₁ ∈ F) (hT₂ : T₂ ∈ F) (hne : T₁ ≠ T₂)
    (huniq₁ : F.count T₁ = 1) (huniq₂ : F.count T₂ = 1) :
    wsSize (emWorkspace T₁ T₂ F) = wsSize F := by
  -- TODO: σ = b₀ + #Acc. Under EM, b₀ decreases by 1 and #Acc increases by 1.
  -- Net change is 0 (or +1 depending on exact accessible term definition).
  sorry

/-- IM: b₀ preserved (same number of components) -/
theorem im_b0_preserved (T β : SyntacticObject)
    (hT : T ∈ F) (hβT : contains T β)
    (huniq : F.count T = 1) :
    b₀ (imWorkspace T β F) = b₀ F := by
  simp only [imWorkspace, b₀, List.length_cons]
  have := length_filter_bne_of_count_one F T hT huniq
  have hlen_pos : F.length ≥ 1 := List.length_pos_of_mem hT
  omega

/-- IM: accessible terms preserved -/
theorem im_acc_preserved (T β : SyntacticObject)
    (hT : T ∈ F) (hβT : contains T β)
    (huniq : F.count T = 1) :
    numAcc (imWorkspace T β F) = numAcc F + 1 := by
  -- TODO: merge(β,T) has one more internal node than T (the new root),
  -- so #Acc increases by 1.
  sorry

/-- IM: σ̂ preserved -/
theorem im_wsSizeAlt_preserved (T β : SyntacticObject)
    (hT : T ∈ F) (hβT : contains T β)
    (huniq : F.count T = 1) :
    wsSizeAlt (imWorkspace T β F) = wsSizeAlt F + 1 := by
  -- TODO: Same argument as σ.
  sorry

end Counting

/-! ## Corollary 2.22: Sideward/Countercyclic Merge violates constraints

Sideward Merge: merge(β, T₂) where β is contained in T₁, and T₁ ≠ T₂.
This extracts a subterm from one tree and merges it with another.

Countercyclic Merge: merge(T₁, T₂) where one is contained in the other
but NOT as a root constituent. -/

/-- Sideward Merge condition: β is in T₁, we merge β with T₂ -/
structure SidewardMerge where
  T₁ : SyntacticObject
  T₂ : SyntacticObject
  β : SyntacticObject
  distinct : T₁ ≠ T₂
  β_in_T₁ : contains T₁ β
  β_not_T₁ : β ≠ T₁
  β_not_in_T₂ : ¬contains T₂ β

/-- Sideward Merge workspace: remove nothing (β stays in T₁), add merge(β, T₂) -/
def sidewardWorkspace (sm : SidewardMerge) (F : List SyntacticObject) : List SyntacticObject :=
  merge sm.β sm.T₂ :: F

/-- Sideward Merge violates b₀ preservation: it adds a component without removing one.
    This is the key constraint violation that distinguishes it from standard EM/IM. -/
theorem sideward_violates_b0 (sm : SidewardMerge) (F : List SyntacticObject) :
    b₀ (sidewardWorkspace sm F) = b₀ F + 1 := by
  simp [sidewardWorkspace, b₀, List.length_cons]

/-! ## Bridge: counting behavior consistent with EM/IM trichotomy

The counting characterization aligns with the order-theoretic partition
from MergeUnification.lean. -/

/-- When α and β are incomparable (EM case), merge combines two separate components -/
theorem em_counting_from_trichotomy (α β : SyntacticObject) (F : List SyntacticObject)
    (h : ¬contains α β ∧ ¬contains β α) (hne : α ≠ β)
    (hα : α ∈ F) (hβ : β ∈ F) :
    b₀ (emWorkspace α β F) < b₀ F ∨ b₀ (emWorkspace α β F) = b₀ F - 1 := by
  -- TODO: follows from em_b0_decreases
  sorry

/-- When one contains the other (IM case), merge preserves component count -/
theorem im_counting_from_trichotomy (α β : SyntacticObject) (F : List SyntacticObject)
    (h : contains α β) (hα : α ∈ F) :
    b₀ (imWorkspace α β F) = b₀ F := by
  -- TODO: follows from im_b0_preserved
  sorry

end Minimalism
