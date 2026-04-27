/-
# Workspace Counting and Accessible Terms

Counting invariants of Merge on workspaces, following
@cite{marcolli-chomsky-berwick-2025}: accessible terms, workspace size
functions (b₀, σ, σ̂), and the counting behavior that distinguishes
External Merge, Internal Merge, and Sideward Merge.

## Main definitions

- `subtrees`, `properSubtrees`: subtree extraction
- `leafMultiset`: frontier tokens of an SO
- `accessibleTerms`: leaf-sets of subtrees at internal nodes
- `b₀`, `numAcc`, `wsSize`, `wsSizeAlt`: workspace counting
- `emWorkspace`, `imWorkspace`: workspace transformations for EM/IM

## Main results

- `em_b0_decreases` / `em_acc_increases` / `em_wsSize_change`: EM counting (Δσ = +1)
- `im_b0_preserved` / `im_acc_change`: IM counting (Δα = 1 + β.nodeCount)
- `sideward_violates_b0`: Sideward Merge violates counting constraints

-/

import Linglib.Theories.Syntax.Minimalism.Algebra
import Mathlib.Data.Multiset.Basic

namespace Minimalism

/-! ## Subtree extraction

`SyntacticObject.subtrees` is defined in `Core.Basic`. We add proper subtrees
and internal node enumeration here. -/

/-- Proper subtrees (excluding self) -/
def SyntacticObject.properSubtrees : SyntacticObject → List SyntacticObject
  | .leaf _ => []
  | .node a b => a.subtrees ++ b.subtrees

/-- Internal nodes (subtrees that are.node) -/
def SyntacticObject.internalNodes : SyntacticObject → List SyntacticObject
  | .leaf _ => []
  | so@(.node a b) => so :: (a.internalNodes ++ b.internalNodes)

/-- Internal node count (= nodeCount from SyntacticObjects.lean) -/
theorem internalNodes_length_eq_nodeCount (so : SyntacticObject) :
    so.internalNodes.length = so.nodeCount := by
  induction so with
  | leaf _ => rfl
  | node a b iha ihb =>
    simp [SyntacticObject.internalNodes, SyntacticObject.nodeCount, List.length_cons,
          List.length_append, iha, ihb]
    omega

/-! ## Leaf multisets (frontier tokens) -/

/-- The multiset of leaf tokens at the frontier of an SO -/
def SyntacticObject.leafMultiset : SyntacticObject → List LIToken
  | .leaf tok => [tok]
  | .node a b => a.leafMultiset ++ b.leafMultiset

theorem leafMultiset_length_eq_leafCount (so : SyntacticObject) :
    so.leafMultiset.length = so.leafCount := by
  induction so with
  | leaf _ => rfl
  | node a b iha ihb =>
    simp [SyntacticObject.leafMultiset, SyntacticObject.leafCount, List.length_append,
          iha, ihb]

/-- Leaf multiset as a `Multiset` — the mathematically correct type
    (frontier token identity is order-independent). -/
def SyntacticObject.leafMultisetM (so : SyntacticObject) : Multiset LIToken :=
  ↑so.leafMultiset

/-! ## Accessible terms (Definition 1.2.2)

For a tree T, the accessible terms are the leaf-sets of subtrees
rooted at internal nodes: Acc(T) = {L(T_v) | v ∈ V_int(T)}.
That is, for each internal node v, we take L(T_v) = the leaf
multiset of the subtree rooted at v. -/

/-- Accessible terms: leaf-multisets of subtrees at internal nodes -/
def SyntacticObject.accessibleTerms : SyntacticObject → List (List LIToken)
  | .leaf _ => []
  | so@(.node a b) => so.leafMultiset :: (a.accessibleTerms ++ b.accessibleTerms)

/-- Proper accessible terms: accessible terms excluding the tree's own root.

    When a tree is a workspace member, its root is a "member" counted by b₀,
    not an accessible term counted by α (§1.2, Proposition 1.6.4). -/
def SyntacticObject.properAccessibleTerms : SyntacticObject → List (List LIToken)
  | .leaf _ => []
  | .node a b => a.accessibleTerms ++ b.accessibleTerms

/-- Accessible terms as `Multiset` of `Multiset`s — order-independent identity. -/
def SyntacticObject.accessibleTermsM (so : SyntacticObject) : Multiset (Multiset LIToken) :=
  ↑(so.accessibleTerms.map (↑· : List LIToken → Multiset LIToken))

/-- Number of accessible terms = number of internal nodes -/
theorem accessibleTerms_length_eq_nodeCount (so : SyntacticObject) :
    so.accessibleTerms.length = so.nodeCount := by
  induction so with
  | leaf _ => rfl
  | node a b iha ihb =>
    simp [SyntacticObject.accessibleTerms, SyntacticObject.nodeCount, List.length_cons,
          List.length_append, iha, ihb]
    omega

/-- Proper accessible terms length = nodeCount - 1 (Nat subtraction).
    For leaves: 0 = 0. For nodes with n ≥ 1 internal nodes: n - 1. -/
theorem properAccessibleTerms_length_eq (so : SyntacticObject) :
    so.properAccessibleTerms.length = so.nodeCount - 1 := by
  match so with
  | .leaf _ => simp [SyntacticObject.properAccessibleTerms, SyntacticObject.nodeCount]
  | .node a b =>
    simp [SyntacticObject.properAccessibleTerms, SyntacticObject.nodeCount,
          List.length_append, accessibleTerms_length_eq_nodeCount]
    omega

/-! ## Workspace counting (§1.2, §1.6)

A workspace (forest) is a list of SOs = the connected components.

Following @cite{marcolli-chomsky-berwick-2025} Proposition 1.6.4:
σ = b₀ + α where α counts *proper* accessible terms (excluding each
tree's root, which is a "member" counted by b₀). Under this convention,
EM on non-leaf inputs gives Δα = +2, Δσ = +1. -/

/-- b₀(F): number of connected components = List.length -/
def b₀ (F : List SyntacticObject) : Nat := F.length

/-- α(F): proper accessible terms across all workspace members (§1.2).

    Each tree's root is a "member" counted by b₀, not an accessible term.
    Only proper subtrees at internal nodes contribute to α. -/
def numAcc (F : List SyntacticObject) : Nat :=
  (F.map (·.properAccessibleTerms.length)).sum

/-- σ(F) = b₀(F) + α(F) (Proposition 1.6.4) -/
def wsSize (F : List SyntacticObject) : Nat := b₀ F + numAcc F

/-- Total internal nodes across all trees in forest -/
def numVertices (F : List SyntacticObject) : Nat :=
  (F.map (·.nodeCount)).sum

/-- σ̂(F) = b₀(F) + #V(F) — alternative size counting all internal nodes -/
def wsSizeAlt (F : List SyntacticObject) : Nat := b₀ F + numVertices F

/-! ## Depth of a subtree occurrence -/

/-- Depth of β in α (0 if β = α, +1 per level) -/
def SyntacticObject.depthOf (α β : SyntacticObject) : Option Nat :=
  if decide (α = β) then some 0
  else match α with
    | .leaf _ => none
    | .node l r =>
      match l.depthOf β, r.depthOf β with
      | some d, _ => some (d + 1)
      | _, some d => some (d + 1)
      | none, none => none

/-! ## Counting behavior of EM vs IM (Proposition 1.6.4)

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
      have hbne_false : (hd != x) = false := by simp [heq]
      simp only [hbne_false]
      -- count (hd :: tl) x = 1, hd = x, so tl.count x = 0
      have hc' : tl.count x = 0 := by
        rw [heq] at hc
        simp only [List.count_cons_self] at hc
        omega
      -- So filter (· != x) on tl = tl
      have hfilt : tl.filter (· != x) = tl := by
        rw [List.filter_eq_self]
        intro a ha
        simp only [bne_iff_ne, ne_eq]
        intro heqa; subst heqa
        exact absurd (List.count_pos_iff.mpr ha) (by omega)
      rw [hfilt]
      simp [List.length]
    · -- hd ≠ x: this element is kept
      have hbne_true : (hd != x) = true := by simp [heq]
      simp only [hbne_true, List.length_cons]
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

/-- An element of a Nat list is ≤ the list's sum -/
private theorem mem_le_sum {L : List Nat} {x : Nat} (hx : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · have := ih h; omega

/-- Filtering out a unique element reduces the mapped sum by f(x).
    Uses Nat subtraction so requires the ≤ side condition. -/
private theorem sum_map_filter_bne_of_count_one {α : Type*} [DecidableEq α]
    (L : List α) (x : α) (f : α → Nat) (hx : x ∈ L) (hc : L.count x = 1) :
    (L.map f).sum = ((L.filter (· != x)).map f).sum + f x := by
  induction L with
  | nil => simp at hx
  | cons hd tl ih =>
    simp only [List.filter, List.map_cons, List.sum_cons]
    by_cases heq : hd = x
    · have hbne_false : (hd != x) = false := by simp [heq]
      simp only [hbne_false, ite_false]
      have hc' : tl.count x = 0 := by
        rw [heq] at hc; simp only [List.count_cons_self] at hc; omega
      have hfilt : tl.filter (· != x) = tl := by
        rw [List.filter_eq_self]
        intro a ha; simp only [bne_iff_ne, ne_eq]
        intro heqa; subst heqa
        exact absurd (List.count_pos_iff.mpr ha) (by omega)
      rw [hfilt, heq]; omega
    · have hbne_true : (hd != x) = true := by simp [heq]
      simp only [hbne_true, ite_true, List.map_cons, List.sum_cons]
      have hx' : x ∈ tl := by
        rcases List.mem_cons.mp hx with rfl | h
        · exact absurd rfl heq
        · exact h
      have hc' : tl.count x = 1 := by
        rw [List.count_cons] at hc; simp [beq_iff_eq, heq] at hc; exact hc
      have := ih hx' hc'
      omega

/-- numAcc of a cons list -/
private theorem numAcc_cons (t : SyntacticObject) (ts : List SyntacticObject) :
    numAcc (t :: ts) = t.properAccessibleTerms.length + numAcc ts := by
  simp [numAcc, List.map_cons, List.sum_cons]

/-- Filtering out a unique element reduces numAcc by that element's contribution -/
private theorem numAcc_filter_bne {F : List SyntacticObject} {T : SyntacticObject}
    (hT : T ∈ F) (huniq : F.count T = 1) :
    numAcc F = numAcc (F.filter (· != T)) + T.properAccessibleTerms.length := by
  simp only [numAcc]
  exact sum_map_filter_bne_of_count_one F T (·.properAccessibleTerms.length) hT huniq

/-- numVertices of a cons list -/
private theorem numVertices_cons (t : SyntacticObject) (ts : List SyntacticObject) :
    numVertices (t :: ts) = t.nodeCount + numVertices ts := by
  simp [numVertices, List.map_cons, List.sum_cons]

/-- Filtering out a unique element from a forest reduces numVertices by that element's nodeCount -/
private theorem numVertices_filter_bne {F : List SyntacticObject} {T : SyntacticObject}
    (hT : T ∈ F) (huniq : F.count T = 1) :
    numVertices F = numVertices (F.filter (· != T)) + T.nodeCount := by
  simp only [numVertices]
  exact sum_map_filter_bne_of_count_one F T (·.nodeCount) hT huniq

section Counting

variable {F : List SyntacticObject}

/-- External Merge: workspace goes from F to F' where T₁,T₂ ∈ F replaced by merge(T₁,T₂) -/
def emWorkspace (T₁ T₂ : SyntacticObject) (F : List SyntacticObject) : List SyntacticObject :=
  merge T₁ T₂ :: F.filter (· != T₁) |>.filter (· != T₂)

/-- Internal Merge: workspace goes from F to F' where T ∈ F replaced by merge(β, T) -/
def imWorkspace (T β : SyntacticObject) (F : List SyntacticObject) : List SyntacticObject :=
  merge β T :: F.filter (· != T)

/-- merge(T₁, T₂) = node T₁ T₂ is strictly larger than T₂ -/
private theorem merge_ne_right (T₁ T₂ : SyntacticObject) : merge T₁ T₂ ≠ T₂ := by
  intro heq
  have h : (merge T₁ T₂).nodeCount = T₂.nodeCount := by rw [heq]
  have hexpand : (merge T₁ T₂).nodeCount = 1 + T₁.nodeCount + T₂.nodeCount := rfl
  omega

/-- External Merge on workspaces produces a workspace containing merge(T₁, T₂).
    Migrated from legacy `Hopf.Coproduct.lean` to live with the
    `emWorkspace` definition. -/
theorem em_contains_merge (T₁ T₂ : SyntacticObject)
    (F : List SyntacticObject) :
    merge T₁ T₂ ∈ emWorkspace T₁ T₂ F := by
  simp only [emWorkspace]
  rw [List.filter_cons, if_pos (by simp [bne_iff_ne, merge_ne_right])]
  exact List.Mem.head _

/-- Internal Merge on workspaces produces a workspace containing merge(β, T).
    Migrated from legacy `Hopf.Coproduct.lean`. -/
theorem im_contains_merge (T β : SyntacticObject)
    (F : List SyntacticObject) :
    merge β T ∈ imWorkspace T β F := by
  simp [imWorkspace]

/-- Filtering out x preserves the count of y when x ≠ y. -/
private theorem count_filter_bne_of_ne {α : Type*} [DecidableEq α]
    (L : List α) (x y : α) (hne : x ≠ y) :
    (L.filter (· != x)).count y = L.count y := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter]
    by_cases heq : hd = x
    · simp only [show (hd != x) = false from by simp [heq]]
      rw [List.count_cons]; simp [beq_iff_eq, heq ▸ hne, ih]
    · simp only [show (hd != x) = true from by simp [heq]]
      rw [List.count_cons, List.count_cons, ih]

/-- Filtering out x preserves membership of y when x ≠ y. -/
private theorem mem_filter_bne_of_ne {α : Type*} [DecidableEq α]
    (L : List α) (x y : α) (hne : x ≠ y) (hy : y ∈ L) :
    y ∈ L.filter (· != x) := by
  rw [List.mem_filter]
  exact ⟨hy, by simp [bne_iff_ne, Ne.symm hne]⟩

/-- EM: b₀ decreases by 1 (two components become one) -/
theorem em_b0_decreases (T₁ T₂ : SyntacticObject)
    (hT₁ : T₁ ∈ F) (hT₂ : T₂ ∈ F) (hne : T₁ ≠ T₂)
    (huniq₁ : F.count T₁ = 1) (huniq₂ : F.count T₂ = 1) :
    b₀ (emWorkspace T₁ T₂ F) = b₀ F - 1 := by
  -- merge T₁ T₂ = node T₁ T₂ is strictly larger than T₂ (and T₁)
  have hne_merge₂ : merge T₁ T₂ ≠ T₂ := by
    intro heq
    have h : (merge T₁ T₂).nodeCount = T₂.nodeCount := by rw [heq]
    have hexpand : (merge T₁ T₂).nodeCount = 1 + T₁.nodeCount + T₂.nodeCount := rfl
    omega
  have hne_merge₁ : merge T₁ T₂ ≠ T₁ := by
    intro heq
    have h : (merge T₁ T₂).nodeCount = T₁.nodeCount := by rw [heq]
    have hexpand : (merge T₁ T₂).nodeCount = 1 + T₁.nodeCount + T₂.nodeCount := rfl
    omega
  simp only [emWorkspace, b₀]
  -- Unfold the outer filter on the cons cell
  rw [List.filter_cons,
      if_pos (by simp [bne_iff_ne, hne_merge₂]), List.length_cons]
  -- Now goal: 1 + ((F.filter (· != T₁)).filter (· != T₂)).length = F.length - 1
  have h1 := length_filter_bne_of_count_one F T₁ hT₁ huniq₁
  have hT₂' := mem_filter_bne_of_ne F T₁ T₂ hne hT₂
  have hc₂' : (F.filter (· != T₁)).count T₂ = 1 := by
    rw [count_filter_bne_of_ne F T₁ T₂ hne]; exact huniq₂
  have h2 := length_filter_bne_of_count_one (F.filter (· != T₁)) T₂ hT₂' hc₂'
  have hlen₁ : F.length ≥ 1 := List.length_pos_of_mem hT₁
  have hlen₂ : (F.filter (· != T₁)).length ≥ 1 := List.length_pos_of_mem hT₂'
  omega

/-- EM: α increases by 2 when both inputs are non-leaf (Proposition 1.6.4).

    T₁ and T₂ were workspace "members" (counted by b₀) whose roots were
    excluded from α. After merge, they become non-root internal nodes of
    the merged tree, each contributing one new proper accessible term. -/
theorem em_acc_increases (T₁ T₂ : SyntacticObject)
    (hT₁ : T₁ ∈ F) (hT₂ : T₂ ∈ F) (hne : T₁ ≠ T₂)
    (huniq₁ : F.count T₁ = 1) (huniq₂ : F.count T₂ = 1)
    (hnode₁ : T₁.nodeCount ≥ 1) (hnode₂ : T₂.nodeCount ≥ 1) :
    numAcc (emWorkspace T₁ T₂ F) = numAcc F + 2 := by
  have hne_merge₂ : merge T₁ T₂ ≠ T₂ := by
    intro heq
    have h : (merge T₁ T₂).nodeCount = T₂.nodeCount := by rw [heq]
    have hexpand : (merge T₁ T₂).nodeCount = 1 + T₁.nodeCount + T₂.nodeCount := rfl
    omega
  simp only [emWorkspace]
  rw [List.filter_cons, if_pos (by simp [bne_iff_ne, hne_merge₂])]
  rw [numAcc_cons]
  -- merge(T₁,T₂).properAccessibleTerms = T₁.accessibleTerms ++ T₂.accessibleTerms
  simp only [merge, SyntacticObject.properAccessibleTerms, List.length_append]
  rw [accessibleTerms_length_eq_nodeCount, accessibleTerms_length_eq_nodeCount]
  -- numAcc F = T₁.proper + T₂.proper + rest
  have h1 := numAcc_filter_bne hT₁ huniq₁
  have hT₂' := mem_filter_bne_of_ne F T₁ T₂ hne hT₂
  have hc₂' : (F.filter (· != T₁)).count T₂ = 1 := by
    rw [count_filter_bne_of_ne F T₁ T₂ hne]; exact huniq₂
  have h2 := numAcc_filter_bne hT₂' hc₂'
  simp only [properAccessibleTerms_length_eq] at h1 h2
  omega

/-- EM: σ increases by 1 (Δb₀ = -1, Δα = +2, net Δσ = +1).

    Proposition 1.6.4: EM on non-leaf inputs is strictly size-increasing. -/
theorem em_wsSize_change (T₁ T₂ : SyntacticObject)
    (hT₁ : T₁ ∈ F) (hT₂ : T₂ ∈ F) (hne : T₁ ≠ T₂)
    (huniq₁ : F.count T₁ = 1) (huniq₂ : F.count T₂ = 1)
    (hnode₁ : T₁.nodeCount ≥ 1) (hnode₂ : T₂.nodeCount ≥ 1) :
    wsSize (emWorkspace T₁ T₂ F) = wsSize F + 1 := by
  simp only [wsSize]
  have hb := em_b0_decreases T₁ T₂ hT₁ hT₂ hne huniq₁ huniq₂
  have ha := em_acc_increases T₁ T₂ hT₁ hT₂ hne huniq₁ huniq₂ hnode₁ hnode₂
  simp only [b₀] at hb ⊢
  have hlen_pos : F.length ≥ 1 := List.length_pos_of_mem hT₁
  omega

/-- IM: b₀ preserved (same number of components) -/
theorem im_b0_preserved (T β : SyntacticObject)
    (hT : T ∈ F) (_hβT : contains T β)
    (huniq : F.count T = 1) :
    b₀ (imWorkspace T β F) = b₀ F := by
  simp only [imWorkspace, b₀, List.length_cons]
  have := length_filter_bne_of_count_one F T hT huniq
  have hlen_pos : F.length ≥ 1 := List.length_pos_of_mem hT
  omega

/-- IM: α increases by 1 + β.nodeCount.

    merge(β, T) = node β T, replacing T in the workspace.
    The merged tree's proper accessible terms are β.accessibleTerms ++ T.accessibleTerms.
    Since T's proper contribution was T.nodeCount - 1, the net change is
    β.nodeCount + 1. Note: β's subtree is duplicated (it remains inside T
    and also appears as a new child of the root). -/
theorem im_acc_change (T β : SyntacticObject)
    (hT : T ∈ F) (_hβT : contains T β)
    (huniq : F.count T = 1)
    (hnodeT : T.nodeCount ≥ 1) :
    numAcc (imWorkspace T β F) = numAcc F + 1 + β.nodeCount := by
  simp only [imWorkspace]
  rw [numAcc_cons]
  -- merge(β,T).properAccessibleTerms = β.accessibleTerms ++ T.accessibleTerms
  simp only [merge, SyntacticObject.properAccessibleTerms, List.length_append]
  rw [accessibleTerms_length_eq_nodeCount, accessibleTerms_length_eq_nodeCount]
  have h1 := numAcc_filter_bne hT huniq
  rw [properAccessibleTerms_length_eq] at h1
  omega

/-- IM: σ̂ increases by 1 + β.nodeCount.

    wsSizeAlt = b₀ + numVertices. Under IM, b₀ is preserved and
    numVertices increases by 1 + β.nodeCount. -/
theorem im_wsSizeAlt_change (T β : SyntacticObject)
    (hT : T ∈ F) (_hβT : contains T β)
    (huniq : F.count T = 1) :
    wsSizeAlt (imWorkspace T β F) = wsSizeAlt F + 1 + β.nodeCount := by
  simp only [wsSizeAlt, imWorkspace, b₀, List.length_cons]
  rw [numVertices_cons]
  simp only [merge, SyntacticObject.nodeCount]
  have h1 := numVertices_filter_bne hT huniq
  have hlen := length_filter_bne_of_count_one F T hT huniq
  have hlen_pos : F.length ≥ 1 := List.length_pos_of_mem hT
  omega

end Counting

/-! ## Sideward/Countercyclic Merge violates constraints (§1.4, §1.6)

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

/-- When α and β are incomparable (EM case), merge reduces component count by 1.
    Requires uniqueness of α and β in F (each appears exactly once). -/
theorem em_counting_from_trichotomy (α β : SyntacticObject) (F : List SyntacticObject)
    (_h : ¬contains α β ∧ ¬contains β α) (hne : α ≠ β)
    (hα : α ∈ F) (hβ : β ∈ F)
    (huniqα : F.count α = 1) (huniqβ : F.count β = 1) :
    b₀ (emWorkspace α β F) = b₀ F - 1 :=
  em_b0_decreases α β hα hβ hne huniqα huniqβ

/-- When one contains the other (IM case), merge preserves component count.
    Requires uniqueness of α in F. -/
theorem im_counting_from_trichotomy (α β : SyntacticObject) (F : List SyntacticObject)
    (h : contains α β) (hα : α ∈ F)
    (huniq : F.count α = 1) :
    b₀ (imWorkspace α β F) = b₀ F :=
  im_b0_preserved α β hα h huniq

end Minimalism
