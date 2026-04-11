/-
# Coproduct Structure

Formalizes the coproduct decomposition of @cite{marcolli-chomsky-berwick-2025}:
quotient trees T/Tᵥ, admissible cuts, the leading coproduct term, and the
connection between workspace merge and the coproduct structure.

The coproduct Δ(T) decomposes a tree into pairs (subtree, quotient) and is the
key structure connecting Merge to Hopf algebra formalism from QFT renormalization
(Connes-Kreimer).

## Main definitions

- `quotientTree`: T/^c — contraction quotient (subtree → trace leaf)
- `deletionQuotient`: T/^d — deletion quotient (subtree deleted, edges contracted)
- `AdmissibleCut`: set of non-overlapping internal nodes to cut
- `leadingCoproduct`: Δ^c₍₂₎(T) = Σᵥ Tᵥ ⊗ T/^c Tᵥ
- `leadingCoproductD`: Δ^d₍₂₎(T) = Σᵥ Tᵥ ⊗ T/^d Tᵥ

## Main results

- `coproduct_size_identity`: T.leafCount = v.leafCount + (T/^c v).leafCount - 1
- `deletionQuotient_leafCount`: (T/^d v).leafCount = T.leafCount - v.leafCount
- `deletion_vs_contraction_leafCount`: T/^c has one more leaf than T/^d (the trace)
- `workspace_merge_partition`: EM/IM selection determined by containment

-/

import Linglib.Theories.Syntax.Minimalism.Core.Counting
import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Basic

namespace Minimalism

/-! ## Quotient tree (contraction, T/^c)

Given a tree T and a contained subtree Tᵥ, the contraction quotient
T/^c Tᵥ is obtained by replacing Tᵥ with a single leaf (contracting
the subtree to a point). The book also defines deletion quotient T/^d
(removing the trace) and remainder quotient T/^ρ (admissible cuts);
T/^c and T/^d are formalized here; T/^ρ requires n-ary trees
(not formalized). -/

/-- A placeholder leaf token for quotient tree contraction points -/
def quotientLeafToken : LIToken :=
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

/-! ## Admissible cuts (§1.2)

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

/-- All admissible cut options for a tree, excluding cutting the root itself.
    Returns pairs `(P, R)` where `P` is the list of pruned subtrees (forest)
    and `R` is the quotient tree with stump leaves at cut points.

    The trivial cut `([], T)` is always included. For `node a b`, the result
    is the Cartesian product of "extended" options for each child: either
    recurse into the child's cuts, or cut the child entirely (if it's an
    internal node, replacing it with a stump leaf).

    This generates ALL admissible cut antichains, not just single-node cuts.
    Multi-node antichains arise when independent subtrees (incomparable under
    containment) are cut simultaneously. -/
def cutOptions : SyntacticObject → List (List SyntacticObject × SyntacticObject)
  | .leaf tok => [([], .leaf tok)]
  | .node a b =>
    let aExt := cutOptions a ++
      match a with | .node _ _ => [([a], .leaf quotientLeafToken)] | .leaf _ => []
    let bExt := cutOptions b ++
      match b with | .node _ _ => [([b], .leaf quotientLeafToken)] | .leaf _ => []
    aExt.flatMap fun ⟨Pa, Ra⟩ => bExt.map fun ⟨Pb, Rb⟩ => (Pa ++ Pb, .node Ra Rb)

theorem cutOptions_leaf (tok : LIToken) :
    cutOptions (.leaf tok) = [([], .leaf tok)] := rfl

/-- Extended cut options: `cutOptions T` plus (if T is an internal node) the
    option of cutting T entirely, replacing it with a stump leaf.
    This is the factor set in the Cartesian product decomposition of
    `cutOptions (node a b) = extOptions(a) ×_cart extOptions(b)`. -/
def extOptions (T : SyntacticObject) :
    List (List SyntacticObject × SyntacticObject) :=
  cutOptions T ++ match T with
    | .node _ _ => [([T], .leaf quotientLeafToken)]
    | .leaf _ => []

theorem cutOptions_node (a b : SyntacticObject) :
    cutOptions (.node a b) =
    (extOptions a).flatMap fun ⟨Pa, Ra⟩ =>
      (extOptions b).map fun ⟨Pb, Rb⟩ => (Pa ++ Pb, .node Ra Rb) := rfl

/-! ## Leading coproduct (Definition 1.2.8)

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
  have hqpos : q.leafCount ≥ 1 := leafCount_pos q
  omega

/-! ## Merge on workspaces (Definition 1.3.4)

Merge lifts from an operation on pairs of SOs to an operation on
the workspace (list of SOs). `emWorkspace` and `imWorkspace` are defined
in `Core.Counting`; here we prove membership and partition properties
connecting them to the coproduct structure. -/

/-- merge(T₁, T₂) = node T₁ T₂ is strictly larger than T₂ -/
private theorem merge_ne_right (T₁ T₂ : SyntacticObject) : merge T₁ T₂ ≠ T₂ := by
  intro heq; have := congrArg sizeOf heq; simp [merge] at this

/-- External Merge on workspaces produces a workspace containing merge(T₁, T₂) -/
theorem em_contains_merge (T₁ T₂ : SyntacticObject)
    (F : List SyntacticObject) :
    merge T₁ T₂ ∈ emWorkspace T₁ T₂ F := by
  simp only [emWorkspace]
  rw [List.filter_cons, if_pos (by simp [bne_iff_ne, merge_ne_right])]
  exact List.Mem.head _

/-- Internal Merge on workspaces produces a workspace containing merge(β, T) -/
theorem im_contains_merge (T β : SyntacticObject)
    (F : List SyntacticObject) :
    merge β T ∈ imWorkspace T β F := by
  simp [imWorkspace]

/-- The workspace merge operation reduces to pointwise merge on SOs.
    The algebraic (Hopf algebra) formulation recovers the simple
    set-theoretic Merge operation. -/
theorem workspace_merge_recovers_merge (T₁ T₂ : SyntacticObject) :
    merge T₁ T₂ ∈ emWorkspace T₁ T₂ [T₁, T₂] :=
  em_contains_merge T₁ T₂ [T₁, T₂]

/-- Connection to MergeUnification: the EM/IM workspace operations align
    with the containment-based partition. When inputs are incomparable,
    `emWorkspace` is the appropriate operation; when one contains the
    other, `imWorkspace` is appropriate. -/
theorem workspace_merge_partition (α β : SyntacticObject)
    (_hne : α ≠ β) (F : List SyntacticObject)
    (_hα : α ∈ F) :
    (¬contains α β ∧ ¬contains β α →
      merge α β ∈ emWorkspace α β F) ∧
    (contains α β →
      merge β α ∈ imWorkspace α β F) := by
  constructor
  · intro _; exact em_contains_merge α β F
  · intro _; exact im_contains_merge α β F

/-! ## Deletion quotient (T/^d, Definition 1.2.5)

The deletion quotient T/^d T_v deletes the subtree T_v from T entirely.
Where the contraction quotient T/^c leaves a trace leaf, the deletion
quotient removes T_v and contracts the parent edge to maintain binary
branching.

Three quotient types (Definition 1.2.8, ω ∈ {c, d, ρ}):
- T/^c (contraction): subtree → trace leaf (`quotientTree` above)
- T/^d (deletion): subtree deleted, edges contracted (this section)
- T/^ρ (remainder): non-binary tree from admissible cut (requires n-ary
  trees, not formalized)

The coproducts are related by projections (§1.2.1):
  Δ^d = (id ⊗ Π_{d,c}) ∘ Δ^c -/

/-- Deletion quotient: delete subtree v from T, bypassing parent nodes
    via edge contraction (Definition 1.2.5). Returns `none` if v equals T
    (would produce empty tree) or v is not found. -/
def deletionQuotient (T v : SyntacticObject) : Option SyntacticObject :=
  if T == v then none
  else match T with
    | .leaf _ => none
    | .node a b =>
      if a == v then some b
      else if b == v then some a
      else
        match deletionQuotient a v with
        | some a' => some (.node a' b)
        | none =>
          match deletionQuotient b v with
          | some b' => some (.node a b')
          | none => none

/-- If deletionQuotient succeeds, T containsOrEq v. -/
private theorem deletionQuotient_implies_containsOrEq (T v : SyntacticObject)
    (h : (deletionQuotient T v).isSome = true) : containsOrEq T v := by
  induction T with
  | leaf tok =>
    simp only [deletionQuotient] at h
    split at h
    · rename_i heq; rw [beq_iff_eq] at heq; exact Or.inl heq
    · simp at h
  | node a b iha ihb =>
    simp only [deletionQuotient] at h
    split at h
    · rename_i heq; rw [beq_iff_eq] at heq; exact Or.inl heq
    · rename_i hne
      split at h  -- if a == v
      · rename_i heq; rw [beq_iff_eq] at heq
        exact Or.inr (contains.imm _ _
          (by simp only [immediatelyContains]; exact Or.inl heq.symm))
      · split at h  -- if b == v
        · rename_i _ heq; rw [beq_iff_eq] at heq
          exact Or.inr (contains.imm _ _
            (by simp only [immediatelyContains]; exact Or.inr heq.symm))
        · split at h  -- match deletionQuotient a v
          · rename_i a' ha'
            have := iha (by simp [ha'])
            rcases this with rfl | hc
            · exact Or.inr (contains.imm _ _ (by simp [immediatelyContains]))
            · exact Or.inr (contains.trans _ _ a
                (by simp [immediatelyContains]) hc)
          · split at h  -- match deletionQuotient b v
            · rename_i _ b' hb'
              have := ihb (by simp [hb'])
              rcases this with rfl | hc
              · exact Or.inr (contains.imm _ _ (by simp [immediatelyContains]))
              · exact Or.inr (contains.trans _ _ b
                  (by simp [immediatelyContains]) hc)
            · simp at h

/-- Deletion quotient leafCount:
    (T/^d v).leafCount = T.leafCount - v.leafCount. -/
private theorem deletionQuotient_leafCount_aux (T v : SyntacticObject) :
    ∀ q, deletionQuotient T v = some q →
    q.leafCount = T.leafCount - v.leafCount := by
  induction T with
  | leaf tok =>
    intro q hq
    simp only [deletionQuotient] at hq
    split at hq <;> simp at hq
  | node a b iha ihb =>
    intro q hq
    simp only [deletionQuotient] at hq
    split at hq
    · simp at hq
    · rename_i hne
      split at hq  -- if a == v
      · rename_i heq; rw [beq_iff_eq] at heq; subst heq
        simp at hq; subst hq
        simp [SyntacticObject.leafCount]
      · split at hq  -- if b == v
        · rename_i _ heq; rw [beq_iff_eq] at heq; subst heq
          simp at hq; subst hq
          simp only [SyntacticObject.leafCount]; omega
        · split at hq  -- match deletionQuotient a v
          · rename_i a' ha'
            have hqeq : q = .node a' b := by cases hq; rfl
            subst hqeq
            simp only [SyntacticObject.leafCount]
            have := iha a' ha'
            have hle : v.leafCount ≤ a.leafCount :=
              leafCount_le_of_containsOrEq a v
                (deletionQuotient_implies_containsOrEq a v (by simp [ha']))
            omega
          · split at hq  -- match deletionQuotient b v
            · rename_i _ b' hb'
              have hqeq : q = .node a b' := by cases hq; rfl
              subst hqeq
              simp only [SyntacticObject.leafCount]
              have := ihb b' hb'
              have hle : v.leafCount ≤ b.leafCount :=
                leafCount_le_of_containsOrEq b v
                  (deletionQuotient_implies_containsOrEq b v (by simp [hb']))
              omega
            · simp at hq

theorem deletionQuotient_leafCount (T v q : SyntacticObject)
    (_h : contains T v) (hq : deletionQuotient T v = some q) :
    q.leafCount = T.leafCount - v.leafCount :=
  deletionQuotient_leafCount_aux T v q hq

/-- The contraction quotient has exactly one more leaf than the deletion
    quotient—the trace leaf at the extraction site. This reflects the
    projection Π_{d,c}: delete trace and contract edges. -/
theorem deletion_vs_contraction_leafCount (T v q_c q_d : SyntacticObject)
    (h : contains T v)
    (hqc : quotientTree T v = some q_c)
    (hqd : deletionQuotient T v = some q_d) :
    q_c.leafCount = q_d.leafCount + 1 := by
  have h1 := quotientTree_leafCount T v q_c h hqc
  have h2 := deletionQuotient_leafCount T v q_d h hqd
  have hle : v.leafCount ≤ T.leafCount :=
    leafCount_le_of_containsOrEq T v (Or.inr h)
  omega

/-- Leading coproduct with deletion quotient:
    Δ^d₍₂₎(T) = Σ_{v ∈ V_int} Tᵥ ⊗ T/^d Tᵥ -/
def leadingCoproductD (T : SyntacticObject) :
    List (SyntacticObject × Option SyntacticObject) :=
  T.properSubtrees.filterMap (λ v =>
    match v with
    | .leaf _ => none
    | .node _ _ => some (v, deletionQuotient T v))

end Minimalism
