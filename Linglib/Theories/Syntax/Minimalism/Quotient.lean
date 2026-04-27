import Linglib.Theories.Syntax.Minimalism.Counting

/-!
# Quotient Tree (Contraction)
@cite{marcolli-chomsky-berwick-2025}

The "contraction quotient" `T/^c v` from M-C-B Definition 1.2.4
applied at a single accessible term `v ⊂ T`: replace the first
occurrence of `v` in `T` with a trace stub leaf.

This file extracts the core `quotientTree` operation and its leaf-
count theorem from the legacy `Hopf/Coproduct.lean`, breaking the
dependency on the legacy Hopf substrate. Used by
`Properties/NoComplexityLoss.lean` to bound the degree change of
quotient operations.

The new Hopf substrate (`Hopf/AdmissibleCut.lean`'s `CutShape` +
`remainder`) generalizes this to arbitrary admissible cuts; the
single-cut version here is kept as a standalone helper for
non-algebraic consumers.
-/

namespace Minimalism

/-- The trace stub used by `quotientTree`. A placeholder LIToken that
    represents "the contracted subtree at this position". -/
def quotientLeafToken : LIToken :=
  ⟨LexicalItem.simple .N [], 0⟩

/-- Quotient tree: replace the first occurrence of `v` in `T` with the
    trace stub. Returns `none` if `v` is not found in `T`. -/
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

/-- If `containsOrEq T v`, then `quotientTree T v` returns some result. -/
private theorem quotientTree_some_of_containsOrEq (T v : SyntacticObject)
    (h : containsOrEq T v) : ∃ q, quotientTree T v = some q := by
  induction T with
  | leaf tok =>
    rcases h with rfl | hc
    · exact ⟨.leaf quotientLeafToken, by simp [quotientTree]⟩
    · exact absurd hc (leaf_contains_nothing tok v)
  | node a b iha ihb =>
    by_cases heq : SyntacticObject.node a b = v
    · refine ⟨.leaf quotientLeafToken, ?_⟩
      subst heq
      unfold quotientTree
      simp
    · have hbeq : ((SyntacticObject.node a b) == v) = false := by
        rw [beq_eq_false_iff_ne]; exact heq
      unfold quotientTree
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hc : contains (.node a b) v := by
        rcases h with rfl | hc
        · exact absurd rfl heq
        · exact hc
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
      · obtain ⟨a', ha'⟩ := iha ha
        exact ⟨.node a' b, by simp [ha']⟩
      · obtain ⟨b', hb'⟩ := ihb hb
        cases hqa : quotientTree a v with
        | some a' => exact ⟨.node a' b, by simp [hqa]⟩
        | none => exact ⟨.node a b', by simp [hqa, hb']⟩

/-- If v is contained in T, `quotientTree` succeeds. -/
theorem quotientTree_some_of_contains (T v : SyntacticObject)
    (h : contains T v) : (quotientTree T v).isSome = true := by
  obtain ⟨q, hq⟩ := quotientTree_some_of_containsOrEq T v (Or.inr h)
  simp [hq]

/-- If `quotientTree T v` succeeds, then `containsOrEq T v`. -/
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
    · rename_i _hne
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

/-- `containsOrEq` preserves leafCount ordering: `v.leafCount ≤ T.leafCount`. -/
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
        rcases himm with rfl | rfl
        all_goals
          have ihres := ih
          omega

/-- Quotient tree has correct leaf count: replacing a subtree with a leaf
    reduces leaf count by `(v.leafCount - 1)`. -/
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
    · rename_i _hne
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

/-- Public form of `quotientTree_leafCount_aux`. -/
theorem quotientTree_leafCount (T v q : SyntacticObject)
    (_h : contains T v) (hq : quotientTree T v = some q) :
    q.leafCount = T.leafCount - v.leafCount + 1 :=
  quotientTree_leafCount_aux T v q hq

end Minimalism
