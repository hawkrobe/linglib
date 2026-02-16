/-
# Merge Unification: Internal and External Merge are the Same Operation

Formalization of the claim that Internal and External Merge reduce to the
same fundamental operation, differing only in their input conditions.

## The Traditional Distinction

In the syntax literature, Merge is typically divided into:
- **External Merge**: Combines two SOs with no prior structural relation
- **Internal Merge**: Re-merges an SO already contained in the structure (movement)

## The Unification (Chomsky 2004, Harizanov 2019)

The key insight is that this is a distinction in *preconditions*, not in the
*operation itself*. Both:
1. Take two SOs as input
2. Return {α, β} as output
3. Use the same labeling algorithm to determine what projects

## Main Results

1. **Same Operation**: External and Internal Merge both reduce to `merge`
2. **Labeling Uniformity**: Projection depends on selection, not merge type
3. **Exhaustivity**: Every valid merge is either External or Internal
4. **Movement Uniformity**: Properties of movement don't depend on mover's nature

## References

- Chomsky, N. (2004). "Beyond Explanatory Adequacy"
- Chomsky, N. (2013). "Problems of Projection"
- Harizanov, B. (2019). "Head movement and morphological realization"
-/

import Linglib.Theories.Syntax.Minimalism.Core.Labeling
import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.Basic

namespace Minimalism

-- Part 1: The Traditional Distinction (Formalized)

/-- External Merge: combining two SOs with no prior containment relation.

    This is the "first Merge" case: α and β come from the lexical array
    and have never been in a structural relation before.

    Traditional view: This builds structure "from scratch". -/
structure ExternalMerge where
  /-- First input -/
  α : SyntacticObject
  /-- Second input -/
  β : SyntacticObject
  /-- The result of merging -/
  result : SyntacticObject
  /-- Inputs must be distinct -/
  distinct : α ≠ β
  /-- THE KEY PRECONDITION: No prior containment relation -/
  no_containment : ¬contains α β ∧ ¬contains β α
  /-- The result is formed by merge -/
  is_merge : result = merge α β

/-- Internal Merge: re-merging an SO already contained in the structure.

    This is movement: the mover is extracted from within the target
    and re-merged at a higher position.

    Traditional view: This creates displacement/copies. -/
structure InternalMerge where
  /-- The structure containing the mover -/
  target : SyntacticObject
  /-- The element that moves (already in target) -/
  mover : SyntacticObject
  /-- The result of merging -/
  result : SyntacticObject
  /-- Inputs must be distinct -/
  distinct : target ≠ mover
  /-- THE KEY PRECONDITION: Mover is already contained in target -/
  containment : contains target mover
  /-- The result is formed by merge (mover goes to specifier position) -/
  is_merge : result = merge mover target

-- Part 2: The Unification Theorems

/-- **THEOREM 1 (Same Operation)**:
    Both External and Internal Merge use the same underlying `merge` function.

    The operation itself is identical - only the preconditions differ. -/
theorem external_internal_same_operation :
    (∀ em : ExternalMerge, em.result = merge em.α em.β) ∧
    (∀ im : InternalMerge, im.result = merge im.mover im.target) := by
  constructor
  · intro em; exact em.is_merge
  · intro im; exact im.is_merge

/-- A general Merge operation that abstracts over both types -/
structure GeneralMerge where
  /-- First input (the one that ends up on the left) -/
  left : SyntacticObject
  /-- Second input (the one that ends up on the right) -/
  right : SyntacticObject
  /-- The result -/
  result : SyntacticObject
  /-- Inputs must be distinct -/
  distinct : left ≠ right
  /-- Result is merge of inputs -/
  is_merge : result = merge left right

/-- External Merge is a special case of General Merge -/
def ExternalMerge.toGeneral (em : ExternalMerge) : GeneralMerge where
  left := em.α
  right := em.β
  result := em.result
  distinct := em.distinct
  is_merge := em.is_merge

/-- Internal Merge is a special case of General Merge -/
def InternalMerge.toGeneral (im : InternalMerge) : GeneralMerge where
  left := im.mover
  right := im.target
  result := im.result
  distinct := im.distinct.symm
  is_merge := im.is_merge

/-- **THEOREM 2 (Exhaustivity)**:
    Every General Merge is either External or Internal (no third kind).

    The containment precondition is the ONLY distinguishing feature. -/
theorem merge_exhaustive (gm : GeneralMerge) :
    (¬contains gm.left gm.right ∧ ¬contains gm.right gm.left) ∨
    (contains gm.left gm.right ∨ contains gm.right gm.left) := by
  by_cases h : contains gm.left gm.right ∨ contains gm.right gm.left
  · exact Or.inr h
  · push_neg at h
    exact Or.inl h

/-- The preconditions are mutually exclusive and exhaustive -/
theorem merge_preconditions_partition (α β : SyntacticObject) :
    (¬contains α β ∧ ¬contains β α) ↔
    ¬(contains α β ∨ contains β α) := by
  constructor
  · intro ⟨h1, h2⟩ h
    cases h with
    | inl h => exact h1 h
    | inr h => exact h2 h
  · intro h
    push_neg at h
    exact h

-- Part 3: Labeling Uniformity

/-- When α selects β, the label of {α, β} equals the label of α -/
theorem label_of_merge_when_selects (α β : SyntacticObject)
    (h : selects α β) : label (merge α β) = label α := by
  simp only [merge, label]
  simp only [selects] at h
  simp only [h, ↓reduceIte]

/-- When β selects α (and α doesn't select β), the label of {α, β} equals the label of β -/
theorem label_of_merge_when_right_selects (α β : SyntacticObject)
    (h : selects β α) (hna : ¬selects α β) : label (merge α β) = label β := by
  simp only [merge, label]
  simp only [selects] at h hna
  simp only [hna, h, ↓reduceIte]
  rfl

-- Labeling Symmetry and the Necessity of No Mutual Selection

/-
## Why NoMutualSelection is Algebraically Required

Merge creates an UNORDERED set {α, β}. For labeling to be well-defined on sets
(rather than ordered pairs), we need: label (merge α β) = label (merge β α).

The `label` function checks `selectsB α β` before `selectsB β α`, creating
apparent order-dependence. We prove this is only a problem when BOTH select
each other with distinct labels - precisely the case NoMutualSelection excludes.

This reframes NoMutualSelection from "empirical generalization" to
"algebraic requirement for labeling coherence on unordered sets."
-/

/-- Mutual selection with distinct labels breaks labeling symmetry.

    This is the key theorem: if both α and β select each other, and they
    have different labels, then label (merge α β) ≠ label (merge β α).
    This violates the set-theoretic nature of Merge, where {α,β} = {β,α}. -/
theorem mutual_selection_breaks_symmetry (α β : SyntacticObject)
    (hαβ : selects α β) (hβα : selects β α) (hdistinct : label α ≠ label β) :
    label (merge α β) ≠ label (merge β α) := by
  -- label (merge α β) = label α (α selects β, first branch fires)
  have h1 : label (merge α β) = label α := label_of_merge_when_selects α β hαβ
  -- label (merge β α) = label β (β selects α, first branch fires)
  have h2 : label (merge β α) = label β := label_of_merge_when_selects β α hβα
  rw [h1, h2]
  exact hdistinct

/-- No mutual selection (with some selection) preserves labeling symmetry.

    When at least one element selects the other, but not mutually,
    labeling is symmetric: label (merge α β) = label (merge β α). -/
theorem no_mutual_preserves_symmetry (α β : SyntacticObject)
    (h_no_mutual : ¬(selects α β ∧ selects β α))
    (h_some : selects α β ∨ selects β α) :
    label (merge α β) = label (merge β α) := by
  cases h_some with
  | inl hαβ =>
    -- α selects β, so β doesn't select α (by no mutual)
    have hβα : ¬selects β α := λ h => h_no_mutual ⟨hαβ, h⟩
    -- Both merges have label α
    have h1 : label (merge α β) = label α := label_of_merge_when_selects α β hαβ
    have h2 : label (merge β α) = label α := label_of_merge_when_right_selects β α hαβ hβα
    rw [h1, h2]
  | inr hβα =>
    -- β selects α, so α doesn't select β (by no mutual)
    have hαβ : ¬selects α β := λ h => h_no_mutual ⟨h, hβα⟩
    -- Both merges have label β
    have h1 : label (merge α β) = label β := label_of_merge_when_right_selects α β hβα hαβ
    have h2 : label (merge β α) = label β := label_of_merge_when_selects β α hβα
    rw [h1, h2]

/-- **MAIN THEOREM**: Labeling symmetry characterization.

    When at least one element selects the other, labeling is symmetric
    if and only if there's no mutual selection OR the labels are equal.

    This shows NoMutualSelection is NECESSARY (not just empirically observed)
    for labeling to be well-defined on unordered sets {α, β}. -/
theorem labeling_symmetric_iff (α β : SyntacticObject)
    (h_some : selects α β ∨ selects β α) :
    label (merge α β) = label (merge β α) ↔
    ¬(selects α β ∧ selects β α) ∨ label α = label β := by
  constructor
  · -- Forward: symmetry implies no mutual selection or same labels
    intro h_sym
    by_cases h_mutual : selects α β ∧ selects β α
    · -- If mutual selection, must have same labels (else symmetry breaks)
      right
      by_contra h_diff
      exact mutual_selection_breaks_symmetry α β h_mutual.1 h_mutual.2 h_diff h_sym
    · -- No mutual selection
      left; exact h_mutual
  · -- Backward: no mutual selection or same labels implies symmetry
    intro h
    cases h with
    | inl h_no_mutual => exact no_mutual_preserves_symmetry α β h_no_mutual h_some
    | inr h_same =>
      -- If labels are equal, symmetry is trivial
      cases h_some with
      | inl hαβ =>
        rw [label_of_merge_when_selects α β hαβ]
        by_cases hβα : selects β α
        · rw [label_of_merge_when_selects β α hβα, h_same]
        · rw [label_of_merge_when_right_selects β α hαβ hβα, h_same]
      | inr hβα =>
        by_cases hαβ : selects α β
        · rw [label_of_merge_when_selects α β hαβ,
              label_of_merge_when_selects β α hβα, h_same]
        · rw [label_of_merge_when_right_selects α β hβα hαβ,
              label_of_merge_when_selects β α hβα]

/-- No mutual selection: at most one of α, β can select the other.

    Within the Minimalist formalism, this is algebraically required:
    `labeling_symmetric_iff` shows that without it (and with distinct labels),
    label (merge α β) ≠ label (merge β α), violating the set-theoretic
    nature of Merge where {α, β} = {β, α}. -/
def NoMutualSelection (α β : SyntacticObject) : Prop :=
  ¬(selects α β ∧ selects β α)

/-- When α selects β, α and {α,β} have the same label -/
theorem sameLabel_when_selects (α β : SyntacticObject)
    (h : selects α β) (hne : label α ≠ none) : sameLabel α (merge α β) := by
  unfold sameLabel
  constructor
  · exact (label_of_merge_when_selects α β h).symm
  · exact hne

/-- Helper: label of a leaf is always some -/
theorem label_leaf_is_some (tok : LIToken) : label (.leaf tok) = some tok.item := rfl

/-- Helper lemma: label of a leaf is never none -/
theorem label_leaf_ne_none (tok : LIToken) : label (.leaf tok) ≠ none := by
  simp only [label]; intro h; cases h

/-- Corollary: if label α ≠ none, then label returns some LI -/
theorem label_ne_none_is_some (α : SyntacticObject) (h : label α ≠ none) :
    ∃ li, label α = some li := by
  cases hlbl : label α with
  | none => exact absurd hlbl h
  | some li => exact ⟨li, rfl⟩

/-- For any SO, label never returns none.
    This follows from the structure: every SO contains a leaf,
    and label always finds it. -/
theorem label_always_some (α : SyntacticObject) : label α ≠ none := by
  induction α with
  | leaf tok =>
    -- Leaf: label always returns some
    simp only [label]; intro h; cases h
  | node a b ih_a ih_b =>
    simp only [label]
    split_ifs with hab hba
    · -- selectsB a b = true: label = label a
      exact ih_a
    · -- selectsB b a = true: label = label b
      exact ih_b
    · -- Neither selectsB: case split on getLIToken
      match ha : a.getLIToken, hb : b.getLIToken with
      | some _, some _ =>
        -- Both leaves: always returns some
        simp only [label, ha, hb]; split_ifs <;> (intro h; cases h)
      | some _, none =>
        -- a is leaf, b is phrase: returns label b
        simp only [label, ha, hb]; exact ih_b
      | none, some _ =>
        -- a is phrase, b is leaf: returns label a
        simp only [label, ha, hb]; exact ih_a
      | none, none =>
        -- Both phrases: depends on label a, label b
        simp only [label, ha, hb]
        match hla : label a, hlb : label b with
        | some _, some _ => simp only [hla, hlb]; split_ifs <;> (intro h; cases h)
        | some _, none => exact absurd hlb ih_b
        | none, some _ => exact absurd hla ih_a
        | none, none => exact absurd hla ih_a

/-- Corollary: getProjectingLI returning some implies label is not none -/
theorem getProjectingLI_some_implies_label_some (α : SyntacticObject) :
    ∀ li, getProjectingLI α = some li → label α ≠ none := by
  intro _ _
  exact label_always_some α

/-- If α selects β, then α has a label (not none). -/
theorem selects_implies_has_label (α β : SyntacticObject)
    (h : selects α β) : label α ≠ none := by
  simp only [selects, selectsB] at h
  cases α with
  | leaf tok => exact label_leaf_ne_none tok
  | node a b =>
    simp only [SyntacticObject.getLIToken] at h
    cases hli : getProjectingLI (SyntacticObject.node a b) with
    | none => simp only [hli] at h; cases h
    | some li =>
      exact getProjectingLI_some_implies_label_some (.node a b) li hli

/-- When β selects α and α doesn't select β, β and {α,β} have the same label -/
theorem sameLabel_when_right_selects (α β : SyntacticObject)
    (h : selects β α) (hna : ¬selects α β) : sameLabel β (merge α β) := by
  unfold sameLabel
  constructor
  · exact (label_of_merge_when_right_selects α β h hna).symm
  · exact selects_implies_has_label β α h

/-- **THEOREM 3 (Labeling Uniformity)**:
    The labeling algorithm works identically for External and Internal Merge.

    What projects depends on selectional relations, not on whether the
    merge was external or internal. -/
theorem labeling_uniform_external (em : ExternalMerge)
    (h_selects : selects em.α em.β) :
    projectsIn em.α em.result := by
  -- If α selects β, then α projects in {α, β}
  -- projectsIn x y = immediatelyContains y x ∧ sameLabel x y
  unfold projectsIn
  constructor
  · -- α is immediately contained in result
    rw [em.is_merge]
    simp only [merge, immediatelyContains]
    left; trivial
  · -- α has the same label as result
    rw [em.is_merge]
    exact sameLabel_when_selects em.α em.β h_selects (selects_implies_has_label em.α em.β h_selects)

theorem labeling_uniform_internal (im : InternalMerge)
    (h_selects : selects im.mover im.target) :
    projectsIn im.mover im.result := by
  -- Same logic: if mover selects target, mover projects
  unfold projectsIn
  constructor
  · -- mover is immediately contained in result
    rw [im.is_merge]
    simp only [merge, immediatelyContains]
    left; trivial
  · -- mover has the same label as result
    rw [im.is_merge]
    exact sameLabel_when_selects im.mover im.target h_selects
      (selects_implies_has_label im.mover im.target h_selects)

/-- **COROLLARY**: Selection determines projection, not merge type -/
theorem selection_determines_projection :
    ∀ (gm : GeneralMerge),
      selects gm.left gm.right → projectsIn gm.left gm.result := by
  intro gm h_sel
  unfold projectsIn
  constructor
  · rw [gm.is_merge]
    simp only [merge, immediatelyContains]
    left; trivial
  · rw [gm.is_merge]
    exact sameLabel_when_selects gm.left gm.right h_sel
      (selects_implies_has_label gm.left gm.right h_sel)

-- Part 4: Parallel Properties for Both Merge Types

/-
## Harizanov's Three Unification Claims (Page 53)

We now show that External and Internal Merge satisfy the same three properties:

1. **Operation Uniformity**: The merge operation doesn't depend on element nature
2. **Labeling Uniformity**: Projection depends on selection, not merge type
3. **Projection Flexibility**: Either input can project (not just one)
-/

/-- **Property 1 for External Merge**: Operation doesn't depend on element nature -/
theorem external_merge_uniform (em : ExternalMerge) :
    -- Whether α and β are heads or phrases, the result is the same
    em.result = merge em.α em.β :=
  em.is_merge

/-- **Property 1 for Internal Merge**: Operation doesn't depend on element nature -/
theorem internal_merge_uniform (im : InternalMerge) :
    -- Whether mover is a head or phrase, the result is the same
    im.result = merge im.mover im.target :=
  im.is_merge

/-- **Property 2 for External Merge**: Labeling depends on selection -/
theorem external_merge_labeling (em : ExternalMerge)
    (h : selects em.α em.β) : projectsIn em.α em.result :=
  labeling_uniform_external em h

/-- **Property 2 for Internal Merge**: Labeling depends on selection -/
theorem internal_merge_labeling (im : InternalMerge)
    (h : selects im.mover im.target) : projectsIn im.mover im.result :=
  labeling_uniform_internal im h

/-- **Property 3 for External Merge**: Either element can project.

    Requires `NoMutualSelection`: selection on categories must be acyclic,
    so at most one of α, β can select the other. -/
theorem external_merge_either_projects (em : ExternalMerge)
    (h_acyclic : NoMutualSelection em.α em.β) :
    (selects em.α em.β → projectsIn em.α em.result) ∧
    (selects em.β em.α → projectsIn em.β em.result) := by
  constructor
  · exact labeling_uniform_external em
  · intro h
    unfold projectsIn
    constructor
    · rw [em.is_merge]
      simp only [merge, immediatelyContains]
      right; trivial
    · rw [em.is_merge]
      -- β selects α. By acyclicity, α cannot also select β.
      have hαβ : ¬selects em.α em.β := λ hαβ => h_acyclic ⟨hαβ, h⟩
      exact sameLabel_when_right_selects em.α em.β h hαβ

/-- **Property 3 for Internal Merge**: Either element can project.

    Requires `NoMutualSelection`: selection on categories must be acyclic. -/
theorem internal_merge_either_projects (im : InternalMerge)
    (h_acyclic : NoMutualSelection im.mover im.target) :
    (selects im.mover im.target → projectsIn im.mover im.result) ∧
    (selects im.target im.mover → projectsIn im.target im.result) := by
  constructor
  · -- mover can project
    exact labeling_uniform_internal im
  · -- target can project
    intro h
    unfold projectsIn
    constructor
    · rw [im.is_merge]
      simp only [merge, immediatelyContains]
      right; trivial
    · rw [im.is_merge]
      -- target selects mover. By acyclicity, mover cannot also select target.
      have hmov : ¬selects im.mover im.target := λ hmov => h_acyclic ⟨hmov, h⟩
      exact sameLabel_when_right_selects im.mover im.target h hmov

/-- **THEOREM (Harizanov Unification)**: Both merge types satisfy all three properties.

    Property 3 requires `NoMutualSelection` (acyclicity of selection on categories). -/
theorem harizanov_unification :
    -- Property 1: Same operation
    (∀ em : ExternalMerge, em.result = merge em.α em.β) ∧
    (∀ im : InternalMerge, im.result = merge im.mover im.target) ∧
    -- Property 2: Labeling by selection
    (∀ em : ExternalMerge, selects em.α em.β → projectsIn em.α em.result) ∧
    (∀ im : InternalMerge, selects im.mover im.target → projectsIn im.mover im.result) ∧
    -- Property 3: Either can project (given acyclic selection)
    (∀ em : ExternalMerge, NoMutualSelection em.α em.β →
      (selects em.α em.β → projectsIn em.α em.result) ∧
      (selects em.β em.α → projectsIn em.β em.result)) ∧
    (∀ im : InternalMerge, NoMutualSelection im.mover im.target →
      (selects im.mover im.target → projectsIn im.mover im.result) ∧
      (selects im.target im.mover → projectsIn im.target im.result)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact external_merge_uniform
  · exact internal_merge_uniform
  · exact λ em => labeling_uniform_external em
  · exact λ im => labeling_uniform_internal im
  · exact external_merge_either_projects
  · exact internal_merge_either_projects

-- Part 5: Movement Uniformity (Harizanov's First Claim - Details)

/-- **THEOREM 4 (Movement Uniformity)**:
    "The properties of movement do not depend on the nature of the moving element"

    Whether the mover is a head or a phrase, Internal Merge works the same way.
    The mover always ends up in the left daughter position of the result. -/
theorem movement_uniform_position (im : InternalMerge) :
    ∃ sister, im.result = SyntacticObject.node im.mover sister := by
  use im.target
  rw [im.is_merge]
  rfl

/-- The mover is always the left daughter after Internal Merge -/
theorem mover_is_left_daughter (im : InternalMerge) :
    immediatelyContains im.result im.mover := by
  rw [im.is_merge]
  simp only [merge, immediatelyContains]
  left; trivial

/-- The target is always the right daughter after Internal Merge -/
theorem target_is_right_daughter (im : InternalMerge) :
    immediatelyContains im.result im.target := by
  rw [im.is_merge]
  simp only [merge, immediatelyContains]
  right; trivial

-- Part 5: Projection After Movement (Harizanov's Second Claim)

/-- **THEOREM 5 (Mover Can Project)**:
    "A moved element can project after movement"

    This is non-trivial: traditionally, only the target was thought to project.
    But if the mover has unvalued selectional features that can be satisfied
    by the target, the mover can project (= head-to-head movement). -/
theorem mover_can_project (im : InternalMerge)
    (h_mover_selects : selects im.mover im.target) :
    projectsIn im.mover im.result := by
  -- When mover selects target, mover projects (this is reprojection)
  exact labeling_uniform_internal im h_mover_selects

/-- Target can also project (standard case).

    Requires `NoMutualSelection`: selection on categories must be acyclic. -/
theorem target_can_project (im : InternalMerge)
    (h_target_selects : selects im.target im.mover)
    (h_acyclic : NoMutualSelection im.mover im.target) :
    projectsIn im.target im.result := by
  unfold projectsIn
  constructor
  · -- target is immediately contained in result
    rw [im.is_merge]
    simp only [merge, immediatelyContains]
    right; trivial
  · -- target has the same label as result
    rw [im.is_merge]
    -- target selects mover. By acyclicity, mover cannot also select target.
    have hmov : ¬selects im.mover im.target := λ hmov => h_acyclic ⟨hmov, h_target_selects⟩
    exact sameLabel_when_right_selects im.mover im.target h_target_selects hmov

/-- The dichotomy: either mover or target projects (one must).

    Requires `NoMutualSelection`: selection on categories must be acyclic. -/
theorem projection_dichotomy (im : InternalMerge)
    (h_one_selects : selects im.mover im.target ∨ selects im.target im.mover)
    (h_acyclic : NoMutualSelection im.mover im.target) :
    projectsIn im.mover im.result ∨ projectsIn im.target im.result := by
  cases h_one_selects with
  | inl h => exact Or.inl (mover_can_project im h)
  | inr h => exact Or.inr (target_can_project im h h_acyclic)

-- Part 6: The Core Equivalence

/-- **MAIN THEOREM (Merge Unification)**:
    Internal and External Merge are the same operation under different preconditions.

    Formally: there exists a single function `merge` such that both EM and IM
    are instances of applying this function, differing only in whether the
    containment precondition holds. -/
theorem merge_unification :
    -- 1. Same underlying operation
    (∀ em : ExternalMerge, ∀ im : InternalMerge,
      em.result = merge em.α em.β ∧ im.result = merge im.mover im.target) ∧
    -- 2. Preconditions are the only difference
    (∀ em : ExternalMerge, ¬contains em.α em.β ∧ ¬contains em.β em.α) ∧
    (∀ im : InternalMerge, contains im.target im.mover) ∧
    -- 3. Preconditions are exhaustive
    (∀ α β : SyntacticObject, α ≠ β →
      (¬contains α β ∧ ¬contains β α) ∨ (contains α β ∨ contains β α)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro em im
    exact ⟨em.is_merge, im.is_merge⟩
  · intro em
    exact em.no_containment
  · intro im
    exact im.containment
  · intro α β _
    by_cases h : contains α β ∨ contains β α
    · exact Or.inr h
    · push_neg at h
      exact Or.inl h

-- Part 7: Consequences for Head Movement

/-- Head movement is just Internal Merge where the mover is a head -/
def isHeadMovement (im : InternalMerge) : Prop :=
  isHeadIn im.mover im.target

/-- Phrasal movement is Internal Merge where the mover is a phrase -/
def isPhrasalMovement (im : InternalMerge) : Prop :=
  isPhraseIn im.mover im.target

/-- **THEOREM**: Head and phrasal movement use the same Internal Merge -/
theorem head_phrasal_same_merge (im₁ im₂ : InternalMerge)
    (h₁ : isHeadMovement im₁) (h₂ : isPhrasalMovement im₂) :
    -- Both satisfy the same structural equation
    im₁.result = merge im₁.mover im₁.target ∧
    im₂.result = merge im₂.mover im₂.target := by
  exact ⟨im₁.is_merge, im₂.is_merge⟩

/-- The difference is in what projects, not in the operation.

    Requires `NoMutualSelection`: selection on categories must be acyclic. -/
theorem head_vs_phrasal_projection (im : InternalMerge)
    (h_acyclic : NoMutualSelection im.mover im.target) :
    -- If mover is a head that selects target: mover projects (head-to-head)
    -- If target selects mover: target projects (head-to-spec or phrasal)
    (isHeadMovement im ∧ selects im.mover im.target → projectsIn im.mover im.result) ∧
    (selects im.target im.mover → projectsIn im.target im.result) := by
  constructor
  · intro ⟨_, h_sel⟩
    exact mover_can_project im h_sel
  · intro h_sel
    exact target_can_project im h_sel h_acyclic

-- Part 8: The Algebraic Foundation (Why This Isn't a Choice)

/-
## Why the Partition is Algebraic, Not Stipulated

Collins & Stabler (2016) note that "various modifications of derive-by-Merge
would yield other possibilities" including sideward merge. This might suggest
the Internal/External distinction is arbitrary.

But there are TWO separate issues:
1. **The partition of element pairs** - algebraic, follows from order theory
2. **Accessibility conditions** - operational, involves choices about workspaces

The partition itself follows from containment being a STRICT PARTIAL ORDER:
- Irreflexive: ¬(α contains α)
- Asymmetric: α contains β → ¬(β contains α)
- Transitive: α contains β → β contains γ → α contains γ

For ANY strict partial order, element pairs partition into:
- Comparable: one relates to the other
- Incomparable: neither relates to the other

This is the **trichotomy theorem** for partial orders - pure algebra, no choice.
-/

/-- Containment is a strict partial order: irreflexive, asymmetric, transitive.
    This is an algebraic property of tree structure, not a stipulation. -/
structure StrictPartialOrder (α : Type*) (R : α → α → Prop) : Prop where
  irrefl : ∀ x, ¬R x x
  asymm : ∀ x y, R x y → ¬R y x
  trans : ∀ x y z, R x y → R y z → R x z

/-- No element contains itself (well-foundedness of trees) -/
theorem contains_irrefl' (x : SyntacticObject) : ¬contains x x :=
  contains_irrefl x

/-- Containment on syntactic objects forms a strict partial order -/
theorem contains_is_strict_partial_order : StrictPartialOrder SyntacticObject contains where
  irrefl := contains_irrefl'
  asymm := λ x y hxy hyx => contains_irrefl' x (contains_trans hxy hyx)
  trans := λ _ _ _ => contains_trans

/-- **TRICHOTOMY THEOREM** (Order Theory):
    For any strict partial order, element pairs fall into exactly one of three cases.
    This is algebraic - it follows from the definition of strict partial order. -/
theorem strict_partial_order_trichotomy
    {α : Type*} {R : α → α → Prop} (spo : StrictPartialOrder α R)
    (x y : α) (hne : x ≠ y) :
    (R x y ∧ ¬R y x) ∨ (R y x ∧ ¬R x y) ∨ (¬R x y ∧ ¬R y x) := by
  by_cases hxy : R x y
  · left
    exact ⟨hxy, spo.asymm x y hxy⟩
  · by_cases hyx : R y x
    · right; left
      exact ⟨hyx, spo.asymm y x hyx⟩
    · right; right
      exact ⟨hxy, hyx⟩

/-- The trichotomy cases are mutually exclusive -/
theorem trichotomy_mutually_exclusive
    {α : Type*} {R : α → α → Prop} (spo : StrictPartialOrder α R)
    (x y : α) :
    ¬((R x y) ∧ (R y x)) := by
  intro ⟨hxy, hyx⟩
  exact spo.asymm x y hxy hyx

/-- **COROLLARY**: Internal/External partition follows from trichotomy.

    Grouping "R x y" and "R y x" gives COMPARABLE (Internal Merge).
    The third case is INCOMPARABLE (External Merge).

    This is why the partition isn't a "choice" - it's forced by order theory. -/
theorem merge_partition_from_trichotomy (α β : SyntacticObject) (hne : α ≠ β) :
    -- Either comparable (one contains the other) = Internal Merge
    (contains α β ∨ contains β α) ∨
    -- Or incomparable (neither contains) = External Merge
    (¬contains α β ∧ ¬contains β α) := by
  have tri := strict_partial_order_trichotomy contains_is_strict_partial_order α β hne
  rcases tri with ⟨hαβ, _⟩ | ⟨hβα, _⟩ | hincomp
  · left; left; exact hαβ
  · left; right; exact hβα
  · right; exact hincomp

/-- The "choices" Collins & Stabler mention are about ACCESSIBILITY, not partition.

    Different workspace conditions determine which pairs are ACCESSIBLE for Merge:
    - "A ∈ W ∧ B ∈ W" → only incomparable pairs accessible (External only)
    - "A ∈ W ∧ (A contains B ∨ B ∈ W)" → standard (External + Internal)
    - "A ∈ W ∧ B contained in W" → adds sideward merge

    But the PARTITION of pairs into comparable/incomparable is algebraic.
    The "choice" is which partition cells are accessible, not the partition itself. -/
theorem accessibility_is_separate_from_partition :
    -- The partition exists independently of accessibility conditions
    ∀ α β : SyntacticObject, α ≠ β →
      (contains α β ∨ contains β α) ∨ (¬contains α β ∧ ¬contains β α) :=
  merge_partition_from_trichotomy

/-
## Algebraic Structure of Accessibility Conditions

The accessibility conditions themselves form a LATTICE ordered by permissivity.
Chomsky's choice is distinguished by a minimality property.
-/

/-- Accessibility conditions as predicates on (workspace, element, element) triples -/
def AccessCondition := Set SyntacticObject → SyntacticObject → SyntacticObject → Prop

/-- External-only: both must be roots -/
def externalOnly : AccessCondition :=
  λ W A B => A ∈ W ∧ B ∈ W

/-- Standard (Chomsky): A is root, B is either in A or a root -/
def standardAccess : AccessCondition :=
  λ W A B => A ∈ W ∧ (contains A B ∨ B ∈ W)

/-- Sideward: A is root, B is anywhere in W -/
def sidewardAccess : AccessCondition :=
  λ W A B => A ∈ W ∧ (∃ C ∈ W, containsOrEq C B)

/-- Full: both anywhere in W -/
def fullAccess : AccessCondition :=
  λ W A B => (∃ C ∈ W, containsOrEq C A) ∧ (∃ D ∈ W, containsOrEq D B)

/-- One condition is more permissive than another -/
def morePermissive (c1 c2 : AccessCondition) : Prop :=
  ∀ W A B, c2 W A B → c1 W A B

/-- The conditions form a chain: external ⊂ standard ⊂ sideward ⊂ full -/
theorem accessibility_chain :
    morePermissive standardAccess externalOnly ∧
    morePermissive sidewardAccess standardAccess ∧
    morePermissive fullAccess sidewardAccess := by
  constructor
  · -- standard ⊇ external
    intro W A B ⟨hA, hB⟩
    exact ⟨hA, Or.inr hB⟩
  constructor
  · -- sideward ⊇ standard
    intro W A B ⟨hA, hAB⟩
    constructor
    · exact hA
    · cases hAB with
      | inl hcont => exact ⟨A, hA, Or.inr hcont⟩
      | inr hB => exact ⟨B, hB, Or.inl rfl⟩
  · -- full ⊇ sideward
    intro W A B ⟨hA, ⟨C, hC, hCB⟩⟩
    constructor
    · exact ⟨A, hA, Or.inl rfl⟩
    · exact ⟨C, hC, hCB⟩

/-- **THEOREM (Minimality of Chomsky's Choice)**:
    Standard access is the MINIMAL extension of external-only that allows Internal Merge.

    "Minimal" means: any condition that allows Internal Merge and is
    at most as permissive as standard must equal standard on Internal cases. -/
theorem chomsky_choice_is_minimal :
    -- Standard allows Internal Merge
    (∀ W A B, A ∈ W → contains A B → standardAccess W A B) ∧
    -- External-only doesn't allow Internal Merge (when B ∉ W)
    (∀ W A B, contains A B → B ∉ W → ¬externalOnly W A B) := by
  constructor
  · intro W A B hA hcont
    exact ⟨hA, Or.inl hcont⟩
  · intro W A B _ hBnotW ⟨_, hB⟩
    exact hBnotW hB

/-
## What "Minimality" Means Mathematically

In lattice-theoretic terms, Chomsky's standard condition is the JOIN (least upper bound)
of two simpler conditions:

  Standard = External ∨ Internal

where:
  - External(W,A,B) = A ∈ W ∧ B ∈ W
  - Internal(W,A,B) = A ∈ W ∧ contains A B

This is the MINIMAL condition that:
1. Includes all external merges (roots with roots)
2. Includes all internal merges (root with something it contains)
3. Includes nothing else

The mathematical characterization is:
  Standard = sup{External, Internal} in the lattice of accessibility conditions

This explains why Standard is "natural" - it's not an arbitrary point in the lattice,
but the LEAST UPPER BOUND of the two fundamental merge types.
-/

/-- The pure Internal Merge condition (without External) -/
def internalOnly : AccessCondition :=
  λ W A B => A ∈ W ∧ contains A B

/-- **THEOREM (Join Characterization)**:
    Standard access is exactly the join of External and Internal conditions.
    This is why Chomsky's choice is canonical - it's a lattice-theoretic join. -/
theorem standard_is_join_of_external_internal :
    ∀ W A B, standardAccess W A B ↔ (externalOnly W A B ∨ internalOnly W A B) := by
  intro W A B
  constructor
  · intro ⟨hA, hAB⟩
    cases hAB with
    | inl hcont => right; exact ⟨hA, hcont⟩
    | inr hB => left; exact ⟨hA, hB⟩
  · intro h
    cases h with
    | inl hext => exact ⟨hext.1, Or.inr hext.2⟩
    | inr hint => exact ⟨hint.1, Or.inl hint.2⟩

/-- Standard is the LEAST condition containing both External and Internal -/
theorem standard_is_least_upper_bound (C : AccessCondition)
    (hext : morePermissive C externalOnly)
    (hint : morePermissive C internalOnly) :
    morePermissive C standardAccess := by
  intro W A B hstd
  rw [standard_is_join_of_external_internal] at hstd
  cases hstd with
  | inl hext' => exact hext W A B hext'
  | inr hint' => exact hint W A B hint'

-- Part 9: Connecting to HeadMovement/Basic.lean

/-
## Connection to Head Movement Types

We now show that both head movement types from HeadMovement/Basic.lean
are instances of InternalMerge, completing the unification picture.

This establishes:
- HeadToSpecMovement IS InternalMerge (with target projecting)
- HeadToHeadMovement IS InternalMerge (with mover projecting)
-/

/-- Containment implies distinctness (uses contains_irrefl from Containment.lean) -/
theorem contains_implies_ne {x y : SyntacticObject} (h : contains x y) : x ≠ y := by
  intro heq
  cases heq
  exact contains_irrefl _ h

/-- Convert a Movement to an InternalMerge -/
def Movement.toInternalMerge (m : Movement) : InternalMerge where
  target := m.target
  mover := m.mover
  result := m.result
  distinct := contains_implies_ne m.mover_in_target
  containment := m.mover_in_target
  is_merge := m.is_merge

/-- HeadToSpecMovement is an instance of InternalMerge -/
def HeadToSpecMovement.toInternalMerge (m : HeadToSpecMovement) : InternalMerge :=
  m.toMovement.toInternalMerge

/-- HeadToHeadMovement is an instance of InternalMerge -/
def HeadToHeadMovement.toInternalMerge (m : HeadToHeadMovement) : InternalMerge :=
  m.toMovement.toInternalMerge

/-- **THEOREM (Head Movement Unification)**:
    Both head movement types are instances of the same InternalMerge operation.

    This completes Harizanov's unification: head-to-spec and head-to-head
    are not different operations, but the same InternalMerge with different
    labeling outcomes. -/
theorem head_movement_is_internal_merge :
    (∀ m : HeadToSpecMovement, m.result = merge m.mover m.target) ∧
    (∀ m : HeadToHeadMovement, m.result = merge m.mover m.target) := by
  constructor
  · intro m; exact m.is_merge
  · intro m; exact m.is_merge

/-- The difference between head-to-spec and head-to-head is purely in labeling -/
theorem head_movement_types_same_merge_different_labeling
    (h2s : HeadToSpecMovement) (h2h : HeadToHeadMovement) :
    -- Same underlying merge operation
    (h2s.result = merge h2s.mover h2s.target) ∧
    (h2h.result = merge h2h.mover h2h.target) ∧
    -- But different labeling: target projects in h2s, mover projects in h2h
    (projectsIn h2s.target h2s.result) ∧
    (¬isMaximalIn h2h.mover h2h.result) := by
  refine ⟨h2s.is_merge, h2h.is_merge, h2s.target_projects, h2h.mover_not_maximal⟩

/-- **COROLLARY**: All movement (head or phrasal) reduces to InternalMerge -/
theorem all_movement_is_internal_merge :
    ∀ m : Movement, ∃ im : InternalMerge,
      im.mover = m.mover ∧ im.target = m.target ∧ im.result = m.result := by
  intro m
  use m.toInternalMerge
  simp [Movement.toInternalMerge]

-- Part 9: The Complete Picture

/-- **MAIN THEOREM (Complete Harizanov Unification)**:

    1. External Merge and Internal Merge are the same operation (differ only in precondition)
    2. Head movement and phrasal movement are both Internal Merge
    3. Head-to-spec and head-to-head are both Internal Merge (differ only in labeling)
    4. All three Harizanov properties hold for both External and Internal Merge

    The only true distinctions are:
    - Containment precondition (External vs Internal)
    - Which element projects (determined by selection, not by operation type)
-/
theorem complete_harizanov_unification :
    -- 1. EM and IM use same merge
    (∀ em : ExternalMerge, em.result = merge em.α em.β) ∧
    (∀ im : InternalMerge, im.result = merge im.mover im.target) ∧
    -- 2. All Movement is IM
    (∀ m : Movement, ∃ im : InternalMerge,
      im.mover = m.mover ∧ im.target = m.target ∧ im.result = m.result) ∧
    -- 3. Head movement types are both IM
    (∀ m : HeadToSpecMovement, m.result = merge m.mover m.target) ∧
    (∀ m : HeadToHeadMovement, m.result = merge m.mover m.target) ∧
    -- 4. Preconditions partition all merges
    (∀ α β : SyntacticObject, α ≠ β →
      (¬contains α β ∧ ¬contains β α) ∨ (contains α β ∨ contains β α)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact λ em => em.is_merge
  · exact λ im => im.is_merge
  · exact all_movement_is_internal_merge
  · exact λ m => m.is_merge
  · exact λ m => m.is_merge
  · intro α β _
    by_cases h : contains α β ∨ contains β α
    · exact Or.inr h
    · push_neg at h; exact Or.inl h

end Minimalism

