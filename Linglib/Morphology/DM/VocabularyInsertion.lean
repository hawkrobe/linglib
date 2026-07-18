import Mathlib.Tactic.TypeStar
import Linglib.Morphology.Exponence.Rule

/-!
# Vocabulary Insertion (Distributed Morphology)
[halle-marantz-1993] [bobaljik-2000]

Vocabulary Insertion is the mechanism by which syntactic terminal nodes
receive phonological exponents in Distributed Morphology. It is the
formal realization of DM's **List 2**: a set of Vocabulary Items (VI
rules) that compete for insertion at each terminal.

## Architecture

A Vocabulary Item specifies:
1. A **phonological exponent** (the surface form)
2. A **morphosyntactic context** (the features the terminal must bear)
3. A **root context** (optional: which roots the rule applies to)

When multiple VI rules match a terminal, the **Elsewhere Condition**
([halle-marantz-1993]) resolves the competition: the most specific
matching rule wins. A rule is more specific if its context is a proper
superset of another matching rule's context.

## Root-Out Insertion

[bobaljik-2000] argues that VI proceeds **root-out**: the root is
inserted first, then inflectional affixes outward. This means VI for
outer morphemes can only be phonologically conditioned by material
already inserted (inward) — it cannot "look ahead" to morphemes not yet
inserted. This is the basis for the claim that outward-sensitive
phonologically conditioned suppletive allomorphy (OS-PCSA) should not
exist.

## Connection to Linglib

This module provides the generic VI framework. Language-specific VI
rules live in `Fragments/` or in phenomenon-specific `Studies/` files.
The `Categorizer` and `CategorizedRoot` types from
`Morphology/DM/Categorizer.lean` provide the syntax-side
terminal nodes that VI targets.
-/

namespace Morphology.DM.VI

-- ============================================================================
-- § 1: Vocabulary Item
-- ============================================================================

/-- A Vocabulary Item: a rule mapping morphosyntactic context to a
    phonological exponent.

    - `Ctx`: the type of morphosyntactic contexts (e.g., feature bundles)
    - `Root`: the type of root identifiers (for root-specific rules)

    The `specificity` field encodes the Elsewhere Condition: when
    multiple rules match, the highest-specificity rule wins. In
    practice, specificity equals the number of features the context
    checks — a rule conditioned on [ACC, +animate] (specificity 2) beats
    a default rule with no feature requirements (specificity 0). -/
structure VocabItem (Ctx Root : Type*) where
  /-- The phonological exponent inserted at the terminal. -/
  exponent : String
  /-- Context check: does the terminal's feature bundle match? -/
  contextMatch : Ctx → Bool
  /-- Root restriction: which roots this rule applies to.
      `none` means the rule is unrestricted (default/elsewhere). -/
  rootMatch : Option (Root → Bool) := none
  /-- Specificity for Elsewhere Condition resolution. Higher = more
      specific. When two rules both match, the higher-specificity
      rule wins. -/
  specificity : Nat := 0

-- ============================================================================
-- § 2: Vocabulary Insertion
-- ============================================================================

/-- Does a Vocabulary Item match at a given terminal node?
    Checks both the morphosyntactic context and the root restriction. -/
def VocabItem.matches {Ctx Root : Type*}
    (vi : VocabItem Ctx Root) (ctx : Ctx) (root : Root) : Bool :=
  vi.contextMatch ctx &&
  match vi.rootMatch with
  | none => true
  | some f => f root

/-- Insert a Vocabulary Item at a terminal node. Tries all rules in
    specificity order (highest first); returns the exponent of the
    first matching rule. Returns `none` if no rule matches.

    This implements the **Subset Principle** / **Elsewhere Condition**
    ([halle-marantz-1993]): among all matching rules, the most
    specific one wins. -/
def vocabularyInsert {Ctx Root : Type*}
    (rules : List (VocabItem Ctx Root))
    (ctx : Ctx) (root : Root) : Option String :=
  let sorted := rules.mergeSort (λ a b => a.specificity ≥ b.specificity)
  sorted.findSome? λ vi =>
    if vi.matches ctx root then some vi.exponent else none

/-- Simplified insertion when rules are not root-specific. -/
def vocabularyInsertSimple {Ctx : Type*}
    (rules : List (VocabItem Ctx Unit))
    (ctx : Ctx) : Option String :=
  vocabularyInsert rules ctx ()

-- ============================================================================
-- § 3: Feature-Set Vocabulary Items (Subset Principle)
-- ============================================================================

/-- A feature-set vocabulary item for the Subset Principle.
    Simpler than the full `VocabItem`: a feature specification paired
    with an exponent. The **Subset Principle** selects the most specific
    item whose features are all present in the target.

    Used when VI is purely determined by feature-subset matching
    (e.g., gender agreement class selection in
    [adamson-anagnostopoulou-2025]). -/
structure FeatureVI (F E : Type*) where
  features : List F
  exponent : E
  deriving DecidableEq, Repr

/-- The **Subset Principle** ([halle-marantz-1993]): among vocabulary
    items whose feature specification is a subset of the target, select
    the most specific (longest feature list).

    Returns `none` only if `items` is empty. When items include an
    elsewhere entry (empty feature list), `subsetPrinciple` always
    succeeds — the elsewhere item matches any target. -/
def subsetPrinciple {F E : Type*} [BEq F]
    (items : List (FeatureVI F E)) (target : List F) : Option E :=
  let matching := items.filter (·.features.all (target.contains ·))
  (matching.foldl (init := none) fun acc item =>
    match acc with
    | none => some item
    | some prev =>
      if item.features.length > prev.features.length
      then some item
      else some prev
  ).map (·.exponent)

/-- An elsewhere item (empty features) matches any target. -/
theorem elsewhere_always_matches {F E : Type*} [BEq F]
    (e : E) (target : List F) :
    (FeatureVI.mk ([] : List F) e).features.all (target.contains ·) = true := by
  simp [List.all_nil]

-- ============================================================================
-- § 4: The shared exponence core
-- ============================================================================

section ExponenceCore

open Morphology.Exponence

variable {Ctx Root : Type*}

/-- A Vocabulary Item exposes the shared exponence core interface
(`Morphology.Exponence.RuleLike`): contexts are (feature-context, root)
pairs, applicability is `matches`. -/
instance : RuleLike (VocabItem Ctx Root) (Ctx × Root) String :=
  ⟨VocabItem.exponent, fun vi => {cr | vi.matches cr.1 cr.2 = true}⟩

instance : Preorder (VocabItem Ctx Root) := RuleLike.toPreorder

/-- The stipulated `specificity` rank is **faithful** when it refines
the derived specificity of the shared core: a strictly more specific
item always outranks. With opaque `contextMatch` predicates the derived
order is not computable, so this engine must stipulate a rank — this
Prop is the obligation the stipulation incurs, and
`vocabularyInsert_isElsewhereWinner` is what discharging it buys. -/
def SpecificityFaithful (rules : List (VocabItem Ctx Root)) : Prop :=
  ∀ a ∈ rules, ∀ b ∈ rules, a ≤ b → ¬ b ≤ a → b.specificity < a.specificity

private theorem findSome?_pairwise_max {l : List (VocabItem Ctx Root)}
    (hs : l.Pairwise (λ a b => b.specificity ≤ a.specificity))
    {ctx : Ctx} {root : Root} {e : String}
    (h : (l.findSome? λ vi =>
      if vi.matches ctx root then some vi.exponent else none) = some e) :
    ∃ vi ∈ l, vi.matches ctx root = true ∧ vi.exponent = e ∧
      ∀ b ∈ l, b.matches ctx root = true → b.specificity ≤ vi.specificity := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [List.findSome?_cons] at h
    obtain ⟨hx, hl⟩ := List.pairwise_cons.mp hs
    by_cases hm : x.matches ctx root
    · rw [if_pos hm] at h
      refine ⟨x, List.mem_cons_self .., hm, Option.some.inj h, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact λ _ => Nat.le_refl _
      · exact λ _ => hx b hb'
    · rw [if_neg hm] at h
      obtain ⟨vi, hvi, hvm, hve, hmax⟩ := ih hl h
      refine ⟨vi, List.mem_cons_of_mem _ hvi, hvm, hve, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact λ hbm => absurd hbm (by simpa using hm)
      · exact hmax b hb'

/-- Under a faithful specificity stipulation, the engine's selection is
an Elsewhere winner of the shared core. -/
theorem vocabularyInsert_isElsewhereWinner {rules : List (VocabItem Ctx Root)}
    {ctx : Ctx} {root : Root} {e : String}
    (h : vocabularyInsert rules ctx root = some e)
    (hf : SpecificityFaithful rules) :
    ∃ vi ∈ rules, vi.exponent = e ∧
      IsElsewhereWinner rules (ctx, root) vi := by
  unfold vocabularyInsert at h
  have hsort : (rules.mergeSort (λ a b => a.specificity ≥ b.specificity)).Pairwise
      (λ a b => b.specificity ≤ a.specificity) := by
    have := List.pairwise_mergeSort
      (le := λ a b : VocabItem Ctx Root => decide (a.specificity ≥ b.specificity))
      (λ a b c hab hbc => by
        simp only [decide_eq_true_eq] at *; omega)
      (λ a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      rules
    exact this.imp (λ hab => by simpa using hab)
  obtain ⟨vi, hvi, hvm, hve, hmax⟩ := findSome?_pairwise_max hsort h
  rw [List.mem_mergeSort] at hvi
  refine ⟨vi, hvi, hve, ⟨hvi, hvm⟩, ?_⟩
  rintro s ⟨hs, happ⟩ hspec
  by_contra hns
  have hlt : vi.specificity < s.specificity := hf s hs vi hvi hspec hns
  have hble : s.specificity ≤ vi.specificity :=
    hmax s (List.mem_mergeSort.mpr hs) happ
  omega

end ExponenceCore

end Morphology.DM.VI
