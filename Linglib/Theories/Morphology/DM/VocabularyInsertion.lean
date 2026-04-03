import Linglib.Theories.Morphology.DM.Categorizer

/-!
# Vocabulary Insertion (Distributed Morphology)
@cite{halle-marantz-1993} @cite{bobaljik-2000}

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
(@cite{halle-marantz-1993}) resolves the competition: the most specific
matching rule wins. A rule is more specific if its context is a proper
superset of another matching rule's context.

## Root-Out Insertion

@cite{bobaljik-2000} argues that VI proceeds **root-out**: the root is
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
`Theories/Morphology/DM/Categorizer.lean` provide the syntax-side
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
structure VocabItem (Ctx Root : Type) where
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
def VocabItem.matches {Ctx Root : Type}
    (vi : VocabItem Ctx Root) (ctx : Ctx) (root : Root) : Bool :=
  vi.contextMatch ctx &&
  match vi.rootMatch with
  | none => true
  | some f => f root

/-- Insert a Vocabulary Item at a terminal node. Tries all rules in
    specificity order (highest first); returns the exponent of the
    first matching rule. Returns `none` if no rule matches.

    This implements the **Subset Principle** / **Elsewhere Condition**
    (@cite{halle-marantz-1993}): among all matching rules, the most
    specific one wins. -/
def vocabularyInsert {Ctx Root : Type}
    (rules : List (VocabItem Ctx Root))
    (ctx : Ctx) (root : Root) : Option String :=
  let sorted := rules.mergeSort (λ a b => a.specificity ≥ b.specificity)
  sorted.findSome? λ vi =>
    if vi.matches ctx root then some vi.exponent else none

/-- Simplified insertion when rules are not root-specific. -/
def vocabularyInsertSimple {Ctx : Type}
    (rules : List (VocabItem Ctx Unit))
    (ctx : Ctx) : Option String :=
  vocabularyInsert rules ctx ()

-- ============================================================================
-- § 3: Elsewhere Condition Properties
-- ============================================================================

/-- A rule set has a **default** (elsewhere) rule if some rule matches
    every context. -/
def hasDefault {Ctx Root : Type}
    (rules : List (VocabItem Ctx Root)) : Prop :=
  ∃ vi ∈ rules, ∀ (ctx : Ctx) (root : Root), vi.matches ctx root = true

/-- A rule **overrides** another: both match the same context, but the
    first has strictly higher specificity. -/
def overrides {Ctx Root : Type}
    (vi₁ vi₂ : VocabItem Ctx Root) (ctx : Ctx) (root : Root) : Prop :=
  vi₁.matches ctx root = true ∧
  vi₂.matches ctx root = true ∧
  vi₁.specificity > vi₂.specificity

-- ============================================================================
-- § 4: Root-Out Directionality
-- ============================================================================

/-- Root-out ordering: a terminal at position `i` in the morphological
    structure (0 = root, increasing outward) is inserted at step `i`.

    @cite{bobaljik-2000} argues this is the standard assumption in DM:
    the root is the first exponent to be inserted, then the innermost
    inflectional affix, then the next one out, etc.

    The consequence: VI for terminal at position `i` can only be
    conditioned by the phonological shapes of terminals at positions
    0..i−1 (already inserted). It cannot look ahead to position i+1. -/
structure InsertionOrder where
  /-- Number of terminal positions in the morphological word. -/
  positions : Nat
  /-- At each step, which position is being inserted.
      For root-out: step i inserts position i. -/
  order : Fin positions → Fin positions

/-- A root-out insertion order: position 0 (root) first, then outward. -/
def rootOutOrder (n : Nat) : InsertionOrder :=
  { positions := n
    order := id }

/-- The constraint that OS-PCSA imposes: the conditioning environment
    for VI at position `i` can only include positions *inward* of `i`
    (i.e., positions 0..i−1).

    If the alternation at position `i` is conditioned by the phonological
    shape of a morpheme at position `i+1` or beyond, it is
    **outward-sensitive** and problematic for standard root-out DM. -/
def isInwardConditioned (conditioningPos targetPos : Nat) : Bool :=
  conditioningPos < targetPos

/-- The Telugu weak alternation is outward-sensitive: the alternation
    on the *n* head (closer to root) is conditioned by case/agreement
    suffixes (further from root). This is the key diagnostic that
    motivates the phonological analysis. -/
def isOutwardSensitive (conditioningPos targetPos : Nat) : Bool :=
  conditioningPos ≥ targetPos

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- In root-out order, position 0 is inserted first. -/
theorem rootOut_starts_at_root (n : Nat) (h : 0 < n) :
    (rootOutOrder n).order ⟨0, h⟩ = ⟨0, h⟩ := rfl

/-- Inward conditioning: position 0 can condition position 1. -/
theorem root_conditions_affix : isInwardConditioned 0 1 = true := rfl

/-- Outward conditioning: position 2 cannot condition position 1
    under root-out VI (it hasn't been inserted yet). -/
theorem outer_cannot_condition_inner :
    isOutwardSensitive 2 1 = true := rfl

-- ============================================================================
-- § 6: Feature-Set Vocabulary Items (Subset Principle)
-- ============================================================================

/-- A feature-set vocabulary item for the Subset Principle.
    Simpler than the full `VocabItem`: a feature specification paired
    with an exponent. The **Subset Principle** selects the most specific
    item whose features are all present in the target.

    Used when VI is purely determined by feature-subset matching
    (e.g., gender agreement class selection in
    @cite{adamson-anagnostopoulou-2025}). -/
structure FeatureVI (F E : Type) where
  features : List F
  exponent : E
  deriving DecidableEq, Repr

/-- The **Subset Principle** (@cite{halle-marantz-1993}): among vocabulary
    items whose feature specification is a subset of the target, select
    the most specific (longest feature list).

    Returns `none` only if `items` is empty. When items include an
    elsewhere entry (empty feature list), `subsetPrinciple` always
    succeeds — the elsewhere item matches any target. -/
def subsetPrinciple {F E : Type} [BEq F]
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
theorem elsewhere_always_matches {F E : Type} [BEq F]
    (e : E) (target : List F) :
    (FeatureVI.mk ([] : List F) e).features.all (target.contains ·) = true := by
  simp [List.all_nil]

end Morphology.DM.VI
