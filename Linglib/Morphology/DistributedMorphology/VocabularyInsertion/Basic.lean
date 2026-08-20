import Mathlib.Tactic.TypeStar
import Linglib.Morphology.DistributedMorphology.Basic
import Linglib.Morphology.Exponence.Select
import Linglib.Morphology.Realization

/-!
# Vocabulary Insertion (Distributed Morphology)

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
The `Categorizer` type and the `WordStructure` trees from
`Morphology/DistributedMorphology/Categorizer/Basic.lean` provide the
syntax-side terminals and configurations that VI targets.
-/

namespace DistributedMorphology.VI

-- ============================================================================
-- § 1: Vocabulary Insertion
-- ============================================================================

/-- Insert a Vocabulary Item at a terminal node: the exponent of the
highest-`specificity` matching rule (the shared engine's `realize`; ties go
to the earlier rule), `none` if no rule matches — the **Elsewhere
Condition** of [halle-marantz-1993]. -/
def vocabularyInsert {Ctx Root : Type*}
    (rules : List (VocabItem Ctx Root))
    (ctx : Ctx) (root : Root) : Option String :=
  Morphology.Exponence.realize VocabItem.specificity rules (ctx, root)

/-- Simplified insertion when rules are not root-specific. -/
def vocabularyInsertSimple {Ctx : Type*}
    (rules : List (VocabItem Ctx Unit))
    (ctx : Ctx) : Option String :=
  vocabularyInsert rules ctx ()

-- ============================================================================
-- § 2: Feature-Set Vocabulary Items (Subset Principle)
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

/-- The vocabulary items applicable at a target: those whose feature
specification is a subset of the target bundle. -/
def applicable {F E : Type*} [BEq F]
    (items : List (FeatureVI F E)) (target : List F) : List (FeatureVI F E) :=
  items.filter (·.features.all (target.contains ·))

/-- Longest-specification choice step for `winner?`; earlier items win
ties. -/
private def pickLonger {F E : Type*}
    (acc : Option (FeatureVI F E)) (item : FeatureVI F E) :
    Option (FeatureVI F E) :=
  match acc with
  | none => some item
  | some prev =>
    if item.features.length > prev.features.length then some item else some prev

/-- The Subset Principle's winning item: the longest-specification
applicable item (the earliest, under ties). -/
def winner? {F E : Type*} [BEq F]
    (items : List (FeatureVI F E)) (target : List F) :
    Option (FeatureVI F E) :=
  (applicable items target).foldl pickLonger none

/-- The **Subset Principle** ([halle-marantz-1993]): among vocabulary
    items whose feature specification is a subset of the target, select
    the most specific (longest feature list).

    Returns `none` only if no item is applicable. When items include an
    elsewhere entry (empty feature list), `subsetPrinciple` always
    succeeds — the elsewhere item matches any target. -/
def subsetPrinciple {F E : Type*} [BEq F]
    (items : List (FeatureVI F E)) (target : List F) : Option E :=
  (winner? items target).map (·.exponent)

/-- An elsewhere item (empty features) matches any target. -/
theorem elsewhere_always_matches {F E : Type*} [BEq F]
    (e : E) (target : List F) :
    (FeatureVI.mk ([] : List F) e).features.all (target.contains ·) = true := by
  simp [List.all_nil]

private theorem pickLonger_cases {F E : Type*} (acc : Option (FeatureVI F E))
    (x : FeatureVI F E) : pickLonger acc x = some x ∨ pickLonger acc x = acc := by
  cases acc with
  | none => exact .inl rfl
  | some prev =>
    by_cases hlen : x.features.length > prev.features.length <;>
      simp [pickLonger, hlen]

private theorem foldl_choice_mem {α : Type*} {pick : Option α → α → Option α}
    (hpick : ∀ acc x, pick acc x = some x ∨ pick acc x = acc) :
    ∀ {l : List α} {acc : Option α} {i : α},
      l.foldl pick acc = some i → i ∈ l ∨ acc = some i := by
  intro l
  induction l with
  | nil => exact fun h => .inr h
  | cons x xs ih =>
    intro acc i h
    rcases ih h with hmem | hacc
    · exact .inl (List.mem_cons_of_mem _ hmem)
    · rcases hpick acc x with hx | hkeep
      · rw [hx] at hacc
        obtain rfl := Option.some.inj hacc
        exact .inl (List.mem_cons_self ..)
      · exact .inr (hkeep ▸ hacc)

private theorem foldl_pickLonger_ne_none {F E : Type*} :
    ∀ (l : List (FeatureVI F E)) (a : FeatureVI F E),
      l.foldl pickLonger (some a) ≠ none := by
  intro l
  induction l with
  | nil => exact fun a h => by simp at h
  | cons x xs ih =>
    intro a h
    rw [List.foldl_cons] at h
    rcases pickLonger_cases (some a) x with hx | hkeep
    · rw [hx] at h; exact ih x h
    · rw [hkeep] at h; exact ih a h

private theorem foldl_pickLonger_max {F E : Type*} :
    ∀ (l : List (FeatureVI F E)) (acc : Option (FeatureVI F E))
      (i : FeatureVI F E), l.foldl pickLonger acc = some i →
      (∀ j ∈ l, j.features.length ≤ i.features.length) ∧
        ∀ a, acc = some a → a.features.length ≤ i.features.length := by
  intro l
  induction l with
  | nil =>
    intro acc i h
    refine ⟨by simp, fun a ha => ?_⟩
    rw [ha] at h
    obtain rfl := Option.some.inj h
    exact Nat.le_refl _
  | cons x xs ih =>
    intro acc i h
    rw [List.foldl_cons] at h
    obtain ⟨hxs, hstep⟩ := ih (pickLonger acc x) i h
    have hx : x.features.length ≤ i.features.length := by
      cases acc with
      | none => exact hstep x rfl
      | some prev =>
        by_cases hlen : x.features.length > prev.features.length
        · exact hstep x (by simp [pickLonger, hlen])
        · have := hstep prev (by simp [pickLonger, hlen])
          omega
    refine ⟨fun j hj => ?_, fun a ha => ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · exact hx
      · exact hxs j hj'
    · subst ha
      by_cases hlen : x.features.length > a.features.length
      · omega
      · have := hstep a (by simp [pickLonger, hlen])
        omega

/-- The winner is an applicable item. -/
theorem winner?_mem {F E : Type*} [BEq F]
    {items : List (FeatureVI F E)} {target : List F} {i : FeatureVI F E}
    (h : winner? items target = some i) : i ∈ applicable items target := by
  rcases foldl_choice_mem pickLonger_cases h with hmem | hnone
  · exact hmem
  · exact absurd hnone (by simp)

/-- The winner belongs to the vocabulary and draws only on features the
target bears. -/
theorem winner?_spec {F E : Type*} [BEq F]
    {items : List (FeatureVI F E)} {target : List F} {i : FeatureVI F E}
    (h : winner? items target = some i) :
    i ∈ items ∧ i.features.all (target.contains ·) = true := by
  have := List.mem_filter.mp (winner?_mem h)
  exact ⟨this.1, this.2⟩

/-- The Subset Principle's exponent comes from an applicable vocabulary
item — the selection never draws on features the node does not bear. -/
theorem subsetPrinciple_winner_mem {F E : Type*} [BEq F]
    {items : List (FeatureVI F E)} {target : List F} {e : E}
    (h : subsetPrinciple items target = some e) :
    ∃ i ∈ items, i.exponent = e ∧ i.features.all (target.contains ·) = true := by
  obtain ⟨i, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hi, happ⟩ := winner?_spec hw
  exact ⟨i, hi, rfl, happ⟩

/-- `winner?` succeeds iff some item is applicable. -/
theorem winner?_isSome_iff {F E : Type*} [BEq F]
    {items : List (FeatureVI F E)} {target : List F} :
    (winner? items target).isSome ↔ applicable items target ≠ [] := by
  unfold winner?
  cases hl : applicable items target with
  | nil => simp
  | cons x xs =>
    simp only [List.foldl_cons, ne_eq, reduceCtorEq, not_false_eq_true,
      iff_true]
    have hstep : pickLonger (none : Option (FeatureVI F E)) x = some x := rfl
    rw [hstep, Option.isSome_iff_ne_none]
    exact foldl_pickLonger_ne_none xs x

/-- The winner is maximally specific among the applicable items. -/
theorem winner?_max {F E : Type*} [BEq F]
    {items : List (FeatureVI F E)} {target : List F} {i : FeatureVI F E}
    (h : winner? items target = some i) :
    ∀ j ∈ applicable items target, j.features.length ≤ i.features.length :=
  (foldl_pickLonger_max _ _ _ h).1

/-- Applicability is monotone in the target bundle. -/
theorem applicable_mono {F E : Type*} [BEq F]
    {items : List (FeatureVI F E)} {t t' : List F}
    (hsub : ∀ x, t'.contains x = true → t.contains x = true) :
    ∀ i ∈ applicable items t', i ∈ applicable items t := by
  intro i hi
  obtain ⟨him, hall⟩ := List.mem_filter.mp hi
  refine List.mem_filter.mpr ⟨him, ?_⟩
  rw [List.all_eq_true] at hall ⊢
  exact fun x hx => hsub x (hall x hx)

/-- **Retreat to the general case**: shrinking the target — deleting
features by Impoverishment — can only make the Subset-Principle winner
weakly less specific, which is why impoverishment yields syncretism with
a more general exponent rather than a different specific one
([halle-marantz-1993], [arregi-nevins-2012]). -/
theorem winner?_retreat {F E : Type*} [BEq F]
    {items : List (FeatureVI F E)} {t t' : List F} {i' : FeatureVI F E}
    (hsub : ∀ x, t'.contains x = true → t.contains x = true)
    (h' : winner? items t' = some i') :
    ∃ i, winner? items t = some i ∧
      i'.features.length ≤ i.features.length := by
  have hmem : i' ∈ applicable items t :=
    applicable_mono hsub _ (winner?_mem h')
  have hne : applicable items t ≠ [] := fun hnil => by simp [hnil] at hmem
  obtain ⟨i, hi⟩ :=
    Option.isSome_iff_exists.mp (winner?_isSome_iff.mpr hne)
  exact ⟨i, hi, winner?_max hi _ hmem⟩

-- ============================================================================
-- § 3: The shared exponence core
-- ============================================================================

section ExponenceCore

open Morphology.Exponence

variable {Ctx Root : Type*}

/-- The stipulated `specificity` rank is **faithful** when it refines
the derived specificity of the shared core: a strictly more specific
item always outranks. With opaque `contextMatch` predicates the derived
order is not computable, so this engine must stipulate a rank — this
Prop is the obligation the stipulation incurs, and
`vocabularyInsert_isElsewhereWinner` is what discharging it buys. -/
def SpecificityFaithful (rules : List (VocabItem Ctx Root)) : Prop :=
  ∀ a ∈ rules, ∀ b ∈ rules, a ≤ b → ¬ b ≤ a → b.specificity < a.specificity

/-- Under a faithful specificity stipulation, the engine's selection is
an Elsewhere winner of the shared core. -/
theorem vocabularyInsert_isElsewhereWinner {rules : List (VocabItem Ctx Root)}
    {ctx : Ctx} {root : Root} {e : String}
    (h : vocabularyInsert rules ctx root = some e)
    (hf : SpecificityFaithful rules) :
    ∃ vi ∈ rules, vi.exponent = e ∧ IsElsewhereWinner rules (ctx, root) vi := by
  obtain ⟨vi, hvi, hve⟩ := Option.map_eq_some_iff.mp h
  exact ⟨vi, selectBy_mem hvi, hve, selectBy_isElsewhereWinner
    (λ a ha b hb hab => hf a (mem_applicable.mp ha).1 b (mem_applicable.mp hb).1
      (lt_iff_le_not_ge.mp hab).1 (lt_iff_le_not_ge.mp hab).2) hvi⟩

end ExponenceCore

/-! ### The realization view -/

/-- Vocabulary Insertion as a realization: roots as opaque indices,
syntactic
contexts as contexts, `none` as non-licensing — the univalent stratum. -/
def toRealization {Ctx Root : Type*} (rules : List (VocabItem Ctx Root)) :
    Morphology.Realization Root Ctx String :=
  ⟨fun r c => match vocabularyInsert rules c r with
    | some f => {f}
    | none => ∅⟩

theorem toRealization_isUnivalent {Ctx Root : Type*}
    (rules : List (VocabItem Ctx Root)) : (toRealization rules).IsUnivalent :=
  fun r c => by
    simp only [toRealization]
    cases vocabularyInsert rules c r <;> simp

end DistributedMorphology.VI
