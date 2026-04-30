/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Theories.Phonology.Subregular.OCP
import Mathlib.Data.List.Chain

/-!
# OCP-as-Merger — the canonical normal form
@cite{goldsmith-1976} @cite{mccarthy-1981} @cite{burzio-1998}
@cite{mccarthy-1995}

Two readings of the OCP coexist in the autosegmental and computational
traditions:

* **Prohibition** (@cite{mccarthy-1986}): adjacent identical autosegments
  are *rejected* — a constraint on output well-formedness. Formalised
  in `Linglib/Theories/Phonology/Subregular/OCP.lean` as
  `TSLGrammar.ocp p`.
* **Merger / repair** (@cite{goldsmith-1976}, @cite{burzio-1998}'s
  Multiple Correspondence, @cite{mccarthy-1995}): adjacent identical
  autosegments are *collapsed* into a single multiply-linked
  autosegment — a transformation on representations.

This file provides the **substrate operation for the merger reading at
full generality** — `Tier.ocpCollapse` over `List α` for any
`DecidableEq α` — and the bridge to the prohibition reading: the
canonical-form output is OCP-clean.

## Why this is shared substrate

Both `Phonology.Autosegmental.RegisterTier.mergeTRN` (Lionnet 2022 Laal
tones) and the |A|+|A| fusion of @cite{faust-lampitelli-2026}
(Tigrinya/Tigre guttural synseresis) are instances of the same
operation on different feature spaces. The bundle-level
`FeatureBundle.merge` (in `Featural/Bundle.lean`) is an OR-of-Option
building block at one level below; the OCP operation lives at the
**tier level** and is identity-driven.

The `combine` argument resolves framework-specific side-information
when two elements are equal under `DecidableEq` but carry payload
(e.g. Element-Theory headedness). The default `fun a _ => a` is correct
for strict identity (LHS preserved unchanged).

## Convention: predicates as `Prop`

Following mathlib + the existing `Phonology.Subregular.OCP` style
(see `OCPCleanPair : Prop` there), predicates in this file are
`Prop`-valued with `Decidable` instances. `decide` recovers
computability for closed instances.

The OCP-cleanness predicate is defined directly via `List.Chain'
(· ≠ ·)` — mathlib's "no two adjacent satisfy R" predicate at
`R := (· ≠ ·)`. This pattern reuses `OptimalityTheory.Correspondence`'s
`IsContiguous` style (which uses `List.IsChain`) and slots into
mathlib's chain lemmas for free.
-/

namespace Phonology.Tier

variable {α : Type*}

-- ============================================================================
-- § 1: The Canonical Normal Form
-- ============================================================================

/-- Helper: walk the tail of a list with a "running" head `x`. If the
    next element equals `x`, collapse via `combine` and continue with
    the merged head. Otherwise, emit `x` and continue with the next
    element as the new running head. Structurally recursive on the
    tail. -/
private def ocpCollapseAux [DecidableEq α] (combine : α → α → α)
    (x : α) : List α → List α
  | []        => [x]
  | y :: rs =>
      if x = y then ocpCollapseAux combine (combine x y) rs
      else x :: ocpCollapseAux combine y rs

/-- **OCP-merger normal form** at the tier level: collapse each maximal
    run of identical adjacent elements into a single element via
    `combine`. Default `combine := fun a _ => a` preserves the LHS,
    correct for strict-identity merges (Lionnet TRN OCP). -/
def ocpCollapse [DecidableEq α] (combine : α → α → α := fun a _ => a) :
    List α → List α
  | []        => []
  | x :: rest => ocpCollapseAux combine x rest

@[simp] theorem ocpCollapse_nil [DecidableEq α] (combine : α → α → α) :
    ocpCollapse combine ([] : List α) = [] := rfl

@[simp] theorem ocpCollapse_singleton [DecidableEq α] (combine : α → α → α)
    (x : α) : ocpCollapse combine [x] = [x] := rfl

private theorem ocpCollapseAux_nil [DecidableEq α] (combine : α → α → α) (x : α) :
    ocpCollapseAux combine x [] = [x] := rfl

private theorem ocpCollapseAux_cons_eq [DecidableEq α] (combine : α → α → α)
    (x : α) (rs : List α) :
    ocpCollapseAux combine x (x :: rs) = ocpCollapseAux combine (combine x x) rs := by
  simp only [ocpCollapseAux, ↓reduceIte]

private theorem ocpCollapseAux_cons_ne [DecidableEq α] (combine : α → α → α)
    {x y : α} (h : x ≠ y) (rs : List α) :
    ocpCollapseAux combine x (y :: rs) = x :: ocpCollapseAux combine y rs := by
  simp only [ocpCollapseAux, if_neg h]

-- ============================================================================
-- § 2: OCP-Cleanness Predicate
-- ============================================================================

/-- A list is **OCP-clean** iff no adjacent pair is identical — the
    universal-tier instance of the OCP. Implemented as the
    @cite{mccarthy-1986} prohibition condition over the entire string,
    via mathlib's `List.IsChain` predicate at `R := (· ≠ ·)`. -/
def IsOCPClean [DecidableEq α] (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

instance [DecidableEq α] (xs : List α) : Decidable (IsOCPClean xs) :=
  inferInstanceAs (Decidable (List.IsChain _ xs))

@[simp] theorem isOCPClean_nil [DecidableEq α] :
    IsOCPClean ([] : List α) := List.isChain_nil

@[simp] theorem isOCPClean_singleton [DecidableEq α] (x : α) :
    IsOCPClean [x] := List.isChain_singleton x

theorem isOCPClean_cons_cons_iff [DecidableEq α] (x y : α) (rs : List α) :
    IsOCPClean (x :: y :: rs) ↔ x ≠ y ∧ IsOCPClean (y :: rs) := by
  unfold IsOCPClean
  rw [List.isChain_cons]
  refine ⟨fun ⟨h1, h2⟩ => ⟨?_, h2⟩, fun ⟨h1, h2⟩ => ⟨?_, h2⟩⟩
  · exact h1 y (by simp [List.head?])
  · intro z hz
    simp [List.head?] at hz
    exact hz ▸ h1

-- ============================================================================
-- § 3: Head Preservation (helper for clean-form)
-- ============================================================================

/-- Under `combine x x = x`, `ocpCollapseAux x xs` always starts with
    `x`. The output is `x :: rest'` for some tail `rest'`. -/
private theorem ocpCollapseAux_head [DecidableEq α] (combine : α → α → α)
    (h : ∀ z : α, combine z z = z) :
    ∀ (x : α) (xs : List α), ∃ rest, ocpCollapseAux combine x xs = x :: rest := by
  intro x xs
  induction xs generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons y rs ih =>
    by_cases hxy : x = y
    · rw [hxy, ocpCollapseAux_cons_eq combine y rs, h y]
      exact ih y
    · rw [ocpCollapseAux_cons_ne combine hxy rs]
      exact ⟨ocpCollapseAux combine y rs, rfl⟩

/-- Under `combine x x = x`, `ocpCollapse` preserves the head. -/
theorem ocpCollapse_head [DecidableEq α] (combine : α → α → α)
    (h : ∀ z : α, combine z z = z) (x : α) (xs : List α) :
    ∃ rest, ocpCollapse combine (x :: xs) = x :: rest :=
  ocpCollapseAux_head combine h x xs

-- ============================================================================
-- § 4: Substrate Theorems
-- ============================================================================

variable [DecidableEq α]

/-- **OCP-cleanness of the canonical form**: after `ocpCollapse`, no two
    adjacent elements are identical. The bridge from the merger reading
    to the prohibition reading.

    Requires `combine x x = x`. The default `fun a _ => a` satisfies
    this trivially; ET's `headedWins` does too. -/
private theorem ocpCollapseAux_clean (combine : α → α → α)
    (h : ∀ z : α, combine z z = z) :
    ∀ (x : α) (xs : List α), IsOCPClean (ocpCollapseAux combine x xs) := by
  intro x xs
  induction xs generalizing x with
  | nil =>
    rw [ocpCollapseAux_nil]
    exact isOCPClean_singleton x
  | cons y rs ih =>
    by_cases hxy : x = y
    · rw [hxy, ocpCollapseAux_cons_eq combine y rs, h y]
      exact ih y
    · rw [ocpCollapseAux_cons_ne combine hxy rs]
      obtain ⟨rest', heq⟩ := ocpCollapseAux_head combine h y rs
      rw [heq]
      rw [isOCPClean_cons_cons_iff]
      refine ⟨hxy, ?_⟩
      rw [← heq]
      exact ih y

/-- **OCP-cleanness of the canonical form** (top-level). -/
theorem ocpCollapse_clean (combine : α → α → α)
    (h : ∀ z : α, combine z z = z) (xs : List α) :
    IsOCPClean (ocpCollapse combine xs) := by
  cases xs with
  | nil => exact isOCPClean_nil
  | cons x rest => exact ocpCollapseAux_clean combine h x rest

/-- **Idempotence on a clean list**: `ocpCollapse` is the identity on
    OCP-clean lists. Helper for the composition-form idempotence. -/
private theorem ocpCollapseAux_idempotent_on_clean (combine : α → α → α) :
    ∀ (x : α) (xs : List α), IsOCPClean (x :: xs) →
      ocpCollapseAux combine x xs = x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil => intro _; rfl
  | cons y rs ih =>
    intro hclean
    rw [isOCPClean_cons_cons_iff] at hclean
    obtain ⟨hxy, hrest⟩ := hclean
    rw [ocpCollapseAux_cons_ne combine hxy rs]
    exact congrArg (x :: ·) (ih y hrest)

/-- **Idempotence on a clean list**: `ocpCollapse` is the identity on
    OCP-clean lists. -/
theorem ocpCollapse_idempotent_on_clean (combine : α → α → α)
    (xs : List α) (h : IsOCPClean xs) :
    ocpCollapse combine xs = xs := by
  cases xs with
  | nil => rfl
  | cons x rest => exact ocpCollapseAux_idempotent_on_clean combine x rest h

/-- **Idempotence (composition form)**: `ocpCollapse f ∘ ocpCollapse f =
    ocpCollapse f`. Closes the OCP.lean docstring's "two readings
    coexist without a master bridge" gap by establishing the merger
    operation as a normal-form algorithm whose output is the
    prohibition's accepted set. -/
theorem ocpCollapse_idempotent (combine : α → α → α)
    (h : ∀ z : α, combine z z = z) (xs : List α) :
    ocpCollapse combine (ocpCollapse combine xs) = ocpCollapse combine xs :=
  ocpCollapse_idempotent_on_clean combine _ (ocpCollapse_clean combine h xs)

end Phonology.Tier
