/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Destutter

/-!
# OCP-as-merger: the canonical normal form

[goldsmith-1976] [mccarthy-1981] [mccarthy-1995] [burzio-1998]

The autosegmental tradition reads the Obligatory Contour Principle two ways.
The *prohibition* reading ([mccarthy-1986]) rejects adjacent identical
autosegments as ill-formed output (formalised as a TSL constraint in
`Phonology.Subregular.OCP`). The *merger* reading ([goldsmith-1976],
[mccarthy-1995], [burzio-1998]'s Multiple Correspondence) instead collapses
each maximal run of adjacent identical autosegments into a single
multiply-linked autosegment.

This file formalises the merger reading at the tier level as the normal form
`Tier.ocpCollapse` over `List α` for `DecidableEq α`. Its default merge is
mathlib's `List.destutter (· ≠ ·)` (`ocpCollapse_default_eq_destutter`);
`ocpCollapse` generalises it with a `combine : α → α → α` argument that resolves
framework-specific payload when two elements are equal under `DecidableEq` but
carry side-information (e.g. Element-Theory headedness). The default
`fun a _ => a` keeps the left element, correct for strict-identity merges
(Lionnet TRN OCP). The output is OCP-clean (`ocpCollapse_clean`) and the
operation is idempotent (`ocpCollapse_idempotent`), so the merger normal form
lands exactly in the prohibition reading's accepted set.

## Main definitions

* `Tier.IsOCPClean` — no two adjacent elements are identical, i.e.
  `List.IsChain (· ≠ ·)`.
* `Tier.ocpCollapse` — the OCP-merger normal form.

## Main results

* `ocpCollapse_default_eq_destutter` — the default merge is `List.destutter`.
* `ocpCollapse_clean` — the normal form is OCP-clean.
* `ocpCollapse_idempotent` — `ocpCollapse` is idempotent.
-/

namespace Phonology.Tier

variable {α : Type*}

/-! ### OCP-cleanness predicate -/

/-- A list is **OCP-clean** when no adjacent pair is identical — the
[mccarthy-1986] prohibition condition over the whole tier, as mathlib's
`List.IsChain (· ≠ ·)`. -/
def IsOCPClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isOCPClean_nil : IsOCPClean ([] : List α) := List.isChain_nil

@[simp] theorem isOCPClean_singleton (x : α) : IsOCPClean [x] := List.isChain_singleton x

@[simp] theorem isOCPClean_cons_cons_iff (x y : α) (rs : List α) :
    IsOCPClean (x :: y :: rs) ↔ x ≠ y ∧ IsOCPClean (y :: rs) := by
  simp only [IsOCPClean, List.isChain_cons_cons]

instance decidableIsOCPClean [DecidableEq α] : DecidablePred (IsOCPClean (α := α)) :=
  fun xs => inferInstanceAs (Decidable (List.IsChain (· ≠ ·) xs))

section
variable [DecidableEq α]

/-! ### The canonical normal form -/

/-- Helper: walk the tail of a list with a "running" head `x`. If the next
element equals `x`, collapse via `combine` and continue with the merged head.
Otherwise, emit `x` and continue with the next element as the new running head.
Structurally recursive on the tail. -/
private def ocpCollapseAux (combine : α → α → α) (x : α) : List α → List α
  | []        => [x]
  | y :: rs =>
      if x = y then ocpCollapseAux combine (combine x y) rs
      else x :: ocpCollapseAux combine y rs

/-- **OCP-merger normal form** at the tier level: collapse each maximal run of
identical adjacent elements into a single element via `combine`. Default
`combine := fun a _ => a` preserves the LHS, correct for strict-identity merges
(Lionnet TRN OCP). -/
def ocpCollapse (combine : α → α → α := fun a _ => a) : List α → List α
  | []        => []
  | x :: rest => ocpCollapseAux combine x rest

@[simp] theorem ocpCollapse_nil (combine : α → α → α) :
    ocpCollapse combine ([] : List α) = [] := rfl

@[simp] theorem ocpCollapse_singleton (combine : α → α → α) (x : α) :
    ocpCollapse combine [x] = [x] := rfl

private theorem ocpCollapseAux_nil (combine : α → α → α) (x : α) :
    ocpCollapseAux combine x [] = [x] := rfl

private theorem ocpCollapseAux_cons_eq (combine : α → α → α) (x : α) (rs : List α) :
    ocpCollapseAux combine x (x :: rs) = ocpCollapseAux combine (combine x x) rs := by
  simp only [ocpCollapseAux, ↓reduceIte]

private theorem ocpCollapseAux_cons_ne (combine : α → α → α) {x y : α} (h : x ≠ y)
    (rs : List α) :
    ocpCollapseAux combine x (y :: rs) = x :: ocpCollapseAux combine y rs := by
  simp only [ocpCollapseAux, if_neg h]

/-- Under `combine x x = x`, collapsing a run that starts with a duplicate head
drops the duplicate. The shared step in the head- and cleanness-preservation
proofs. -/
private theorem ocpCollapseAux_self (combine : α → α → α) (h : ∀ z : α, combine z z = z)
    (x : α) (rs : List α) :
    ocpCollapseAux combine x (x :: rs) = ocpCollapseAux combine x rs := by
  rw [ocpCollapseAux_cons_eq, h]

private theorem ocpCollapse_default_eq_destutter_aux (x : α) (rs : List α) :
    ocpCollapseAux (fun a _ => a) x rs = List.destutter' (· ≠ ·) x rs := by
  induction rs generalizing x with
  | nil => rfl
  | cons y rs ih =>
    simp only [ocpCollapseAux, List.destutter'_cons]
    by_cases hxy : x = y <;> simp [hxy, ih]

/-- The default merge `fun a _ => a` is mathlib's `List.destutter (· ≠ ·)`:
`ocpCollapse` is its payload-merging generalisation. -/
theorem ocpCollapse_default_eq_destutter (xs : List α) :
    ocpCollapse (fun a _ => a) xs = xs.destutter (· ≠ ·) := by
  cases xs with
  | nil => rfl
  | cons x rest => rw [List.destutter_cons']; exact ocpCollapse_default_eq_destutter_aux x rest

/-! ### Head preservation -/

/-- Under `combine x x = x`, `ocpCollapseAux x xs` always starts with `x`. -/
private theorem ocpCollapseAux_head (combine : α → α → α) (h : ∀ z : α, combine z z = z) :
    ∀ (x : α) (xs : List α), ∃ rest, ocpCollapseAux combine x xs = x :: rest := by
  intro x xs
  induction xs generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons y rs ih =>
    by_cases hxy : x = y
    · rw [hxy, ocpCollapseAux_self combine h]
      exact ih y
    · rw [ocpCollapseAux_cons_ne combine hxy rs]
      exact ⟨ocpCollapseAux combine y rs, rfl⟩

/-- Under `combine x x = x`, `ocpCollapse` preserves the head. -/
theorem ocpCollapse_head (combine : α → α → α) (h : ∀ z : α, combine z z = z) (x : α)
    (xs : List α) :
    ∃ rest, ocpCollapse combine (x :: xs) = x :: rest :=
  ocpCollapseAux_head combine h x xs

/-! ### Substrate theorems -/

/-- **OCP-cleanness of the canonical form**: after `ocpCollapse`, no two
adjacent elements are identical. Requires `combine x x = x`; the default
`fun a _ => a` satisfies this trivially, as does ET's `headedWins`. -/
private theorem ocpCollapseAux_clean (combine : α → α → α) (h : ∀ z : α, combine z z = z) :
    ∀ (x : α) (xs : List α), IsOCPClean (ocpCollapseAux combine x xs) := by
  intro x xs
  induction xs generalizing x with
  | nil => rw [ocpCollapseAux_nil]; exact isOCPClean_singleton x
  | cons y rs ih =>
    by_cases hxy : x = y
    · rw [hxy, ocpCollapseAux_self combine h]
      exact ih y
    · rw [ocpCollapseAux_cons_ne combine hxy rs]
      obtain ⟨rest', heq⟩ := ocpCollapseAux_head combine h y rs
      rw [heq, isOCPClean_cons_cons_iff]
      exact ⟨hxy, heq ▸ ih y⟩

/-- **OCP-cleanness of the canonical form** (top-level). -/
theorem ocpCollapse_clean (combine : α → α → α) (h : ∀ z : α, combine z z = z) (xs : List α) :
    IsOCPClean (ocpCollapse combine xs) := by
  cases xs with
  | nil => exact isOCPClean_nil
  | cons x rest => exact ocpCollapseAux_clean combine h x rest

/-- **Idempotence on a clean list**: `ocpCollapse` is the identity on OCP-clean
lists. -/
private theorem ocpCollapseAux_idempotent_on_clean (combine : α → α → α) :
    ∀ (x : α) (xs : List α), IsOCPClean (x :: xs) → ocpCollapseAux combine x xs = x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil => intro _; rfl
  | cons y rs ih =>
    intro hclean
    obtain ⟨hxy, hrest⟩ := (isOCPClean_cons_cons_iff x y rs).mp hclean
    rw [ocpCollapseAux_cons_ne combine hxy rs]
    exact congrArg (x :: ·) (ih y hrest)

/-- **Idempotence on a clean list**: `ocpCollapse` is the identity on OCP-clean
lists. -/
theorem ocpCollapse_idempotent_on_clean (combine : α → α → α) (xs : List α)
    (h : IsOCPClean xs) :
    ocpCollapse combine xs = xs := by
  cases xs with
  | nil => rfl
  | cons x rest => exact ocpCollapseAux_idempotent_on_clean combine x rest h

/-- **Idempotence**: `ocpCollapse f ∘ ocpCollapse f = ocpCollapse f`. The merger
normal form's output is the prohibition reading's accepted set. -/
theorem ocpCollapse_idempotent (combine : α → α → α) (h : ∀ z : α, combine z z = z)
    (xs : List α) :
    ocpCollapse combine (ocpCollapse combine xs) = ocpCollapse combine xs :=
  ocpCollapse_idempotent_on_clean combine _ (ocpCollapse_clean combine h xs)

end

end Phonology.Tier
