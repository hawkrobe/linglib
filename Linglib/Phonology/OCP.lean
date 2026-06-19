/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Destutter

/-!
# The Obligatory Contour Principle

[mccarthy-1986] [goldsmith-1976] [mccarthy-prince-1995]
[heinz-rawal-tanner-2011] [chandlee-heinz-2018] [chandlee-jardine-2019]

This file formalises the **categorical, strict-identity, single-tier** OCP — the
reading that bans two *identical* adjacent autosegments on one tier. (Gradient,
similarity-scaled OCP — [frisch-pierrehumbert-broe-2004]'s Arabic OCP-Place,
which proves no categorical model fits its data — is a different object and lives
in the thresholded-TSL substrate, not here.) It has three faces, unified around
one satisfaction predicate `OCP.IsClean`.

* **The constraint** — `OCP.IsClean`: no two adjacent elements are identical
  (`List.IsChain (· ≠ ·)`); the prohibition reading ([mccarthy-1986]). On a
  *projected* tier this is `OCP.IsCleanOn` — the OCP is intrinsically
  tier-relative ([chandlee-jardine-2019]). As a stringset the constraint is
  **tier-based strictly local** (TSL₂, [heinz-rawal-tanner-2011]).
* **The repairs** — a tier transformation enforces the OCP when it lands in the
  clean set. The fusion/merger repair ([goldsmith-1976], [mccarthy-prince-1995]'s
  Correspondence, [burzio-1998]'s Multiple Correspondence) collapses each run of
  identical adjacent elements into one (multiply-linked) element: `OCP.collapse`.
  Its output is clean (`collapse_clean`) and it fixes already-clean tiers
  (`collapse_idempotent_on_clean`), i.e. a **retraction onto `IsClean`**. As a
  string map `collapse` is input-strictly-local ([chandlee-heinz-2018]); on an
  autosegmental tier the OCP repairs are A-ISL ([chandlee-jardine-2019]).
* **The subregular characterization** — that the constraint is a TSL₂ language
  lives in `Phonology.Subregular.OCP` (`mkOCPOnTier_zero_iff_isClean`), which
  consumes this `IsClean`.

`collapse` generalises mathlib's `List.destutter (· ≠ ·)`
(`collapse_default_eq_destutter`) with a `combine : α → α → α` argument that
resolves framework-specific payload when two elements are equal under
`DecidableEq` but carry side-information (e.g. Element-Theory headedness,
register-tier `[upper]`/`[raised]`). The default `fun a _ => a` keeps the left
element; `RegisterTier.mergeTRN` is the payload-merging `combine` for the tone
tier (its `combine z z = z` obligation is `mergeTRN_self`).

McCarthy's ([mccarthy-1986]) wider repair typology (deletion, dissimilation,
epenthesis, and crucially *blocking* — the antigemination case that is
[mccarthy-1986]'s own central phenomenon) is intentionally **not** implemented
here: only repairs with an actual consumer are coded. Note that a *blocker* is
not a retraction onto `IsClean` but a guard, so it (not fusion) is the strategy
that will earn the deferred `Repair` abstraction.

## Main definitions

* `OCP.IsClean` — no two adjacent elements are identical.
* `OCP.IsCleanOn` — the OCP on a projected tier (tier-relativity).
* `OCP.collapse` — the OCP-merger normal form (fusion repair).

## Main results

* `collapse_default_eq_destutter` — the default merge is `List.destutter`.
* `collapse_clean` — the repair lands in the OCP-clean set.
* `collapse_idempotent` — the repair is idempotent (a retraction).
-/

namespace Phonology.OCP

variable {α : Type*}

/-! ### The constraint -/

/-- A tier is **OCP-clean** when no adjacent pair is identical — the
[mccarthy-1986] prohibition condition over the whole tier, as mathlib's
`List.IsChain (· ≠ ·)`.

Adjacency-only, hence strictly weaker than `List.Nodup` (`[1, 2, 1]` is clean but
not nodup, as `(· ≠ ·)` is not transitive): `Nodup`/sublist-closure lemmas do not
transfer. -/
def IsClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isClean_nil : IsClean ([] : List α) := List.isChain_nil

@[simp] theorem isClean_singleton (x : α) : IsClean [x] := List.isChain_singleton x

@[simp] theorem isClean_cons_cons_iff (x y : α) (rs : List α) :
    IsClean (x :: y :: rs) ↔ x ≠ y ∧ IsClean (y :: rs) := by
  simp only [IsClean, List.isChain_cons_cons]

/-- OCP on the tier projected from `xs` by keeping the `p`-elements and reading
`proj` (autosegmental tier-relativity, [chandlee-jardine-2019]). The flat
`IsClean` is the `p = ⊤`, `proj = id` case. -/
def IsCleanOn {β : Type*} (p : α → Prop) [DecidablePred p] (proj : α → β)
    (xs : List α) : Prop :=
  IsClean ((xs.filter (fun a => decide (p a))).map proj)

instance decidableIsClean [DecidableEq α] : DecidablePred (IsClean (α := α)) :=
  fun xs => inferInstanceAs (Decidable (List.IsChain (· ≠ ·) xs))

instance decidableIsCleanOn {β : Type*} [DecidableEq β] (p : α → Prop)
    [DecidablePred p] (proj : α → β) : DecidablePred (IsCleanOn p proj) :=
  fun _ => inferInstanceAs (Decidable (IsClean _))

section
variable [DecidableEq α]

/-! ### The fusion repair -/

/-- Helper: walk the tail of a list with a "running" head `x`. If the next
element equals `x`, collapse via `combine` and continue with the merged head.
Otherwise, emit `x` and continue with the next element as the new running head.
Structurally recursive on the tail. -/
private def collapseAux (combine : α → α → α) (x : α) : List α → List α
  | []        => [x]
  | y :: rs =>
      if x = y then collapseAux combine (combine x y) rs
      else x :: collapseAux combine y rs

/-- **OCP-merger normal form** (the fusion repair): collapse each maximal run of
identical adjacent elements into a single element via `combine`. Default
`combine := fun a _ => a` preserves the LHS, correct for strict-identity merges;
`RegisterTier.mergeTRN` is the payload-merging `combine` on the tone tier. -/
def collapse (combine : α → α → α := fun a _ => a) : List α → List α
  | []        => []
  | x :: rest => collapseAux combine x rest

@[simp] theorem collapse_nil (combine : α → α → α) :
    collapse combine ([] : List α) = [] := rfl

@[simp] theorem collapse_singleton (combine : α → α → α) (x : α) :
    collapse combine [x] = [x] := rfl

private theorem collapseAux_nil (combine : α → α → α) (x : α) :
    collapseAux combine x [] = [x] := rfl

private theorem collapseAux_cons_eq (combine : α → α → α) (x : α) (rs : List α) :
    collapseAux combine x (x :: rs) = collapseAux combine (combine x x) rs := by
  simp only [collapseAux, ↓reduceIte]

private theorem collapseAux_cons_ne (combine : α → α → α) {x y : α} (h : x ≠ y)
    (rs : List α) :
    collapseAux combine x (y :: rs) = x :: collapseAux combine y rs := by
  simp only [collapseAux, if_neg h]

/-- Under `combine x x = x`, collapsing a run that starts with a duplicate head
drops the duplicate. The shared step in the head- and cleanness-preservation
proofs. -/
private theorem collapseAux_self (combine : α → α → α) (h : ∀ z : α, combine z z = z)
    (x : α) (rs : List α) :
    collapseAux combine x (x :: rs) = collapseAux combine x rs := by
  rw [collapseAux_cons_eq, h]

private theorem collapse_default_eq_destutter_aux (x : α) (rs : List α) :
    collapseAux (fun a _ => a) x rs = List.destutter' (· ≠ ·) x rs := by
  induction rs generalizing x with
  | nil => rfl
  | cons y rs ih =>
    simp only [collapseAux, List.destutter'_cons]
    by_cases hxy : x = y <;> simp [hxy, ih]

/-- The default merge `fun a _ => a` is mathlib's `List.destutter (· ≠ ·)`:
`collapse` is its payload-merging generalisation. -/
theorem collapse_default_eq_destutter (xs : List α) :
    collapse (fun a _ => a) xs = xs.destutter (· ≠ ·) := by
  cases xs with
  | nil => rfl
  | cons x rest => rw [List.destutter_cons']; exact collapse_default_eq_destutter_aux x rest

/-! ### Head preservation -/

/-- Under `combine x x = x`, `collapseAux x xs` always starts with `x`. -/
private theorem collapseAux_head (combine : α → α → α) (h : ∀ z : α, combine z z = z) :
    ∀ (x : α) (xs : List α), ∃ rest, collapseAux combine x xs = x :: rest := by
  intro x xs
  induction xs generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons y rs ih =>
    by_cases hxy : x = y
    · rw [hxy, collapseAux_self combine h]
      exact ih y
    · rw [collapseAux_cons_ne combine hxy rs]
      exact ⟨collapseAux combine y rs, rfl⟩

/-- Under `combine x x = x`, `collapse` preserves the head. -/
theorem collapse_head (combine : α → α → α) (h : ∀ z : α, combine z z = z) (x : α)
    (xs : List α) :
    ∃ rest, collapse combine (x :: xs) = x :: rest :=
  collapseAux_head combine h x xs

/-! ### Retraction onto the clean set -/

/-- **OCP-cleanness of the repair output**: after `collapse`, no two adjacent
elements are identical. Requires `combine x x = x`; the default `fun a _ => a`
satisfies this trivially, as does `RegisterTier.mergeTRN` (`mergeTRN_self`). -/
private theorem collapseAux_clean (combine : α → α → α) (h : ∀ z : α, combine z z = z) :
    ∀ (x : α) (xs : List α), IsClean (collapseAux combine x xs) := by
  intro x xs
  induction xs generalizing x with
  | nil => rw [collapseAux_nil]; exact isClean_singleton x
  | cons y rs ih =>
    by_cases hxy : x = y
    · rw [hxy, collapseAux_self combine h]
      exact ih y
    · rw [collapseAux_cons_ne combine hxy rs]
      obtain ⟨rest', heq⟩ := collapseAux_head combine h y rs
      rw [heq, isClean_cons_cons_iff]
      exact ⟨hxy, heq ▸ ih y⟩

/-- **OCP-cleanness of the repair output** (top-level): `collapse` lands in the
OCP-clean set. -/
theorem collapse_clean (combine : α → α → α) (h : ∀ z : α, combine z z = z) (xs : List α) :
    IsClean (collapse combine xs) := by
  cases xs with
  | nil => exact isClean_nil
  | cons x rest => exact collapseAux_clean combine h x rest

/-- **Identity on clean tiers**: `collapse` fixes OCP-clean lists. With
`collapse_clean`, this makes `collapse` a retraction onto `IsClean`. -/
private theorem collapseAux_idempotent_on_clean (combine : α → α → α) :
    ∀ (x : α) (xs : List α), IsClean (x :: xs) → collapseAux combine x xs = x :: xs := by
  intro x xs
  induction xs generalizing x with
  | nil => intro _; rfl
  | cons y rs ih =>
    intro hclean
    obtain ⟨hxy, hrest⟩ := (isClean_cons_cons_iff x y rs).mp hclean
    rw [collapseAux_cons_ne combine hxy rs]
    exact congrArg (x :: ·) (ih y hrest)

/-- **Identity on clean tiers**: `collapse` fixes OCP-clean lists. -/
theorem collapse_idempotent_on_clean (combine : α → α → α) (xs : List α)
    (h : IsClean xs) :
    collapse combine xs = xs := by
  cases xs with
  | nil => rfl
  | cons x rest => exact collapseAux_idempotent_on_clean combine x rest h

/-- **Idempotence**: `collapse f ∘ collapse f = collapse f`. The fusion repair is
a retraction onto the OCP-clean set — its image is the prohibition's accepted set. -/
theorem collapse_idempotent (combine : α → α → α) (h : ∀ z : α, combine z z = z)
    (xs : List α) :
    collapse combine (collapse combine xs) = collapse combine xs :=
  collapse_idempotent_on_clean combine _ (collapse_clean combine h xs)

end

end Phonology.OCP
