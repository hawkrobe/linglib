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

The categorical, strict-identity, single-tier OCP: the ban on two *identical* adjacent
autosegments on one tier ([mccarthy-1986]), on a projected tier for `IsCleanOn`
([chandlee-jardine-2019]). As a stringset the constraint is tier-based strictly local
(TSL₂, [heinz-rawal-tanner-2011]), characterised in `Phonology.Subregular.OCP`. The
fusion repair `collapse` is mathlib's
`List.destutter (· ≠ ·)` ([goldsmith-1976], [mccarthy-prince-1995]) — a retraction onto
cleanness, input-strictly-local ([chandlee-heinz-2018]); the blocking repair `block` is
antigemination, a guard rather than a retraction ([mccarthy-1986]).

Gradient, similarity-scaled OCP ([frisch-pierrehumbert-broe-2004]) is a different object
and lives in the thresholded-TSL substrate, not here.

## Main definitions

* `OCP.IsClean` / `OCP.IsCleanOn` — OCP-cleanness, flat and on a projected tier.
* `OCP.collapse` — the fusion repair (OCP-merger normal form).
* `OCP.block` — the blocking repair (antigemination guard).

## Main results

* `collapse_eq_destutter` — the fusion repair is `List.destutter`.
* `collapse_clean` / `collapse_eq_self_iff` — `collapse` is the retraction onto `IsClean`.
* `collapse_sublist` — fusion never adds material.
* `block_eq_self` — antigemination: a rule is blocked when it would violate the OCP.
-/

namespace Phonology.OCP

variable {α : Type*}

/-! ### The constraint -/

/-- A tier is **OCP-clean** when no adjacent pair is identical ([mccarthy-1986]'s
prohibition condition). Adjacency-only, so strictly weaker than `List.Nodup`
(`[1, 2, 1]` is clean): `Nodup` lemmas do not transfer. -/
def IsClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isClean_nil : IsClean ([] : List α) := List.isChain_nil

@[simp] theorem isClean_singleton (x : α) : IsClean [x] := List.isChain_singleton x

@[simp] theorem isClean_cons_cons_iff (x y : α) (rs : List α) :
    IsClean (x :: y :: rs) ↔ x ≠ y ∧ IsClean (y :: rs) := by
  simp only [IsClean, List.isChain_cons_cons]

/-- OCP on the tier projected from `xs` by keeping `p`-elements and reading `proj`
(tier-relativity, [chandlee-jardine-2019]); flat `IsClean` is the `p = ⊤`, `proj = id` case. -/
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

/-- **OCP-merger normal form** (the fusion repair): collapse each maximal run of
identical adjacent elements into one. Fusing identical autosegments returns that same
autosegment, so the payload is unchanged. -/
def collapse (xs : List α) : List α := xs.destutter (· ≠ ·)

theorem collapse_eq_destutter (xs : List α) : collapse xs = xs.destutter (· ≠ ·) := rfl

@[simp] theorem collapse_nil : collapse ([] : List α) = [] := by simp [collapse]

@[simp] theorem collapse_singleton (x : α) : collapse [x] = [x] := by simp [collapse]

/-- `collapse` lands in the OCP-clean set. -/
theorem collapse_clean (xs : List α) : IsClean (collapse xs) :=
  List.isChain_destutter _ xs

/-- `collapse` fixes OCP-clean lists. -/
theorem collapse_idempotent_on_clean {xs : List α} (h : IsClean xs) : collapse xs = xs :=
  List.destutter_of_isChain _ xs h

/-- `collapse` fixes a tier iff it is OCP-clean; with `collapse_clean`, the retraction
onto `IsClean`. -/
@[simp] theorem collapse_eq_self_iff (xs : List α) : collapse xs = xs ↔ IsClean xs :=
  List.destutter_eq_self_iff _ xs

/-- The fusion repair is a retraction onto the OCP-clean set. -/
theorem collapse_idempotent (xs : List α) : collapse (collapse xs) = collapse xs :=
  List.destutter_idem _ _

/-! ### Normal-form lemmas -/

@[simp] theorem collapse_eq_nil {xs : List α} : collapse xs = [] ↔ xs = [] :=
  List.destutter_eq_nil _

/-- Fusion never adds material: the repair output is a sublist of the input. -/
theorem collapse_sublist (xs : List α) : (collapse xs).Sublist xs :=
  List.destutter_sublist _ xs

theorem collapse_length_le (xs : List α) : (collapse xs).length ≤ xs.length :=
  (collapse_sublist xs).length_le

theorem mem_collapse {a : α} {xs : List α} (ha : a ∈ collapse xs) : a ∈ xs :=
  (collapse_sublist xs).mem ha

/-! ### The blocking repair -/

/-- **Blocking** ([mccarthy-1986]'s antigemination): apply `rule` only when it would not
create an OCP violation, else leave the input untouched — a guard preventing a process,
not a retraction repairing its output. -/
def block (rule : List α → List α) (xs : List α) : List α :=
  if IsClean (rule xs) then rule xs else xs

theorem block_eq_rule (rule : List α → List α) {xs : List α} (hc : IsClean (rule xs)) :
    block rule xs = rule xs := if_pos hc

/-- Antigemination: the rule fails to apply exactly when it would create an OCP
violation, leaving the input unrepaired (contrast `collapse`). -/
theorem block_eq_self (rule : List α → List α) {xs : List α} (hc : ¬ IsClean (rule xs)) :
    block rule xs = xs := if_neg hc

/-- Blocking never worsens a clean tier. -/
theorem block_isClean (rule : List α → List α) {xs : List α} (hx : IsClean xs) :
    IsClean (block rule xs) := by
  unfold block; split <;> assumption

end

end Phonology.OCP
