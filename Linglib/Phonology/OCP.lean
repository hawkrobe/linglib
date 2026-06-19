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
similarity-scaled OCP — [frisch-pierrehumbert-broe-2004]'s Arabic OCP-Place, which
proves no categorical model fits its data — is a different object and lives in the
thresholded-TSL substrate, not here.) It has three faces, unified around one
satisfaction predicate `OCP.IsClean`.

* **The constraint** — `OCP.IsClean`: no two adjacent elements are identical
  (`List.IsChain (· ≠ ·)`); the prohibition reading ([mccarthy-1986]). On a
  *projected* tier this is `OCP.IsCleanOn` — the OCP is intrinsically tier-relative
  ([chandlee-jardine-2019]). As a stringset the constraint is **tier-based strictly
  local** (TSL₂, [heinz-rawal-tanner-2011]).
* **The repairs** — a tier transformation enforces the OCP when it lands in the
  clean set. The fusion/merger repair ([goldsmith-1976], [mccarthy-prince-1995]'s
  Correspondence, [burzio-1998]'s Multiple Correspondence) collapses each run of
  identical adjacent elements into one (multiply-linked) element: `OCP.collapse`.
  Its output is clean (`collapse_clean`) and it fixes already-clean tiers
  (`collapse_idempotent_on_clean`), i.e. a **retraction onto `IsClean`**. As a string
  map `collapse` is input-strictly-local ([chandlee-heinz-2018]); on an autosegmental
  tier the OCP repairs are A-ISL ([chandlee-jardine-2019]).
* **The subregular characterization** — that the constraint is a TSL₂ language lives
  in `Phonology.Subregular.OCP` (`mkOCPOnTier_zero_iff_isClean`), which consumes this
  `IsClean`.

`collapse` is exactly mathlib's `List.destutter (· ≠ ·)` (`collapse_eq_destutter`),
inheriting its API. (The fusion repair once carried a payload-merging
`combine : α → α → α` argument; since it only ever merges *equal* autosegments,
`combine` was vacuous and has been dropped.)

The repair face has two strategies of different mathematical shape. *Fusion*
(`collapse`) is a **retraction** onto `IsClean` (`collapse_eq_self_iff`), never adding
material (`collapse_sublist`). *Blocking* (`block`, [mccarthy-1986]'s antigemination —
its own central phenomenon) is a **guard**: it withholds a rule that would create a
violation (`block_eq_self`), leaving the input unrepaired, and is therefore *not* a
retraction. The remaining classical repairs (deletion, dissimilation, epenthesis) are
not coded — only strategies with a consumer are.

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

/-- A tier is **OCP-clean** when no adjacent pair is identical — the [mccarthy-1986]
prohibition condition over the whole tier, as mathlib's `List.IsChain (· ≠ ·)`.

Adjacency-only, hence strictly weaker than `List.Nodup` (`[1, 2, 1]` is clean but not
nodup, as `(· ≠ ·)` is not transitive): `Nodup`/sublist-closure lemmas do not transfer. -/
def IsClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isClean_nil : IsClean ([] : List α) := List.isChain_nil

@[simp] theorem isClean_singleton (x : α) : IsClean [x] := List.isChain_singleton x

@[simp] theorem isClean_cons_cons_iff (x y : α) (rs : List α) :
    IsClean (x :: y :: rs) ↔ x ≠ y ∧ IsClean (y :: rs) := by
  simp only [IsClean, List.isChain_cons_cons]

/-- OCP on the tier projected from `xs` by keeping the `p`-elements and reading `proj`
(autosegmental tier-relativity, [chandlee-jardine-2019]). The flat `IsClean` is the
`p = ⊤`, `proj = id` case. -/
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
identical adjacent elements into one. This is mathlib's `List.destutter (· ≠ ·)` — the
OCP merger is exactly the duplicate-removing normal form, since fusing a run of
*identical* autosegments returns that same autosegment (the payload is unchanged). -/
def collapse (xs : List α) : List α := xs.destutter (· ≠ ·)

theorem collapse_eq_destutter (xs : List α) : collapse xs = xs.destutter (· ≠ ·) := rfl

@[simp] theorem collapse_nil : collapse ([] : List α) = [] := by simp [collapse]

@[simp] theorem collapse_singleton (x : α) : collapse [x] = [x] := by simp [collapse]

/-- **OCP-cleanness of the repair output**: `collapse` lands in the OCP-clean set. -/
theorem collapse_clean (xs : List α) : IsClean (collapse xs) :=
  List.isChain_destutter _ xs

/-- **Identity on clean tiers**: `collapse` fixes OCP-clean lists. -/
theorem collapse_idempotent_on_clean {xs : List α} (h : IsClean xs) : collapse xs = xs :=
  List.destutter_of_isChain _ xs h

/-- **Retraction characterisation**: `collapse` fixes a tier iff it is OCP-clean. With
`collapse_clean`, `collapse` is the retraction onto `IsClean`. -/
@[simp] theorem collapse_eq_self_iff (xs : List α) : collapse xs = xs ↔ IsClean xs :=
  List.destutter_eq_self_iff _ xs

/-- **Idempotence**: the fusion repair is a retraction onto the OCP-clean set. -/
theorem collapse_idempotent (xs : List α) : collapse (collapse xs) = collapse xs :=
  List.destutter_idem _ _

/-! ### Normal-form lemmas -/

@[simp] theorem collapse_eq_nil {xs : List α} : collapse xs = [] ↔ xs = [] :=
  List.destutter_eq_nil _

/-- **Fusion never adds material**: the repair output is a sublist of the input. -/
theorem collapse_sublist (xs : List α) : (collapse xs).Sublist xs :=
  List.destutter_sublist _ xs

theorem collapse_length_le (xs : List α) : (collapse xs).length ≤ xs.length :=
  (collapse_sublist xs).length_le

theorem mem_collapse {a : α} {xs : List α} (ha : a ∈ collapse xs) : a ∈ xs :=
  (collapse_sublist xs).mem ha

/-! ### The blocking repair -/

/-- **Blocking** ([mccarthy-1986]'s antigemination): apply `rule` only when it would
not create an OCP violation; otherwise leave the input untouched. Unlike the fusion
repair `collapse`, a blocker is a *guard*, not a retraction onto `IsClean` — the OCP
acting to *prevent* a process rather than repair its output. -/
def block (rule : List α → List α) (xs : List α) : List α :=
  if IsClean (rule xs) then rule xs else xs

theorem block_eq_rule (rule : List α → List α) {xs : List α} (hc : IsClean (rule xs)) :
    block rule xs = rule xs := if_pos hc

/-- **Antigemination**: the rule fails to apply exactly when it would create an OCP
violation, leaving the input unrepaired (contrast `collapse`). -/
theorem block_eq_self (rule : List α → List α) {xs : List α} (hc : ¬ IsClean (rule xs)) :
    block rule xs = xs := if_neg hc

/-- Blocking never worsens a clean tier. -/
theorem block_isClean (rule : List α → List α) {xs : List α} (hx : IsClean xs) :
    IsClean (block rule xs) := by
  unfold block; split
  · assumption
  · exact hx

end

end Phonology.OCP
