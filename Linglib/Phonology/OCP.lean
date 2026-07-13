/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Order.Monotone.Basic
import Linglib.Core.Data.List.Destutter

/-!
# The Obligatory Contour Principle

The categorical, strict-identity, single-tier OCP: the ban on two *identical* adjacent
autosegments on one tier ([leben-1973], [mccarthy-1986]), on a projected tier for `IsCleanOn`
([chandlee-jardine-2019]). As a stringset the constraint is tier-based strictly local
(TSL₂, [heinz-rawal-tanner-2011]), characterised in `OCP`. The
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
* `collapse_append` — `collapse` is the OCP congruence: collapsing each operand before `++`
  is harmless, so `collapse` descends to the OCP quotient of `(List α, ++)` (the quotient
  monoid and its presentation `⟨α | a · a = a⟩` live on the `Core.Algebra.FreeMonoid.Destutter`
  substrate; the autosegmental reading is in `Autosegmental.Collapse`).
* `block_eq_self` — antigemination: a rule is blocked when it would violate the OCP.
-/

namespace OCP

variable {α β : Type*}

/-! ### The constraint -/

/-- A tier is **OCP-clean** when no adjacent pair is identical. Adjacency-only, so
weaker than `List.Nodup` (`[1, 2, 1]` is clean). A reducible alias of the substrate
predicate `List.IsChain (· ≠ ·)`, so the substrate's `Monoid {l // l.IsChain (· ≠ ·)}`
applies to OCP-clean tiers downstream. -/
abbrev IsClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isClean_nil : IsClean ([] : List α) := List.isChain_nil

@[simp] theorem isClean_singleton (x : α) : IsClean [x] := List.isChain_singleton x

@[simp] theorem isClean_cons_cons_iff (x y : α) (rs : List α) :
    IsClean (x :: y :: rs) ↔ x ≠ y ∧ IsClean (y :: rs) := by
  simp only [IsClean, List.isChain_cons_cons]

/-- OCP on the tier projected from `xs` by keeping `p`-elements and reading `proj`
(tier-relativity, [chandlee-jardine-2019]); flat `IsClean` is the `p = ⊤`, `proj = id` case. -/
def IsCleanOn (p : α → Prop) [DecidablePred p] (proj : α → β) (xs : List α) : Prop :=
  IsClean ((xs.filter (fun a => decide (p a))).map proj)

instance decidableIsClean [DecidableEq α] : DecidablePred (IsClean (α := α)) :=
  fun xs => inferInstanceAs (Decidable (List.IsChain (· ≠ ·) xs))

instance decidableIsCleanOn [DecidableEq β] (p : α → Prop)
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

/-- `collapse` fuses a constant run into its single autosegment. -/
@[simp] theorem collapse_replicate (n : ℕ) (a : α) :
    collapse (List.replicate (n + 1) a) = [a] :=
  List.destutter_replicate (fun h => h rfl) n

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

/-! ### The OCP congruence: `collapse` as a quotient homomorphism

`collapse` descends to a homomorphism on the OCP quotient of `(List α, ++)`: collapsing
each operand before appending is harmless. This is what makes the OCP-clean tiers under
fusion-concatenation (`List.destutterConcat`) the quotient `(List α, ++)/OCP` — bundled on
the `Core.Algebra.FreeMonoid.Destutter` substrate as `FreeMonoid.destutterHom`. -/

/-- Collapsing the left operand before appending does not change the result. -/
theorem collapse_append_left (x y : List α) :
    collapse (collapse x ++ y) = collapse (x ++ y) :=
  List.destutter_append_left x y

/-- Collapsing the right operand before appending does not change the result. -/
theorem collapse_append_right (x y : List α) :
    collapse (x ++ collapse y) = collapse (x ++ y) :=
  List.destutter_append_right x y

/-- **The OCP congruence.** `collapse` is a `++`→quotient homomorphism: collapsing each
operand first is harmless. Thus `collapse` descends to the OCP quotient of `(List α, ++)`. -/
theorem collapse_append (x y : List α) :
    collapse (x ++ y) = collapse (collapse x ++ collapse y) :=
  List.destutter_append_destutter x y

/-! ### The blocking repair

The substrate provides the OCP quotient monoid (OCP-clean tiers under fusion-concatenation,
`List.destutterConcat`) and its identification with the monoid presented by idempotent
autosegments `⟨α | a · a = a⟩`
(`Core.Algebra.FreeMonoid.Destutter`). The autosegmental reading of that quotient — the
decategorification square against the categorical representation, contrasting the OCP (a
monoidal quotient) with the No-Crossing Constraint (a monoidal subcategory) — lives
downstream in `Autosegmental.Collapse`, which can see both `Autosegmental.ncc_isMonoidal` and
`Autosegmental.ocp_not_isMonoidal`. -/

variable (rule : List α → List α)

/-- **Blocking** ([mccarthy-1986]'s antigemination): apply `rule` only when it would not
create an OCP violation, else leave the input untouched — a guard preventing a process,
not a retraction repairing its output. -/
def block (xs : List α) : List α :=
  if IsClean (rule xs) then rule xs else xs

theorem block_eq_rule {xs : List α} (hc : IsClean (rule xs)) : block rule xs = rule xs := if_pos hc

/-- Antigemination: the rule fails to apply exactly when it would create an OCP
violation, leaving the input unrepaired (contrast `collapse`). -/
theorem block_eq_self {xs : List α} (hc : ¬ IsClean (rule xs)) : block rule xs = xs := if_neg hc

/-- Blocking never worsens a clean tier. -/
theorem block_isClean {xs : List α} (hx : IsClean xs) : IsClean (block rule xs) := by
  unfold block; split <;> assumption

end

/-! ### The run-index map -/

section RunIndex
variable {α : Type*} [DecidableEq α]

/-- **Run index** of upper position `k` in `xs`: the index (0-based) of the
    OCP-run containing `k`, i.e. one less than the number of runs in the prefix
    `xs[0..k]`. Concretely `(OCP.collapse (xs.take (k+1))).length - 1`. -/
def runIdx (xs : List α) (k : ℕ) : ℕ := (collapse (xs.take (k + 1))).length - 1

/-- `runIdx` is monotone: later positions sit in later (or the same) runs. -/
theorem runIdx_monotone (xs : List α) : Monotone (runIdx xs) := by
  intro a b hab
  unfold runIdx
  have hsub : (collapse (xs.take (a + 1))).Sublist (xs.take (b + 1)) :=
    (collapse_sublist _).trans (List.take_sublist_take_left (by omega))
  have hlen := List.IsChain.length_le_length_destutter_ne hsub (collapse_clean _)
  simp only [collapse_eq_destutter] at hlen ⊢
  omega

/-- `runIdx` lands inside the collapsed tier: an in-bounds position maps to an
    in-bounds run index. The upper half of `collapseAR`'s in-bounds proof. -/
theorem runIdx_lt_collapse_length (xs : List α) {k : ℕ} (hk : k < xs.length) :
    runIdx xs k < (collapse xs).length := by
  unfold runIdx
  have hne : xs.take (k + 1) ≠ [] := by
    intro h
    have hlen : (xs.take (k + 1)).length = k + 1 := List.length_take_of_le (by omega)
    rw [h] at hlen; simp at hlen
  have hsub : (collapse (xs.take (k + 1))).Sublist xs :=
    (collapse_sublist _).trans (List.take_sublist _ _)
  have hlen := List.IsChain.length_le_length_destutter_ne hsub (collapse_clean _)
  simp only [collapse_eq_destutter] at hlen ⊢
  have hpos : 0 < ((xs.take (k + 1)).destutter (· ≠ ·)).length := by
    rw [List.length_pos_iff]
    intro h
    rw [← collapse_eq_destutter, collapse_eq_nil] at h
    exact hne h
  omega

/-- On a constant tier every position lies in the single run: `runIdx` is `0`. -/
@[simp] theorem runIdx_replicate (n : ℕ) (a : α) (k : ℕ) :
    runIdx (List.replicate n a) k = 0 := by
  unfold runIdx
  rw [List.take_replicate]
  cases hm : min (k + 1) n with
  | zero => simp
  | succ m => rw [collapse_replicate, List.length_singleton]

/-! ### Run-index and concatenation

The defining property of `concat` for the OCP quotient: `runIdx` commutes with the
collapse-collapse seam (`runIdx_append_collapse_left/right`). On the A-block the prefix
run-index is untouched (`runIdx_append_left`, plus `runIdx_clean` re-reading a clean tier
as the identity); on the B-block the seam merges exactly when `collapse xs` ends in the
element heading `ys` (`runIdx_append_right`, the AR shadow of
`List.destutter_append_length_clean`). -/

/-- The prefix run-index is unaffected by a right append. -/
theorem runIdx_append_left {xs ys : List α} {k : ℕ} (h : k < xs.length) :
    runIdx (xs ++ ys) k = runIdx xs k := by
  unfold runIdx; rw [List.take_append_of_le_length (by omega)]

/-- On a clean tier `runIdx` is the identity (no runs to merge). -/
theorem runIdx_clean {xs : List α} (hc : IsClean xs) {k : ℕ} (h : k < xs.length) :
    runIdx xs k = k := by
  unfold runIdx
  rw [collapse_idempotent_on_clean (hc.take (k + 1)), List.length_take_of_le (by omega)]
  omega

/-- The length of the collapse of a nonempty prefix is its top run-index plus one. -/
theorem collapse_take_succ_length {xs : List α} {m : ℕ} (hm : m < xs.length) :
    (collapse (xs.take (m + 1))).length = runIdx xs m + 1 := by
  unfold runIdx
  have hpos : 0 < (collapse (xs.take (m + 1))).length := by
    rw [List.length_pos_iff]
    refine fun h => ?_
    have hne : xs.take (m + 1) ≠ [] := by
      intro h'
      have : (xs.take (m + 1)).length = m + 1 := List.length_take_of_le (by omega)
      rw [h'] at this; simp at this
    exact hne (collapse_eq_nil.mp h)
  omega

/-- The collapse of a prefix has the same head as the whole tier. -/
theorem collapse_take_head? {xs : List α} {m : ℕ} :
    (collapse (xs.take (m + 1))).head? = xs.head? := by
  rw [collapse, List.destutter_head?]
  cases xs <;> simp

/-- **The B-part seam identity.** Reading a suffix position through the collapse of an
append: the run-index is the left collapse's length plus the suffix's own run-index, minus
one exactly when the seam merges (`List.destutter_append_length_clean`). -/
theorem runIdx_append_right {xs ys : List α} {a : ℕ} (ha : a < ys.length) :
    runIdx (xs ++ ys) (xs.length + a) =
      (collapse xs).length + runIdx ys a -
        (if (collapse xs).getLast? = ys.head? then 1 else 0) := by
  unfold runIdx
  rw [show xs.length + a + 1 = xs.length + (a + 1) by omega, List.take_length_add_append,
    collapse_append, collapse_eq_destutter,
    List.destutter_append_length_clean (collapse_clean _) (collapse_clean _),
    collapse_take_succ_length ha, collapse_take_head?]
  split_ifs with h
  · have : 0 < (collapse ys).length := Nat.zero_lt_of_lt (runIdx_lt_collapse_length ys ha)
    omega
  · omega

/-- A-block: a prefix index commutes with the collapse-collapse seam. -/
theorem runIdx_append_collapse_left {xs ys : List α} {k : ℕ} (h : k < xs.length) :
    runIdx (xs ++ ys) k = runIdx (collapse xs ++ collapse ys) (runIdx xs k) := by
  rw [runIdx_append_left h, runIdx_append_left (runIdx_lt_collapse_length xs h),
    runIdx_clean (collapse_clean _) (runIdx_lt_collapse_length xs h)]

/-- B-block: a suffix index commutes with the collapse-collapse seam. -/
theorem runIdx_append_collapse_right {xs ys : List α} {a : ℕ} (ha : a < ys.length) :
    runIdx (xs ++ ys) (xs.length + a) =
      runIdx (collapse xs ++ collapse ys) ((collapse xs).length + runIdx ys a) := by
  rw [runIdx_append_right ha, runIdx_append_right (runIdx_lt_collapse_length ys ha),
    collapse_idempotent, runIdx_clean (collapse_clean _) (runIdx_lt_collapse_length ys ha),
    collapse_eq_destutter ys, List.destutter_head?]

end RunIndex

end OCP
