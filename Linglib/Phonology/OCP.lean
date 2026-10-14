/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Monotone.Basic
public import Linglib.Core.Data.List.Destutter

/-!
# The Obligatory Contour Principle

The Obligatory Contour Principle (OCP) bans two identical adjacent autosegments on one tier.
Here it is categorical and bans strict identity, either on the tier itself (`IsClean`, after
Leben and McCarthy) or on a projection of it (`IsCleanOn`, after Chandlee and Jardine). Fusion,
`collapse`, repairs a violation by merging each run of identical elements into one; it is
`List.destutter (· ≠ ·)`, a retraction onto the clean tiers. Blocking, `block`, is McCarthy's
antigemination: a rule that would create a violation does not apply. The run index `runIdx`
tracks where each position lands under fusion. `Phonology/Subregular/OCP.lean` shows that the
constraint is tier-based strictly local and that fusion is input strictly local.

The gradient OCP of Frisch, Pierrehumbert and Broe, which scales with the similarity of the two
consonants, is a different object and lives in that paper's study.

## Main definitions

* `OCP.IsClean`, `OCP.IsCleanOn`: no two identical adjacent elements, on the tier or on a
  projection of it.
* `OCP.collapse`: the fusion repair.
* `OCP.block`: the blocking repair.
* `OCP.runIdx`: the index of the run containing a position.

## Main statements

* `OCP.collapse_eq_self_iff`: `collapse` fixes exactly the clean tiers.
* `OCP.collapse_append`: `collapse` is a congruence for `++`.
* `OCP.runIdx_append_collapse_left`, `OCP.runIdx_append_collapse_right`: run indices commute
  with collapsing the two halves of a concatenation.

## References

* [leben-1973]
* [goldsmith-1976]
* [mccarthy-1986]
* [mccarthy-prince-1995]
* [frisch-pierrehumbert-broe-2004]
* [heinz-rawal-tanner-2011]
* [chandlee-heinz-2018]
* [chandlee-jardine-2019]
-/

@[expose] public section

namespace OCP

variable {α β : Type*}

/-! ### The constraint -/

/-- A tier is **OCP-clean** when no two adjacent elements are identical. This is weaker than
`List.Nodup`, since `[1, 2, 1]` is clean. It is a reducible alias of `List.IsChain (· ≠ ·)`, so
that API applies. -/
abbrev IsClean (xs : List α) : Prop :=
  List.IsChain (· ≠ ·) xs

@[simp] theorem isClean_nil : IsClean ([] : List α) := List.isChain_nil

@[simp] theorem isClean_singleton (x : α) : IsClean [x] := List.isChain_singleton x

@[simp] theorem isClean_cons_cons_iff (x y : α) (rs : List α) :
    IsClean (x :: y :: rs) ↔ x ≠ y ∧ IsClean (y :: rs) := by
  simp only [IsClean, List.isChain_cons_cons]

/-- The OCP on the tier projected from `xs` by keeping the `p`-elements and reading them
through `proj`. Flat `IsClean` is the case `p = ⊤`, `proj = id`. -/
def IsCleanOn (p : α → Prop) [DecidablePred p] (proj : α → β) (xs : List α) : Prop :=
  IsClean ((xs.filter (fun a ↦ decide (p a))).map proj)

instance decidableIsClean [DecidableEq α] : DecidablePred (IsClean (α := α)) :=
  fun xs ↦ inferInstanceAs (Decidable (List.IsChain (· ≠ ·) xs))

instance decidableIsCleanOn [DecidableEq β] (p : α → Prop)
    [DecidablePred p] (proj : α → β) : DecidablePred (IsCleanOn p proj) :=
  fun _ ↦ inferInstanceAs (Decidable (IsClean _))

section
variable [DecidableEq α]

/-! ### The fusion repair -/

/-- The **fusion repair** merges each maximal run of identical adjacent elements into one. -/
def collapse (xs : List α) : List α := xs.destutter (· ≠ ·)

theorem collapse_eq_destutter (xs : List α) : collapse xs = xs.destutter (· ≠ ·) := rfl

@[simp] theorem collapse_nil : collapse ([] : List α) = [] := by simp [collapse]

@[simp] theorem collapse_singleton (x : α) : collapse [x] = [x] := by simp [collapse]

/-- `collapse` fuses a constant run into its single autosegment. -/
@[simp] theorem collapse_replicate (n : ℕ) (a : α) :
    collapse (List.replicate (n + 1) a) = [a] :=
  List.destutter_replicate (fun h ↦ h rfl) n

/-- `collapse` lands in the OCP-clean set. -/
theorem collapse_clean (xs : List α) : IsClean (collapse xs) :=
  List.isChain_destutter _ xs

/-- `collapse` fixes OCP-clean lists. -/
theorem collapse_idempotent_on_clean {xs : List α} (h : IsClean xs) : collapse xs = xs :=
  List.destutter_of_isChain _ xs h

/-- `collapse` fixes exactly the OCP-clean tiers, so with `collapse_clean` it is a retraction
onto them. -/
@[simp] theorem collapse_eq_self_iff (xs : List α) : collapse xs = xs ↔ IsClean xs :=
  List.destutter_eq_self_iff _ xs

/-- The fusion repair is a retraction onto the OCP-clean set. -/
theorem collapse_idempotent (xs : List α) : collapse (collapse xs) = collapse xs :=
  List.destutter_idem _ _

/-! ### Normal-form lemmas -/

@[simp] theorem collapse_eq_nil {xs : List α} : collapse xs = [] ↔ xs = [] :=
  List.destutter_eq_nil _

/-- The output of the fusion repair is a sublist of its input. -/
theorem collapse_sublist (xs : List α) : (collapse xs).Sublist xs :=
  List.destutter_sublist _ xs

theorem collapse_length_le (xs : List α) : (collapse xs).length ≤ xs.length :=
  (collapse_sublist xs).length_le

theorem mem_collapse {a : α} {xs : List α} (ha : a ∈ collapse xs) : a ∈ xs :=
  (collapse_sublist xs).mem ha

/-! ### The OCP congruence

Collapsing either operand before appending changes nothing, so `collapse` is a congruence
for `++`. -/

/-- Collapsing the left operand before appending does not change the result. -/
theorem collapse_append_left (x y : List α) :
    collapse (collapse x ++ y) = collapse (x ++ y) :=
  List.destutter_append_left x y

/-- Collapsing the right operand before appending does not change the result. -/
theorem collapse_append_right (x y : List α) :
    collapse (x ++ collapse y) = collapse (x ++ y) :=
  List.destutter_append_right x y

/-- Collapsing each operand before appending changes nothing. -/
theorem collapse_append (x y : List α) :
    collapse (x ++ y) = collapse (collapse x ++ collapse y) :=
  (List.destutter_append_destutter x y).symm

/-! ### The blocking repair

A rule that would create an OCP violation fails to apply, leaving its input unrepaired. -/

variable (rule : List α → List α)

/-- **Blocking** applies `rule` only when its output is OCP-clean and otherwise leaves the input
untouched. Unlike `collapse`, it prevents a process rather than repairing its output. -/
def block (xs : List α) : List α :=
  if IsClean (rule xs) then rule xs else xs

theorem block_eq_rule {xs : List α} (hc : IsClean (rule xs)) : block rule xs = rule xs := ite_eq_left hc

/-- Under antigemination a rule that would create an OCP violation does not apply, and the
input is left unrepaired. -/
theorem block_eq_self {xs : List α} (hc : ¬ IsClean (rule xs)) : block rule xs = xs := ite_eq_right hc

/-- Blocking never worsens a clean tier. -/
theorem block_isClean {xs : List α} (hx : IsClean xs) : IsClean (block rule xs) := by
  unfold block; split <;> assumption

end

/-! ### The run-index map -/

section RunIndex
variable {α : Type*} [DecidableEq α]

/-- The **run index** of position `k` in `xs` is the 0-based index of the run of identical
elements containing it, one less than the number of runs in `xs.take (k + 1)`. -/
def runIdx (xs : List α) (k : ℕ) : ℕ := (collapse (xs.take (k + 1))).length - 1

/-- Later positions sit in the same or later runs. -/
theorem runIdx_monotone (xs : List α) : Monotone (runIdx xs) := by
  intro a b hab
  unfold runIdx
  have hsub : (collapse (xs.take (a + 1))).Sublist (xs.take (b + 1)) :=
    (collapse_sublist _).trans (List.take_sublist_take_left (by omega))
  have hlen := List.IsChain.length_le_length_destutter_ne hsub (collapse_clean _)
  simp only [collapse_eq_destutter] at hlen ⊢
  omega

/-- An in-bounds position has an in-bounds run index in the collapsed tier. -/
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

/-- On a constant tier every position lies in the single run. -/
@[simp] theorem runIdx_replicate (n : ℕ) (a : α) (k : ℕ) :
    runIdx (List.replicate n a) k = 0 := by
  unfold runIdx
  rw [List.take_replicate]
  cases hm : min (k + 1) n with
  | zero => simp
  | succ m => rw [collapse_replicate, List.length_singleton]

/-! ### Run-index and concatenation

`runIdx` commutes with the collapse-collapse seam (`runIdx_append_collapse_left/right`). On
the left block the prefix run index is untouched (`runIdx_append_left`, with `runIdx_clean`
reading a clean tier as the identity); on the right block the seam merges exactly when
`collapse xs` ends in the element heading `ys` (`runIdx_append_right`, from
`List.IsChain.length_destutter_ne_append`). -/

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
    refine fun h ↦ ?_
    have hne : xs.take (m + 1) ≠ [] := by
      intro h'
      have : (xs.take (m + 1)).length = m + 1 := List.length_take_of_le (by omega)
      rw [h'] at this; simp at this
    exact hne (collapse_eq_nil.mp h)
  omega

/-- The collapse of a prefix has the same head as the whole tier. -/
theorem collapse_take_head? {xs : List α} {m : ℕ} :
    (collapse (xs.take (m + 1))).head? = xs.head? := by
  rw [collapse, List.head?_destutter]
  cases xs <;> simp

/-- The run index of a suffix position is the length of the collapsed prefix plus its run
index in the suffix, minus one exactly when the seam merges. -/
theorem runIdx_append_right {xs ys : List α} {a : ℕ} (ha : a < ys.length) :
    runIdx (xs ++ ys) (xs.length + a) =
      (collapse xs).length + runIdx ys a -
        (if (collapse xs).getLast? = ys.head? then 1 else 0) := by
  unfold runIdx
  rw [show xs.length + a + 1 = xs.length + (a + 1) by omega, List.take_length_add_append,
    collapse_append, collapse_eq_destutter,
    (collapse_clean _).length_destutter_ne_append (collapse_clean _),
    collapse_take_succ_length ha, collapse_take_head?]
  split_ifs with h
  · have : 0 < (collapse ys).length := Nat.zero_lt_of_lt (runIdx_lt_collapse_length ys ha)
    omega
  · omega

/-- The run index of a prefix position commutes with collapsing both halves. -/
theorem runIdx_append_collapse_left {xs ys : List α} {k : ℕ} (h : k < xs.length) :
    runIdx (xs ++ ys) k = runIdx (collapse xs ++ collapse ys) (runIdx xs k) := by
  rw [runIdx_append_left h, runIdx_append_left (runIdx_lt_collapse_length xs h),
    runIdx_clean (collapse_clean _) (runIdx_lt_collapse_length xs h)]

/-- The run index of a suffix position commutes with collapsing both halves. -/
theorem runIdx_append_collapse_right {xs ys : List α} {a : ℕ} (ha : a < ys.length) :
    runIdx (xs ++ ys) (xs.length + a) =
      runIdx (collapse xs ++ collapse ys) ((collapse xs).length + runIdx ys a) := by
  rw [runIdx_append_right ha, runIdx_append_right (runIdx_lt_collapse_length ys ha),
    collapse_idempotent, runIdx_clean (collapse_clean _) (runIdx_lt_collapse_length ys ha),
    collapse_eq_destutter ys, List.head?_destutter]

end RunIndex

end OCP
