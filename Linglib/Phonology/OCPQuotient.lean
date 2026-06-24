/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.OCP

/-!
# The OCP quotient monoid

The algebraic core of the autosegmental free concatenation `⊙` (string `++` on the melody
tier, the categorical coproduct) versus the OCP-gluing concatenation `∘`: they are a free
monoid and its quotient. `∘` is `⊙` modulo the OCP, and `OCP.collapse`
(`List.destutter (· ≠ ·)`, the OCP-merger normal form, [goldsmith-1976], [mccarthy-1986]) is
the quotient homomorphism. Concretely `(OCP-clean lists, gconcat, [])` is the quotient monoid
`(List α, ++) / OCP`: `gconcat x y := collapse (x ++ y)` is associative with `[]` a unit on
clean lists, and `collapse_append` is the congruence `collapse (x ++ y) =
collapse (collapse x ++ collapse y)` making `collapse` a `++`→`gconcat` hom.

The AR-level lift — pushing links forward along the run-collapse map so that this melody-tier
quotient becomes an autosegmental-graph quotient — is future work.

## Main results

* `OCP.collapse_append` — the crux congruence: `collapse` is a `++`→quotient hom.
* `OCP.gconcat` / `OCP.gconcat_assoc` / `OCP.nil_gconcat` / `OCP.gconcat_nil` — the gluing
  concatenation and the monoid laws on OCP-clean lists.
* `OCP.collapse_gconcat` — `collapse` carries `(List α, ++)` onto `(OCP-clean, gconcat)`.
-/

namespace OCP

variable {α : Type*} [DecidableEq α]

/-! ### Destutter' scaffolding -/

/-- `destutter' (· ≠ ·) a l` always begins with its running element `a`. -/
private theorem dest'_head_cons (a : α) (l : List α) :
    ∃ t, l.destutter' (· ≠ ·) a = a :: t := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    by_cases h : a ≠ b
    · exact ⟨l.destutter' (· ≠ ·) b, by rw [List.destutter'_cons_pos (h := h)]⟩
    · rw [List.destutter'_cons_neg (h := h)]; exact ih a

/-- Re-running `destutter'` against its own running element drops the duplicate head. -/
private theorem dest'_cons_self (a : α) (l : List α) :
    (a :: l).destutter' (· ≠ ·) a = l.destutter' (· ≠ ·) a := by
  rw [List.destutter'_cons_neg (h := by simp)]

/-- Collapsing on the left of an append is absorbed by the outer collapse (running-element
form): `destutter' a` is insensitive to a leading `destutter' a` on its left operand. -/
private theorem dest'_append_left (a : α) (l y : List α) :
    (l.destutter' (· ≠ ·) a ++ y).destutter' (· ≠ ·) a = (l ++ y).destutter' (· ≠ ·) a := by
  induction l generalizing a with
  | nil => simp [List.destutter'_cons_neg]
  | cons b l ih =>
    by_cases h : a ≠ b
    · rw [List.destutter'_cons_pos (h := h), List.cons_append, dest'_cons_self,
        List.cons_append, List.destutter'_cons_pos (h := h)]
      obtain ⟨t, ht⟩ := dest'_head_cons b l
      rw [ht, List.cons_append, List.destutter'_cons_pos (h := h)]
      congr 1
      have key := ih b
      rwa [ht, List.cons_append, dest'_cons_self] at key
    · rw [List.destutter'_cons_neg (h := h), List.cons_append,
        List.destutter'_cons_neg (h := h)]
      exact ih a

/-- If `destutter' c m = c :: t`, the tail `t` is already a `(· ≠ ·)`-chain. -/
private theorem dest'_tail_fixed {c : α} {m t : List α}
    (ht : m.destutter' (· ≠ ·) c = c :: t) : t.destutter' (· ≠ ·) c = c :: t :=
  List.destutter'_of_isChain_cons t (· ≠ ·) (ht ▸ List.isChain_destutter' (· ≠ ·) m c)

/-- `destutter' a` is insensitive to a leading `collapse` of its argument. -/
private theorem dest'_collapse (a : α) (y : List α) :
    (collapse y).destutter' (· ≠ ·) a = y.destutter' (· ≠ ·) a := by
  cases y with
  | nil => simp [collapse]
  | cons c m =>
    rw [collapse, List.destutter_cons']
    obtain ⟨t, ht⟩ := dest'_head_cons c m
    by_cases h : a ≠ c
    · rw [ht, List.destutter'_cons_pos (h := h), List.destutter'_cons_pos (h := h),
        dest'_tail_fixed ht, ht]
    · rw [ht, List.destutter'_cons_neg (h := h), List.destutter'_cons_neg (h := h)]
      obtain rfl : a = c := not_not.mp h
      rw [dest'_tail_fixed ht, ht]

/-- Collapsing on the right of an append is absorbed by the outer collapse (running-element
form). -/
private theorem dest'_append_right (a : α) (l y : List α) :
    (l ++ collapse y).destutter' (· ≠ ·) a = (l ++ y).destutter' (· ≠ ·) a := by
  induction l generalizing a with
  | nil => simpa [collapse] using dest'_collapse a y
  | cons b l ih =>
    by_cases h : a ≠ b
    · rw [List.cons_append, List.cons_append, List.destutter'_cons_pos (h := h),
        List.destutter'_cons_pos (h := h), ih b]
    · rw [List.cons_append, List.cons_append, List.destutter'_cons_neg (h := h),
        List.destutter'_cons_neg (h := h), ih a]

/-! ### The congruence -/

/-- Collapsing the left operand before appending does not change the result. -/
theorem collapse_append_left (x y : List α) :
    collapse (collapse x ++ y) = collapse (x ++ y) := by
  cases x with
  | nil => simp [collapse]
  | cons a l =>
    simp only [collapse, List.destutter_cons']
    obtain ⟨t, ht⟩ := dest'_head_cons a l
    have hL : (l.destutter' (· ≠ ·) a ++ y).destutter (· ≠ ·) = (t ++ y).destutter' (· ≠ ·) a := by
      rw [ht, List.cons_append, List.destutter_cons']
    rw [hL]
    have key := dest'_append_left a l y
    rwa [ht, List.cons_append, dest'_cons_self] at key

/-- Collapsing the right operand before appending does not change the result. -/
theorem collapse_append_right (x y : List α) :
    collapse (x ++ collapse y) = collapse (x ++ y) := by
  cases x with
  | nil => simpa [collapse] using collapse_idempotent y
  | cons a l =>
    show ((a :: l) ++ collapse y).destutter (· ≠ ·) = ((a :: l) ++ y).destutter (· ≠ ·)
    rw [List.cons_append, List.cons_append, List.destutter_cons', List.destutter_cons',
      dest'_append_right]

/-- **The OCP congruence.** `collapse` is a `++`→quotient homomorphism: collapsing each operand
first is harmless. Thus `collapse` descends to the OCP quotient of `(List α, ++)`. -/
theorem collapse_append (x y : List α) :
    collapse (x ++ y) = collapse (collapse x ++ collapse y) := by
  rw [collapse_append_left, collapse_append_right]

/-! ### The gluing concatenation -/

/-- **OCP-gluing concatenation** `∘`: concatenate, then merge the new boundary geminate. The
multiplication of the OCP quotient monoid. -/
def gconcat (x y : List α) : List α := collapse (x ++ y)

/-- `gconcat` is associative — the quotient inherits `++`'s associativity through `collapse`. -/
theorem gconcat_assoc (x y z : List α) :
    gconcat (gconcat x y) z = gconcat x (gconcat y z) := by
  unfold gconcat
  rw [collapse_append_left, collapse_append_right, List.append_assoc]

/-- `[]` is a left unit up to `collapse`; on OCP-clean lists it is a genuine left unit. -/
theorem nil_gconcat (x : List α) : gconcat [] x = collapse x := by simp [gconcat]

/-- `[]` is a right unit up to `collapse`; on OCP-clean lists it is a genuine right unit. -/
theorem gconcat_nil (x : List α) : gconcat x [] = collapse x := by simp [gconcat]

/-- `gconcat` lands in the OCP-clean set: the quotient is closed under its multiplication. -/
theorem gconcat_clean (x y : List α) : IsClean (gconcat x y) := collapse_clean _

/-! ### The quotient homomorphism -/

/-- `collapse` carries `(List α, ++)` onto `(OCP-clean, gconcat)`: the quotient-hom equation. -/
theorem collapse_gconcat (x y : List α) :
    collapse (x ++ y) = gconcat (collapse x) (collapse y) := by
  rw [gconcat, ← collapse_append]

/-- `gconcat` outputs are OCP-clean fixed points of `collapse`. -/
theorem collapse_collapse_gconcat (x y : List α) : collapse (gconcat x y) = gconcat x y := by
  rw [gconcat, collapse_idempotent]

end OCP
