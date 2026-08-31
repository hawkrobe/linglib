import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Order.Defs.LinearOrder

/-!
# Grammatical tense as a comparison cell

A grammatical tense constrains which of `lt`/`eq`/`gt` a reference time may stand in to a
perspective time ([kiparsky-2002]: tense locates R relative to the perspective time P, not speech
time S). There is no bespoke tense type: a tense is a `Finset Ordering` — an element of the Boolean
algebra `𝒫 {lt, eq, gt}` — and the constraint it imposes on times `r`, `p` is membership
`compare r p ∈ cell`. Tense, evidentials, and modal-base time thereby share mathlib's `Ordering`
spine, and derived categories are `Finset` complements and unions (*nonfuture* is `futureᶜ`,
*then*'s non-present is `presentᶜ`, an unconstrained cell is `⊤`).

* `past`    = `{.lt}` (ref < perspective)
* `present` = `{.eq}` (ref = perspective)
* `future`  = `{.gt}` (ref > perspective)
* `nonpast` = `{.eq, .gt}` (ref ≥ perspective — the present-or-future union, [klecha-2016])

The `compare_mem_*` simp lemmas reduce each constraint to `<`/`=`/`≤` on the underlying order, so
downstream proofs bottom out in mathlib's order API.
-/

namespace Tense

/-- **Past**: reference time before perspective time. -/
def past : Finset Ordering := {.lt}

/-- **Present**: reference time overlaps (equals) perspective time. -/
def present : Finset Ordering := {.eq}

/-- **Future**: reference time after perspective time. -/
def future : Finset Ordering := {.gt}

/-- **Nonpast** ([klecha-2016]): reference time at or after perspective time, *not* a fourth
    atomic tense. Lets embedded tense under circumstantial modals have future-oriented readings
    (⟦NPST⟧ requires ref ≥ perspective). -/
def nonpast : Finset Ordering := {.eq, .gt}

/-- [klecha-2016]'s point made literal: nonpast **is** the join of present and future in
    `𝒫 {lt, eq, gt}`, not a fourth atomic tense. -/
theorem nonpast_eq_present_sup_future : nonpast = present ⊔ future := by decide

/-- Nonpast is equally the complement of past — the trichotomy of the underlying linear order. -/
theorem nonpast_eq_compl_past : nonpast = pastᶜ := by decide

variable {T : Type*} [LinearOrder T]

@[simp] theorem compare_mem_past (r p : T) : compare r p ∈ past ↔ r < p := by
  simp [past, compare_lt_iff_lt]

@[simp] theorem compare_mem_present (r p : T) : compare r p ∈ present ↔ r = p := by
  simp [present]

@[simp] theorem compare_mem_future (r p : T) : compare r p ∈ future ↔ p < r := by
  simp [future, compare_gt_iff_gt]

@[simp] theorem compare_mem_nonpast (r p : T) : compare r p ∈ nonpast ↔ p ≤ r := by
  rw [nonpast_eq_compl_past, Finset.mem_compl, compare_mem_past, not_lt]

end Tense
