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
downstream proofs bottom out in mathlib's order API. Cells compose: `comp R S` collects the
orderings of `a` to `c` compatible with `a` to `b` in `R` and `b` to `c` in `S`, so a relation
between non-adjacent times is derived by `compare_mem_comp`.
-/

/-- The orderings of `a` to `c` compatible with an ordering of `a` to `b` and one of `b` to `c`
in a linear order. -/
def Ordering.comp : Ordering → Ordering → Finset Ordering
  | .lt, .lt => {.lt}
  | .lt, .eq => {.lt}
  | .lt, .gt => ⊤
  | .eq, o => {o}
  | .gt, .lt => ⊤
  | .gt, .eq => {.gt}
  | .gt, .gt => {.gt}

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

/-- Composition of cells: the orderings of `a` to `c` compatible with `a` to `b` in `R` and
`b` to `c` in `S`. -/
def comp (R S : Finset Ordering) : Finset Ordering :=
  Finset.univ.filter λ o => ∃ r ∈ R, ∃ s ∈ S, o ∈ r.comp s

theorem compare_mem_comp_compare (a b c : T) :
    compare a c ∈ (compare a b).comp (compare b c) := by
  rcases h₁ : compare a b with _ | _ | _ <;> rcases h₂ : compare b c with _ | _ | _ <;>
    simp only [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at h₁ h₂ <;>
    simp [Ordering.comp, compare_lt_iff_lt, compare_gt_iff_gt, h₁, h₂] <;>
    first
      | exact h₁.trans h₂ | exact h₂.trans h₁ | exact h₁.trans_eq h₂ | exact h₁.trans_lt h₂
      | exact h₂.symm.trans_lt h₁

theorem compare_mem_comp {R S : Finset Ordering} {a b c : T} (h₁ : compare a b ∈ R)
    (h₂ : compare b c ∈ S) : compare a c ∈ comp R S :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, _, h₁, _, h₂, compare_mem_comp_compare a b c⟩

end Tense
