import Mathlib.Order.Compare
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union

/-!
# Comparison categories

A **comparison category** is a `Finset Ordering` — which of `lt`/`eq`/`gt` a pair of elements of a
linear order may stand in. The atomic categories are the singletons (mathlib `Ordering` itself);
unions like `≤`/`≥` are larger sets. `holds s a b` says the comparison of `a` and `b` falls in `s`.

This is framework-agnostic order theory (the point analogue of `AllenRelation` for intervals): it is
generic over any `[LinearOrder α]` and bakes in **no** notion of time. Tense, evidential, and
modal-base-time semantics each supply the order (`Time`) and name the categories they use
(`Tense.past = before`, etc.).
-/

namespace Core.Order

variable {α : Type*} [LinearOrder α]

/-- A pair `a, b` stands in comparison category `s` iff `compare a b` is one of `s`'s orderings. -/
def holds (s : Finset Ordering) (a b : α) : Prop := compare a b ∈ s

instance (s : Finset Ordering) (a b : α) : Decidable (holds s a b) :=
  inferInstanceAs (Decidable (_ ∈ s))

/-! ### Named comparison categories -/

/-- `a < b`. -/
def before : Finset Ordering := {.lt}
/-- `a > b`. -/
def after : Finset Ordering := {.gt}
/-- `a = b` (points overlap). -/
def overlapping : Finset Ordering := {.eq}
/-- `a ≤ b`. -/
def notAfter : Finset Ordering := {.lt, .eq}
/-- `a ≥ b`. -/
def notBefore : Finset Ordering := {.gt, .eq}
/-- no constraint. -/
def unrestricted : Finset Ordering := {.lt, .eq, .gt}

/-! ### Reductions to the underlying order (so consumers' `<`-shaped proofs go through) -/

@[simp] theorem holds_before (a b : α) : holds before a b ↔ a < b := by
  simp [holds, before, compare_lt_iff_lt]
@[simp] theorem holds_after (a b : α) : holds after a b ↔ b < a := by
  simp [holds, after, compare_gt_iff_gt]
@[simp] theorem holds_overlapping (a b : α) : holds overlapping a b ↔ a = b := by
  simp [holds, overlapping]
@[simp] theorem holds_notAfter (a b : α) : holds notAfter a b ↔ a ≤ b := by
  simp [holds, notAfter, compare_lt_iff_lt, le_iff_lt_or_eq]
@[simp] theorem holds_notBefore (a b : α) : holds notBefore a b ↔ b ≤ a := by
  rw [← not_lt, ← compare_lt_iff_lt]
  simp only [holds, notBefore, Finset.mem_insert, Finset.mem_singleton]
  cases compare a b <;> simp
@[simp] theorem holds_unrestricted (a b : α) : holds unrestricted a b ↔ True := by
  simp only [holds, unrestricted, iff_true]
  rcases lt_trichotomy a b with h | h | h
  · simp [compare_lt_iff_lt.mpr h]
  · simp [compare_eq_iff_eq.mpr h]
  · simp [compare_gt_iff_gt.mpr h]

/-! ### Relation-algebra structure: converse and composition

Beyond `Finset`'s Boolean-lattice structure (`⊆`, `∩`, `∪`), `Finset Ordering`
carries a **converse** (swap `lt`/`gt`) and a **composition** with unit
`overlapping` — the **point algebra** (the point analogue of `AllenRelation`'s
interval relations). `comp r s` over-approximates which category `a` stands in to
`c` given `holds r a b` and `holds s b c`: the transitivity / path-consistency
operation. Generic over any `[LinearOrder α]`, so one algebra structures time,
degree, or any other linear domain alike. -/

/-- Swapping the arguments of `compare` swaps the ordering. -/
theorem swap_compare (a b : α) : (compare a b).swap = compare b a := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_gt_iff_gt.mpr h]; rfl
  · rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr h.symm]; rfl
  · rw [compare_gt_iff_gt.mpr h, compare_lt_iff_lt.mpr h]; rfl

/-- Converse of a comparison category: swap `lt` and `gt`. -/
def converse (s : Finset Ordering) : Finset Ordering := s.image Ordering.swap

@[simp] theorem holds_converse (s : Finset Ordering) (a b : α) :
    holds (converse s) a b ↔ holds s b a := by
  simp only [holds, converse, Finset.mem_image]
  constructor
  · rintro ⟨o, ho, hbo⟩
    rw [← swap_compare b a] at hbo
    exact (Ordering.swap_inj.mp hbo) ▸ ho
  · intro hba
    exact ⟨compare b a, hba, swap_compare b a⟩

/-- Base composition table for the point algebra: which categories `a` may stand
    in to `c` given `compare a b` and `compare b c`. -/
def compBase : Ordering → Ordering → Finset Ordering
  | .lt, .lt => before
  | .lt, .eq => before
  | .eq, o   => {o}
  | .gt, .eq => after
  | .gt, .gt => after
  | _,   _   => unrestricted

/-- Composition of comparison categories (transitivity / path-consistency):
    the relations `a` may stand in to `c` given `r` between `a, b` and `s`
    between `b, c`. -/
def comp (r s : Finset Ordering) : Finset Ordering :=
  r.biUnion fun o₁ => s.biUnion fun o₂ => compBase o₁ o₂

/-- Base soundness: the actual comparison of `a` and `c` lies in the composed
    category determined by `compare a b` and `compare b c`. -/
theorem compare_mem_compBase (a b c : α) :
    compare a c ∈ compBase (compare a b) (compare b c) := by
  rcases lt_trichotomy a b with hab | hab | hab <;>
    rcases lt_trichotomy b c with hbc | hbc | hbc
  · rw [compare_lt_iff_lt.mpr hab, compare_lt_iff_lt.mpr hbc,
        compare_lt_iff_lt.mpr (hab.trans hbc)]; decide
  · rw [compare_lt_iff_lt.mpr hab, compare_eq_iff_eq.mpr hbc,
        compare_lt_iff_lt.mpr (lt_of_lt_of_eq hab hbc)]; decide
  · rw [compare_lt_iff_lt.mpr hab, compare_gt_iff_gt.mpr hbc]
    exact (holds_unrestricted a c).2 trivial
  · rw [compare_eq_iff_eq.mpr hab, compare_lt_iff_lt.mpr hbc,
        compare_lt_iff_lt.mpr (lt_of_eq_of_lt hab hbc)]; decide
  · rw [compare_eq_iff_eq.mpr hab, compare_eq_iff_eq.mpr hbc,
        compare_eq_iff_eq.mpr (hab.trans hbc)]; decide
  · rw [compare_eq_iff_eq.mpr hab, compare_gt_iff_gt.mpr hbc,
        compare_gt_iff_gt.mpr (lt_of_lt_of_eq hbc hab.symm)]; decide
  · rw [compare_gt_iff_gt.mpr hab, compare_lt_iff_lt.mpr hbc]
    exact (holds_unrestricted a c).2 trivial
  · rw [compare_gt_iff_gt.mpr hab, compare_eq_iff_eq.mpr hbc,
        compare_gt_iff_gt.mpr (lt_of_eq_of_lt hbc.symm hab)]; decide
  · rw [compare_gt_iff_gt.mpr hab, compare_gt_iff_gt.mpr hbc,
        compare_gt_iff_gt.mpr (hbc.trans hab)]; decide

/-- Composition is **sound**: it over-approximates the transitive relation. If
    `a` stands in `r` to `b` and `b` in `s` to `c`, then `a` stands in `comp r s`
    to `c`. -/
theorem holds_comp {a b c : α} {r s : Finset Ordering}
    (hab : holds r a b) (hbc : holds s b c) : holds (comp r s) a c := by
  simp only [holds, comp, Finset.mem_biUnion]
  exact ⟨compare a b, hab, compare b c, hbc, compare_mem_compBase a b c⟩

/-- A comparison category is **convex** unless it is the non-convex `{lt, gt}`
    ("≠", skipping `eq`) — the one relation that takes the point algebra out of
    its path-consistency-complete fragment. -/
def IsConvex (s : Finset Ordering) : Prop := .lt ∈ s → .gt ∈ s → .eq ∈ s

instance (s : Finset Ordering) : Decidable (IsConvex s) := by
  unfold IsConvex; infer_instance

end Core.Order
