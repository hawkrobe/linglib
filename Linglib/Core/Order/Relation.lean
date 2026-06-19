import Mathlib.Order.Compare
import Mathlib.Order.Hom.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Powerset

/-!
# Comparison categories

A **comparison category** is a `Finset Ordering` — which of `lt`/`eq`/`gt` a pair of elements of a
linear order may stand in. The atomic categories are the singletons (mathlib `Ordering` itself);
unions like `≤`/`≥` are larger sets. `holds s a b` says the comparison of `a` and `b` falls in `s`.

This is framework-agnostic order theory (the point analogue of `AllenRelation` for intervals): it is
generic over any `[LinearOrder α]` and bakes in **no** notion of time. Tense, evidential, and
modal-base-time semantics each supply the order (`Time`) and name the categories they use
(`Tense.past = before`, etc.).

`Finset Ordering` is the eight-element Boolean algebra `𝒫 {lt, eq, gt}` — the Aristotelian diagram of
the trichotomy, with the three singletons as atoms and `≤`/`≥`/`≠` as their joins. For each pair
`a, b`, the map `s ↦ holds s a b` is its **Stone-dual point-evaluation** at `compare a b`: a
`BoundedLatticeHom` into `Prop` (`holdsHom`, `holds_sup`/`holds_inf`/`holds_compl`/`holds_top`/
`holds_bot`). Together with `converse` (↦ `SetRel.inv`) and `comp` (↦ `SetRel.comp`) below, this
exhibits `holds` as a homomorphism from the finite point algebra into the relation algebra
`SetRel α α`, and makes the named categories' `holds_*` reductions corollaries of one morphism.
-/

namespace Core.Order

variable {α : Type*} [LinearOrder α]

/-- A pair `a, b` stands in comparison category `s` iff `compare a b` is one of `s`'s orderings. -/
def holds (s : Finset Ordering) (a b : α) : Prop := compare a b ∈ s

instance (s : Finset Ordering) (a b : α) : Decidable (holds s a b) :=
  inferInstanceAs (Decidable (_ ∈ s))

/-! ### `holds` as a Boolean-algebra homomorphism

For each pair `a, b`, `s ↦ holds s a b` preserves the Boolean structure of `Finset Ordering`: it is
point-evaluation of the membership relation at `compare a b`. These are the `∪`/`∩`/`ᶜ`/`⊤`/`⊥` half
of the relation-algebra homomorphism (the `converse`/`comp` half is below). -/

@[simp] theorem holds_sup (s t : Finset Ordering) (a b : α) :
    holds (s ⊔ t) a b ↔ holds s a b ∨ holds t a b := by
  simp only [holds, Finset.sup_eq_union, Finset.mem_union]

@[simp] theorem holds_inf (s t : Finset Ordering) (a b : α) :
    holds (s ⊓ t) a b ↔ holds s a b ∧ holds t a b := by
  simp only [holds, Finset.inf_eq_inter, Finset.mem_inter]

@[simp] theorem holds_compl (s : Finset Ordering) (a b : α) :
    holds sᶜ a b ↔ ¬ holds s a b := by
  simp only [holds, Finset.mem_compl]

@[simp] theorem holds_top (a b : α) : holds (⊤ : Finset Ordering) a b ↔ True := by
  simp only [holds, Finset.top_eq_univ, Finset.mem_univ]

@[simp] theorem holds_bot (a b : α) : holds (⊥ : Finset Ordering) a b ↔ False := by
  simp only [holds, Finset.bot_eq_empty, Finset.notMem_empty]

/-- `holds`, bundled. For every `[LinearOrder α]`, the map `s ↦ fun a b => holds s a b` is a
    `BoundedLatticeHom` from the eight-element Boolean algebra `Finset Ordering` (= `𝒫 {lt, eq, gt}`)
    into the relation algebra `α → α → Prop` — the Stone-dual evaluation of the comparison-category
    algebra. With `converse` (`holds_converse`) and `comp` (`holds_comp`) it is the point algebra's
    image in the concrete relation algebra. -/
def holdsHom : BoundedLatticeHom (Finset Ordering) (α → α → Prop) where
  toFun s := fun a b => holds s a b
  map_sup' s t := by ext a b; simp only [Pi.sup_apply, sup_Prop_eq]; exact holds_sup s t a b
  map_inf' s t := by ext a b; simp only [Pi.inf_apply, inf_Prop_eq]; exact holds_inf s t a b
  map_top' := by ext a b; simp only [Pi.top_apply]; exact holds_top a b
  map_bot' := by ext a b; simp only [Pi.bot_apply]; exact holds_bot a b

@[simp] theorem holdsHom_apply (s : Finset Ordering) (a b : α) :
    holdsHom s a b = holds s a b := rfl

/-! ### Named comparison categories

The three atoms are the singletons `before`/`overlapping`/`after`; every other category is a Boolean
combination of them, so the composite `holds_*` reductions below are corollaries of `holds_sup`, not
separate `compare`-inspections. -/

/-- `a < b` (atom `lt`). -/
def before : Finset Ordering := {.lt}
/-- `a > b` (atom `gt`). -/
def after : Finset Ordering := {.gt}
/-- `a = b`, points overlap (atom `eq`). -/
def overlapping : Finset Ordering := {.eq}
/-- `a ≤ b` — the join `before ⊔ overlapping`. -/
def notAfter : Finset Ordering := before ⊔ overlapping
/-- `a ≥ b` — the join `after ⊔ overlapping`. -/
def notBefore : Finset Ordering := after ⊔ overlapping
/-- `a ≠ b` — the join `before ⊔ after` (the one non-convex category). -/
def distinct : Finset Ordering := before ⊔ after
/-- no constraint (`= ⊤`, see `unrestricted_eq_top`); kept as the explicit literal so the
    `decide`-checked relation-algebra laws below reduce without unfolding `Finset.univ`. -/
def unrestricted : Finset Ordering := {.lt, .eq, .gt}

/-! ### Reductions to the underlying order (so consumers' `<`-shaped proofs go through)

`holds_before`/`holds_after`/`holds_overlapping` discharge the three atoms; each composite category
then reduces through the homomorphism (`holds_sup`) plus those atoms, rather than by re-inspecting
`compare`. -/

@[simp] theorem holds_before (a b : α) : holds before a b ↔ a < b := by
  simp [holds, before, compare_lt_iff_lt]
@[simp] theorem holds_after (a b : α) : holds after a b ↔ b < a := by
  simp [holds, after, compare_gt_iff_gt]
@[simp] theorem holds_overlapping (a b : α) : holds overlapping a b ↔ a = b := by
  simp [holds, overlapping]
@[simp] theorem holds_notAfter (a b : α) : holds notAfter a b ↔ a ≤ b := by
  rw [notAfter, holds_sup, holds_before, holds_overlapping, le_iff_lt_or_eq]
@[simp] theorem holds_notBefore (a b : α) : holds notBefore a b ↔ b ≤ a := by
  rw [notBefore, holds_sup, holds_after, holds_overlapping, le_iff_lt_or_eq, eq_comm]
@[simp] theorem holds_distinct (a b : α) : holds distinct a b ↔ a ≠ b := by
  rw [distinct, holds_sup, holds_before, holds_after, lt_or_lt_iff_ne]
/-- `unrestricted` is the top of the comparison-category Boolean algebra. -/
theorem unrestricted_eq_top : unrestricted = (⊤ : Finset Ordering) := by decide
@[simp] theorem holds_unrestricted (a b : α) : holds unrestricted a b ↔ True := by
  rw [unrestricted_eq_top, holds_top]

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

/-! ### Relation-algebra laws

The point algebra is a genuine relation algebra: `comp` is associative with unit
`overlapping`, `converse` is an involution that anti-distributes over `comp`,
`comp` is additive and monotone, and the convex fragment is closed under `comp`,
`∩`, and `converse`. All are finite checks over the 8-element carrier (`decide`,
kernel-verified). mathlib has the *concrete* relation category (`SetRel α β` with
`comp`/`inv`, and `CategoryTheory.RelCat`) but no abstract relation-algebra class;
this is the *finite, decidable* point algebra, bridged to the concrete one by
`holds`: `holds s` is the relation `{(a, b) | compare a b ∈ s}` (a `SetRel α α`),
with `converse` mirroring `SetRel.inv` (`holds_converse`) and `comp` sound w.r.t.
`SetRel.comp` (`holds_comp`) — exact only when the order realizes every
intermediate point. -/

theorem comp_assoc (r s t : Finset Ordering) :
    comp (comp r s) t = comp r (comp s t) := by revert r s t; decide

theorem overlapping_comp (s : Finset Ordering) : comp overlapping s = s := by
  revert s; decide

theorem comp_overlapping (s : Finset Ordering) : comp s overlapping = s := by
  revert s; decide

theorem empty_comp (s : Finset Ordering) : comp ∅ s = ∅ := by revert s; decide

theorem comp_empty (s : Finset Ordering) : comp s ∅ = ∅ := by revert s; decide

theorem converse_converse (s : Finset Ordering) : converse (converse s) = s := by
  revert s; decide

theorem converse_comp (r s : Finset Ordering) :
    converse (comp r s) = comp (converse s) (converse r) := by revert r s; decide

theorem comp_union_left (r s t : Finset Ordering) :
    comp (r ∪ s) t = comp r t ∪ comp s t := by revert r s t; decide

theorem comp_union_right (r s t : Finset Ordering) :
    comp r (s ∪ t) = comp r s ∪ comp r t := by revert r s t; decide

theorem comp_mono {r₁ r₂ s₁ s₂ : Finset Ordering} (hr : r₁ ⊆ r₂) (hs : s₁ ⊆ s₂) :
    comp r₁ s₁ ⊆ comp r₂ s₂ := by revert hr hs; revert r₁ r₂ s₁ s₂; decide

theorem isConvex_comp {r s : Finset Ordering} (hr : IsConvex r) (hs : IsConvex s) :
    IsConvex (comp r s) := by revert hr hs; revert r s; decide

theorem isConvex_inter {r s : Finset Ordering} (hr : IsConvex r) (hs : IsConvex s) :
    IsConvex (r ∩ s) := by revert hr hs; revert r s; decide

theorem isConvex_converse {s : Finset Ordering} (hs : IsConvex s) :
    IsConvex (converse s) := by revert hs; revert s; decide

end Core.Order
