import Linglib.Morphology.Exponence.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.MinMax

/-!
# Elsewhere selection

This file proves that selection by a specificity score (`selectBy`) and
selection over the specificity preorder (`selectMinimal`) produce Elsewhere
winners: `≤`-minimal applicable rules of exponence ([kiparsky-1973]).

## Main definitions

* `IsElsewhereWinner`: a `≤`-minimal applicable rule of a vocabulary at a
  context.
* `Realizes`: some Elsewhere winner carries the given exponent.
* `selectBy`, `realize`: the applicable rule of greatest score, and its
  exponent.
* `selectMinimal`: the first applicable rule that no applicable rule
  strictly undercuts.
-/

namespace Morphology.Exponence

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E]
variable {v : List R} {c c' : Ctx} {r s : R} {φ : E}

/-! ### Score selection -/

/-- The rules of `v` applicable at `c`, in vocabulary order. -/
def applicable (v : List R) (c : Ctx) : List R :=
  v.filter (fun r => Applies r c)

@[simp] theorem mem_applicable :
    r ∈ applicable v c ↔ r ∈ v ∧ Applies r c := by
  simp only [applicable, List.mem_filter, decide_eq_true_eq]

variable {α : Type*} [LinearOrder α] {f : R → α}

/-- The applicable rule of greatest score `f`, ties broken by vocabulary
order; scores to be minimized pass through `OrderDual`. -/
def selectBy (f : R → α) (v : List R) (c : Ctx) : Option R :=
  (applicable v c).argmax f

theorem selectBy_mem (h : selectBy f v c = some r) : r ∈ v :=
  (mem_applicable.mp (List.argmax_mem h)).1

theorem selectBy_applies (h : selectBy f v c = some r) : Applies r c :=
  (mem_applicable.mp (List.argmax_mem h)).2

theorem selectBy_eq_none_iff : selectBy f v c = none ↔ applicable v c = [] :=
  List.argmax_eq_none

/-- Contexts with the same applicable rules select the same rule. -/
theorem selectBy_congr (h : applicable v c = applicable v c') :
    selectBy f v c = selectBy f v c' := by
  rw [selectBy, selectBy, h]

/-- The exponent of the rule selected by `selectBy`. -/
def realize (f : R → α) (v : List R) (c : Ctx) : Option E :=
  (selectBy f v c).map exponent

theorem realize_eq_none_iff : realize f v c = none ↔ applicable v c = [] :=
  Option.map_eq_none_iff.trans selectBy_eq_none_iff

theorem realize_congr (h : applicable v c = applicable v c') :
    realize f v c = realize f v c' :=
  congrArg (Option.map exponent) (selectBy_congr h)

/-! ### Elsewhere winners -/

variable [Preorder R]

/-- Two comparable minimal elements of the same predicate are equivalent.
[UPSTREAM] candidate for `Mathlib/Order/Minimal.lean`. -/
theorem _root_.Minimal.antisymmRel {α : Type*} [Preorder α] {P : α → Prop} {x y : α}
    (hx : Minimal P x) (hy : Minimal P y) (h : y ≤ x ∨ x ≤ y) :
    AntisymmRel (· ≤ ·) x y :=
  h.elim (fun h => ⟨hx.le_of_le hy.1 h, h⟩) (fun h => ⟨h, hy.le_of_le hx.1 h⟩)

/-- A `≤`-minimal applicable rule of `v` at `c`. -/
abbrev IsElsewhereWinner (v : List R) (c : Ctx) (r : R) : Prop :=
  Minimal (fun s => s ∈ v ∧ Applies s c) r

/-- A vocabulary is coherent if equivalent rules carry the same exponent. -/
def Coherent (v : List R) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) r s →
    exponent r = exponent s

/-- Comparable winners of a coherent vocabulary carry the same exponent. -/
theorem IsElsewhereWinner.exponent_eq
    (hv : Coherent v) (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s ≤ r ∨ r ≤ s) :
    exponent r = exponent s :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

/-- A vocabulary with an applicable rule has an Elsewhere winner. -/
theorem exists_isElsewhereWinner
    (h : ∃ r ∈ v, Applies r c) : ∃ r, IsElsewhereWinner v c r :=
  (v.finite_toSet.subset fun _ hr => hr.1).exists_minimal h

/-! ### The prediction relation -/

/-- `φ` is realized at `c` when some Elsewhere winner carries it. -/
def Realizes (v : List R) (c : Ctx) (φ : E) : Prop :=
  ∃ r, IsElsewhereWinner v c r ∧ exponent r = φ

/-- Over a coherent vocabulary with comparable winners, the prediction is unique. -/
theorem Realizes.eq {ψ : E} (hv : Coherent v)
    (hcmp : ∀ ⦃r s⦄, IsElsewhereWinner v c r → IsElsewhereWinner v c s → s ≤ r ∨ r ≤ s)
    (hφ : Realizes v c φ) (hψ : Realizes v c ψ) : φ = ψ := by
  obtain ⟨r, hr, rfl⟩ := hφ
  obtain ⟨s, hs, rfl⟩ := hψ
  exact hr.exponent_eq hv hs (hcmp hr hs)

/-! ### Soundness -/

/-- A score strictly antitone on the applicable rules selects an
Elsewhere winner. -/
theorem selectBy_isElsewhereWinner
    (hf : StrictAntiOn f {r | r ∈ applicable v c})
    (h : selectBy f v c = some r) : IsElsewhereWinner v c r := by
  refine ⟨mem_applicable.mp (List.argmax_mem h), fun s hs hsr => ?_⟩
  by_contra hrs
  exact absurd (List.le_of_mem_argmax (mem_applicable.mpr hs) h)
    (not_le_of_gt (hf (mem_applicable.mpr hs) (List.argmax_mem h)
      (lt_of_le_not_ge hsr hrs)))

/-- Realized exponents satisfy `Realizes`. -/
theorem realize_realizes (hf : StrictAntiOn f {r | r ∈ applicable v c})
    (h : realize f v c = some φ) : Realizes v c φ := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, selectBy_isElsewhereWinner hf hr, rfl⟩

/-! ### Order selection -/

variable [DecidableRel (· < · : R → R → Prop)]

/-- The first applicable rule that no applicable rule strictly undercuts. -/
def selectMinimal (v : List R) (c : Ctx) : Option R :=
  (applicable v c).find? (fun r => (applicable v c).all (fun s => decide (¬ s < r)))

/-- `selectMinimal` returns an Elsewhere winner. -/
theorem selectMinimal_isElsewhereWinner
    (h : selectMinimal v c = some r) : IsElsewhereWinner v c r := by
  have hall := List.find?_some h
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable] at hall
  exact minimal_iff_forall_lt.mpr
    ⟨mem_applicable.mp (List.mem_of_find?_eq_some h), fun s hlt hs => hall s hs hlt⟩

theorem selectMinimal_mem (h : selectMinimal v c = some r) : r ∈ v :=
  (selectMinimal_isElsewhereWinner h).prop.1

theorem selectMinimal_applies (h : selectMinimal v c = some r) : Applies r c :=
  (selectMinimal_isElsewhereWinner h).prop.2

/-- `selectMinimal` succeeds iff some rule applies. -/
theorem selectMinimal_isSome_iff :
    (selectMinimal v c).isSome ↔ ∃ r ∈ v, Applies r c := by
  rw [selectMinimal, List.find?_isSome]
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable]
  exact ⟨fun ⟨r, hr, _⟩ => ⟨r, hr⟩, fun h => (exists_isElsewhereWinner h).imp
    fun w hw => ⟨hw.1, fun s hs => hw.not_lt hs⟩⟩

theorem selectMinimal_eq_none_iff :
    selectMinimal v c = none ↔ applicable v c = [] := by
  rw [← Option.not_isSome_iff_eq_none, selectMinimal_isSome_iff]
  simp [applicable, List.filter_eq_nil_iff]

end Morphology.Exponence
