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

variable {Ctx E : Type*} {R : Type*} [Preorder R] [Rule R Ctx E]

/-! ### Elsewhere winners -/

/-- A `≤`-minimal applicable rule of `v` at `c`. -/
def IsElsewhereWinner (v : List R) (c : Ctx) (r : R) : Prop :=
  Minimal (fun s => s ∈ v ∧ Applies s c) r

/-- A winner is below every applicable rule that is below it. -/
theorem IsElsewhereWinner.le_of_le {v : List R} {c : Ctx} {r s : R}
    (hr : IsElsewhereWinner v c r) (hs : s ∈ v)
    (happ : Applies s c) (h : s ≤ r) : r ≤ s :=
  Minimal.le_of_le hr ⟨hs, happ⟩ h

/-! ### Coherence and uniqueness -/

/-- Comparable Elsewhere winners at the same context are equivalent. -/
theorem IsElsewhereWinner.antisymmRel {v : List R} {c : Ctx} {r s : R}
    (hr : IsElsewhereWinner v c r) (hs : IsElsewhereWinner v c s)
    (h : s ≤ r ∨ r ≤ s) : AntisymmRel (· ≤ ·) r s := by
  rcases h with h | h
  · exact ⟨hr.le_of_le hs.1.1 hs.1.2 h, h⟩
  · exact ⟨h, hs.le_of_le hr.1.1 hr.1.2 h⟩

/-- A vocabulary is coherent if equivalent rules carry the same exponent. -/
def Coherent (v : List R) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) r s →
    exponent r = exponent s

/-- Comparable winners of a coherent vocabulary carry the same exponent. -/
theorem IsElsewhereWinner.exponent_eq {v : List R} {c : Ctx} {r s : R}
    (hv : Coherent v) (hr : IsElsewhereWinner v c r)
    (hs : IsElsewhereWinner v c s) (h : s ≤ r ∨ r ≤ s) :
    exponent r = exponent s :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

/-- A vocabulary with an applicable rule has an Elsewhere winner. -/
theorem exists_isElsewhereWinner {v : List R} {c : Ctx}
    (h : ∃ r ∈ v, Applies r c) : ∃ r, IsElsewhereWinner v c r :=
  (v.finite_toSet.subset fun _ hr => hr.1).exists_minimal h

/-! ### The prediction relation -/

/-- `φ` is realized at `c` when some Elsewhere winner carries it. -/
def Realizes (v : List R) (c : Ctx) (φ : E) : Prop :=
  ∃ r, IsElsewhereWinner v c r ∧ exponent r = φ

/-- Over a coherent vocabulary with comparable winners, the prediction is unique. -/
theorem Realizes.eq {v : List R} {c : Ctx} {φ ψ : E} (hv : Coherent v)
    (hcmp : ∀ ⦃r s⦄, IsElsewhereWinner v c r → IsElsewhereWinner v c s → s ≤ r ∨ r ≤ s)
    (hφ : Realizes v c φ) (hψ : Realizes v c ψ) : φ = ψ := by
  obtain ⟨r, hr, rfl⟩ := hφ
  obtain ⟨s, hs, rfl⟩ := hψ
  exact hr.exponent_eq hv hs (hcmp hr hs)

/-! ### Score selection -/

variable [∀ c : Ctx, DecidablePred (fun r : R => Applies r c)]

/-- The rules of `v` applicable at `c`, in vocabulary order. -/
def applicable (v : List R) (c : Ctx) : List R :=
  v.filter (fun r => Applies r c)

omit [Preorder R] in
@[simp] theorem mem_applicable {v : List R} {c : Ctx} {r : R} :
    r ∈ applicable v c ↔ r ∈ v ∧ Applies r c := by
  simp only [applicable, List.mem_filter, decide_eq_true_eq]

variable {α : Type*} [LinearOrder α]

/-- The applicable rule of greatest score `f`, ties broken by vocabulary
order; scores to be minimized pass through `OrderDual`. -/
def selectBy (f : R → α) (v : List R) (c : Ctx) : Option R :=
  (applicable v c).argmax f

omit [Preorder R] in
theorem selectBy_mem {f : R → α} {v : List R} {c : Ctx} {r : R}
    (h : selectBy f v c = some r) : r ∈ v :=
  (mem_applicable.mp (List.argmax_mem h)).1

omit [Preorder R] in
theorem selectBy_applies {f : R → α} {v : List R} {c : Ctx} {r : R}
    (h : selectBy f v c = some r) : Applies r c :=
  (mem_applicable.mp (List.argmax_mem h)).2

omit [Preorder R] in
theorem selectBy_eq_none_iff {f : R → α} {v : List R} {c : Ctx} :
    selectBy f v c = none ↔ applicable v c = [] :=
  List.argmax_eq_none

/-- When the score reflects specificity, the selection is below every
applicable rule. -/
theorem selectBy_le_of_applies {f : R → α} {v : List R} {c : Ctx} {r s : R}
    (hf : ∀ r ∈ v, ∀ s ∈ v, Applies r c →
      Applies s c → (r ≤ s ↔ f s ≤ f r))
    (h : selectBy f v c = some r) (hs : s ∈ v)
    (hsapp : Applies s c) : r ≤ s :=
  (hf r (selectBy_mem h) s hs (selectBy_applies h) hsapp).mpr
    (List.le_of_mem_argmax (mem_applicable.mpr ⟨hs, hsapp⟩) h)

/-- When the score reflects specificity on comparable applicable rules,
`selectBy` returns an Elsewhere winner. -/
theorem selectBy_isElsewhereWinner {f : R → α} {v : List R} {c : Ctx} {r : R}
    (hf : ∀ r ∈ v, ∀ s ∈ v, Applies r c →
      Applies s c → s ≤ r → f s ≤ f r → r ≤ s)
    (h : selectBy f v c = some r) : IsElsewhereWinner v c r := by
  refine ⟨⟨selectBy_mem h, selectBy_applies h⟩, ?_⟩
  rintro s ⟨hs, hsapp⟩ hsr
  exact hf r (selectBy_mem h) s hs (selectBy_applies h) hsapp hsr
    (List.le_of_mem_argmax (mem_applicable.mpr ⟨hs, hsapp⟩) h)

omit [Preorder R] in
/-- Contexts with the same applicable rules select the same rule. -/
theorem selectBy_congr {f : R → α} {v : List R} {c c' : Ctx}
    (h : applicable v c = applicable v c') :
    selectBy f v c = selectBy f v c' := by
  rw [selectBy, selectBy, h]

/-! ### Realization -/

/-- The exponent of the rule selected by `selectBy`. -/
def realize (f : R → α) (v : List R) (c : Ctx) : Option E :=
  (selectBy f v c).map (exponent)

/-- Realized exponents satisfy `Realizes`. -/
theorem realize_realizes {f : R → α} {v : List R} {c : Ctx} {φ : E}
    (hf : ∀ r ∈ v, ∀ s ∈ v, Applies r c →
      Applies s c → s ≤ r → f s ≤ f r → r ≤ s)
    (h : realize f v c = some φ) : Realizes v c φ := by
  rw [realize, Option.map_eq_some_iff] at h
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨r, selectBy_isElsewhereWinner hf hr, rfl⟩

omit [Preorder R] in
theorem realize_eq_none_iff {f : R → α} {v : List R} {c : Ctx} :
    realize f v c = none ↔ applicable v c = [] := by
  rw [realize, Option.map_eq_none_iff]
  exact selectBy_eq_none_iff

omit [Preorder R] in
theorem realize_congr {f : R → α} {v : List R} {c c' : Ctx}
    (h : applicable v c = applicable v c') :
    realize f v c = realize f v c' := by
  rw [realize, realize, selectBy_congr h]

/-! ### Order selection -/

variable [DecidableRel (· < · : R → R → Prop)]

/-- The first applicable rule that no applicable rule strictly undercuts. -/
def selectMinimal (v : List R) (c : Ctx) : Option R :=
  (applicable v c).find? (fun r => (applicable v c).all (fun s => decide (¬ s < r)))

theorem selectMinimal_mem {v : List R} {c : Ctx} {r : R}
    (h : selectMinimal v c = some r) : r ∈ v :=
  (mem_applicable.mp (List.mem_of_find?_eq_some h)).1

theorem selectMinimal_applies {v : List R} {c : Ctx} {r : R}
    (h : selectMinimal v c = some r) : Applies r c :=
  (mem_applicable.mp (List.mem_of_find?_eq_some h)).2

/-- `selectMinimal` returns an Elsewhere winner. -/
theorem selectMinimal_isElsewhereWinner {v : List R} {c : Ctx} {r : R}
    (h : selectMinimal v c = some r) : IsElsewhereWinner v c r := by
  have hall := List.find?_some h
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable] at hall
  exact ⟨mem_applicable.mp (List.mem_of_find?_eq_some h),
    fun s hs => not_lt_iff_le_imp_ge.mp (hall s hs)⟩

/-- `selectMinimal` succeeds iff some rule applies. -/
theorem selectMinimal_isSome_iff {v : List R} {c : Ctx} :
    (selectMinimal v c).isSome ↔ ∃ r ∈ v, Applies r c := by
  rw [selectMinimal, List.find?_isSome]
  simp only [List.all_eq_true, decide_eq_true_eq, mem_applicable]
  exact ⟨fun ⟨r, hr, _⟩ => ⟨r, hr⟩, fun h => (exists_isElsewhereWinner h).imp
    fun w hw => ⟨hw.1, fun s hs => hw.not_lt hs⟩⟩

theorem selectMinimal_eq_none_iff {v : List R} {c : Ctx} :
    selectMinimal v c = none ↔ applicable v c = [] := by
  rw [← Option.not_isSome_iff_eq_none, selectMinimal_isSome_iff]
  simp [applicable, List.filter_eq_nil_iff]

end Morphology.Exponence
