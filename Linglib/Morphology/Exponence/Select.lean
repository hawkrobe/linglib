import Linglib.Morphology.Exponence.Elsewhere
import Mathlib.Data.List.MinMax

/-!
# Elsewhere selection

This file proves that selection by a specificity score (`selectBy`) and
selection over the specificity preorder (`selectMinimal`) produce Elsewhere
winners.

## Main definitions

* `selectBy`, `realize`: the applicable rule of greatest score, and its
  exponent.
* `selectMinimal`: the first applicable rule that no applicable rule
  strictly undercuts.
* `selectBy_isElsewhereWinner`, `selectMinimal_isElsewhereWinner`: both
  selections produce Elsewhere winners.
-/

namespace Morphology.Exponence

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E]
variable [DecidableRel (Applies : R → Ctx → Prop)]
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

/-! ### Soundness -/

variable [Preorder R]

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
