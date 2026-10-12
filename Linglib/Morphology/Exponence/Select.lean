module

public import Linglib.Core.Data.List.MinMax
public import Linglib.Morphology.Exponence.Elsewhere
public import Linglib.Morphology.Paradigm.Contiguity

/-!
# Elsewhere selection

This file defines selection by a specificity score (`selectBy`) and over the
specificity preorder (`selectMinimal`), and proves that both produce Elsewhere
winners. The exponent of the minimal selection, falling back on a default where
no rule applies, is the shape shared by Stump's rules of paradigm linkage over a
root and by Bonami and Stump's rules of basic stem choice.

## Main definitions

* `selectBy`, `realize`: the applicable rule of greatest score, and its
  exponent.
* `selectMinimal`, `realizeMinimal`: the first applicable rule that no
  applicable rule strictly undercuts, and its exponent.
* `realizeMinimalD`: the exponent of the minimal selection, or a fallback where
  no rule applies.

## Main results

* `selectBy_eq_some_of_applies`: selection by a score is consistent under contraction, so the
  rule selected in a context stays selected in any context with fewer applicable rules where it
  still applies.
* `selectBy_map`: selection commutes with a map of rules preserving applicability and the
  comparison of scores.
* `isContiguous_realize_of_monotone`, `isContiguous_realize_of_antitone`: rules applicable on
  upper sets, or on lower sets, of ordered contexts realize contiguous patterns when distinct
  rules carry distinct exponents.
* `selectBy_isElsewhereWinner`, `selectMinimal_isElsewhereWinner`: both
  selections produce Elsewhere winners.
* `selectMinimal_factorsThrough`, `realizeMinimalD_factorsThrough`: selection,
  and realization with a fallback, factor through any map on contexts that every
  rule's applicability (and the fallback) factors through.
* `realizeMinimalD_eq_of_isElsewhereWinner`: over a coherent vocabulary with
  comparable winners, realization with a fallback is the exponent of any
  Elsewhere winner, whatever the order of the vocabulary.

## References

* [bonami-stump-2016]
* [stump-2006]
-/

@[expose] public section

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

theorem selectBy_isSome_iff : (selectBy f v c).isSome ↔ ∃ r ∈ v, Applies r c := by
  simp [← Option.ne_none_iff_isSome, selectBy_eq_none_iff, applicable, List.filter_eq_nil_iff]

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

/-- The selected rule scores at least as high as every applicable rule. -/
theorem le_of_selectBy_eq_some (h : selectBy f v c = some r) (hs : s ∈ v) (hsc : Applies s c) :
    f s ≤ f r :=
  List.le_of_mem_argmax (mem_applicable.mpr ⟨hs, hsc⟩) h

/-- An applicable rule scoring at least as high as every applicable rule is realized, provided
the applicable rules with its score share its exponent. -/
theorem realize_eq_of_forall_le (hr : r ∈ v) (hrc : Applies r c)
    (hle : ∀ s ∈ v, Applies s c → f s ≤ f r)
    (heq : ∀ s ∈ v, Applies s c → f s = f r → exponent s = exponent r) :
    realize f v c = some (exponent r) := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (selectBy_isSome_iff (f := f).mpr ⟨r, hr, hrc⟩)
  have hw' := selectBy_mem hw
  have hwc := selectBy_applies hw
  rw [realize, hw, Option.map_some,
    heq w hw' hwc ((hle w hw' hwc).antisymm (le_of_selectBy_eq_some hw hr hrc))]

/-! ### Contraction -/

theorem applicable_eq_filter (h : ∀ s ∈ v, Applies s c → Applies s c') :
    applicable v c = (applicable v c').filter (fun s ↦ Applies s c) := by
  rw [applicable, applicable, List.filter_filter]
  exact List.filter_congr fun s hs ↦ by by_cases hc : Applies s c <;> simp [hc, h s hs]

/-- Selection by a score is consistent under contraction. The rule selected at `c'` is selected
at any context whose applicable rules are among those at `c'`, as long as it applies there. -/
theorem selectBy_eq_some_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : selectBy f v c' = some r) (hrc : Applies r c) : selectBy f v c = some r := by
  rw [selectBy, applicable_eq_filter h]
  exact List.argmax_filter_of_mem hr (by simpa using hrc)

theorem selectBy_eq_none_of_applies (h : ∀ s ∈ v, Applies s c → Applies s c')
    (hr : selectBy f v c' = none) : selectBy f v c = none := by
  rw [selectBy_eq_none_iff, applicable_eq_filter h, selectBy_eq_none_iff.mp hr, List.filter_nil]

/-- Selection admits no ABA. Across three contexts whose applicable rules are nested, an
antihomophonous vocabulary that realizes one exponent at both outer contexts realizes it at the
middle one. -/
theorem realize_eq_of_applies {c₁ c₂ c₃ : Ctx} (hv : Antihomophonous v)
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₂) (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c₃)
    (h : realize f v c₁ = realize f v c₃) : realize f v c₂ = realize f v c₁ := by
  rcases h₃ : selectBy f v c₃ with - | r
  · rw [realize, realize, selectBy_eq_none_of_applies h₂ h₃,
      selectBy_eq_none_of_applies h₁ (selectBy_eq_none_of_applies h₂ h₃)]
  · obtain ⟨r₁, hr₁, he⟩ : ∃ r₁, selectBy f v c₁ = some r₁ ∧ exponent r₁ = exponent r := by
      simpa [realize, h₃] using h
    obtain rfl := hv (selectBy_mem hr₁) (selectBy_mem h₃) he
    rw [realize, realize, hr₁,
      selectBy_eq_some_of_applies h₂ h₃ (h₁ _ (selectBy_mem hr₁) (selectBy_applies hr₁))]

section Contiguity

variable [Preorder Ctx]

/-- Rules applicable on upper sets of contexts realize contiguous patterns. -/
theorem isContiguous_realize_of_monotone (hv : Antihomophonous v)
    (h : ∀ r ∈ v, Monotone (Applies r)) : IsContiguous (realize f v) :=
  fun _ _ _ hij hjk he ↦
    (realize_eq_of_applies hv (fun s hs ↦ h s hs hij) (fun s hs ↦ h s hs hjk) he).symm

/-- Rules applicable on lower sets of contexts realize contiguous patterns. -/
theorem isContiguous_realize_of_antitone (hv : Antihomophonous v)
    (h : ∀ r ∈ v, Antitone (Applies r)) : IsContiguous (realize f v) :=
  fun _ _ _ hij hjk he ↦ he.trans
    (realize_eq_of_applies hv (fun s hs ↦ h s hs hjk) (fun s hs ↦ h s hs hij) he.symm).symm

end Contiguity

/-! ### Transport -/

section Map

variable {R' Ctx' E' : Type*} [Rule R' Ctx' E'] [DecidableRel (Applies : R' → Ctx' → Prop)]
  {β : Type*} [LinearOrder β] {f' : R' → β} {g : R → R'} {c' : Ctx'}

/-- Selection commutes with a map of rules that preserves applicability and the comparison of
scores. -/
theorem selectBy_map (happ : ∀ r ∈ v, Applies (g r) c' ↔ Applies r c)
    (hf : ∀ r ∈ v, ∀ s ∈ v, f' (g r) ≤ f' (g s) ↔ f r ≤ f s) :
    selectBy f' (v.map g) c' = (selectBy f v c).map g := by
  have happ' : applicable (v.map g) c' = (applicable v c).map g := by
    rw [applicable, applicable, List.filter_map]
    exact congrArg _ (List.filter_congr fun r hr ↦ by simp [happ r hr])
  rw [selectBy, happ', List.argmax_map, selectBy]
  exact congrArg _ (List.argmax_congr fun r hr s hs ↦
    hf r (mem_applicable.mp hr).1 s (mem_applicable.mp hs).1)

end Map

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

/-- Contexts with the same applicable rules select the same rule. -/
theorem selectMinimal_congr (h : applicable v c = applicable v c') :
    selectMinimal v c = selectMinimal v c' := by
  rw [selectMinimal, selectMinimal, h]

/-- A rule system sensitive only to what `A` sees selects the same rule in
contexts that `A` identifies. -/
theorem selectMinimal_factorsThrough {V : Type*} {A : Ctx → V}
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (selectMinimal v).FactorsThrough A :=
  fun _ _ hA ↦ selectMinimal_congr <| List.filter_congr fun r hr ↦ by simp [h r hr hA]

/-- The exponent of the rule selected by `selectMinimal`, the order-based counterpart of
`realize`. -/
def realizeMinimal (v : List R) (c : Ctx) : Option E :=
  (selectMinimal v c).map exponent

theorem realizeMinimal_eq_none_iff : realizeMinimal v c = none ↔ applicable v c = [] :=
  Option.map_eq_none_iff.trans selectMinimal_eq_none_iff

theorem realizeMinimal_isSome_iff : (realizeMinimal v c).isSome ↔ ∃ r ∈ v, Applies r c := by
  rw [realizeMinimal, Option.isSome_map]
  exact selectMinimal_isSome_iff

/-- Contexts with the same applicable rules realize the same exponent. -/
theorem realizeMinimal_congr (h : applicable v c = applicable v c') :
    realizeMinimal v c = realizeMinimal v c' :=
  congrArg (Option.map exponent) (selectMinimal_congr h)

/-- Minimally realized exponents satisfy `Realizes`. -/
theorem realizeMinimal_realizes (h : realizeMinimal v c = some φ) : Realizes v c φ := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨r, selectMinimal_isElsewhereWinner hr, rfl⟩

/-- Over a coherent vocabulary whose Elsewhere winners are comparable, the minimally realized
exponent is that of any Elsewhere winner, so it does not depend on the order of the
vocabulary. -/
theorem realizeMinimal_eq_of_isElsewhereWinner (hv : Coherent v)
    (hcmp : ∀ ⦃r s⦄, IsElsewhereWinner v c r → IsElsewhereWinner v c s → s ≤ r ∨ r ≤ s)
    (hr : IsElsewhereWinner v c r) : realizeMinimal v c = some (exponent r) := by
  obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.mp
    (realizeMinimal_isSome_iff.mpr ⟨r, hr.prop.1, hr.prop.2⟩)
  rw [hφ, (realizeMinimal_realizes hφ).eq hv hcmp ⟨r, hr, rfl⟩]

/-! ### Realization with a fallback -/

/-- `realizeMinimalD v fallback c` is the exponent of the rule selected by `selectMinimal`, or
`fallback c` where no rule of `v` applies at `c`. -/
def realizeMinimalD (v : List R) (fallback : Ctx → E) (c : Ctx) : E :=
  (realizeMinimal v c).getD (fallback c)

variable {fallback : Ctx → E}

/-- With no rules, realization is the fallback. -/
@[simp] theorem realizeMinimalD_nil (fallback : Ctx → E) :
    realizeMinimalD ([] : List R) fallback = fallback :=
  funext fun _ ↦ rfl

theorem realizeMinimalD_eq_of_selectMinimal_eq_some (h : selectMinimal v c = some r) :
    realizeMinimalD v fallback c = exponent r := by
  simp [realizeMinimalD, realizeMinimal, h]

theorem realizeMinimalD_eq_fallback_of_selectMinimal_eq_none (h : selectMinimal v c = none) :
    realizeMinimalD v fallback c = fallback c := by
  simp [realizeMinimalD, realizeMinimal, h]

/-- The realized value is the fallback or the exponent of one of the rules. -/
theorem realizeMinimalD_eq_fallback_or_mem : realizeMinimalD v fallback c = fallback c ∨
    ∃ r ∈ v, realizeMinimalD v fallback c = exponent r :=
  match h : selectMinimal v c with
  | none => .inl (realizeMinimalD_eq_fallback_of_selectMinimal_eq_none h)
  | some r => .inr ⟨r, selectMinimal_mem h, realizeMinimalD_eq_of_selectMinimal_eq_some h⟩

/-- A property of the fallback and of every rule's exponent holds of the realized value. -/
theorem realizeMinimalD_induction (q : E → Prop) (hd : q (fallback c))
    (hv : ∀ r ∈ v, q (exponent r)) : q (realizeMinimalD v fallback c) := by
  obtain h | ⟨r, hr, h⟩ :=
    realizeMinimalD_eq_fallback_or_mem (v := v) (fallback := fallback) (c := c)
  · exact h ▸ hd
  · exact h ▸ hv r hr

/-- Contexts with the same applicable rules and the same fallback realize the same value. -/
theorem realizeMinimalD_congr (h : applicable v c = applicable v c')
    (hd : fallback c = fallback c') :
    realizeMinimalD v fallback c = realizeMinimalD v fallback c' := by
  rw [realizeMinimalD, realizeMinimalD, realizeMinimal_congr h, hd]

/-- Rules whose applicability sees only what `A` sees, with a fallback that factors through
`A`, realize values that factor through `A`. This is the reasoning of Stump 2006 (§5.5), by
which a rule of paradigm linkage sensitive to number alone makes number an absolute correlate of
heteroclisis. -/
theorem realizeMinimalD_factorsThrough {V : Type*} {A : Ctx → V}
    (hd : fallback.FactorsThrough A)
    (h : ∀ r ∈ v, ∀ ⦃c c'⦄, A c = A c' → (Applies r c ↔ Applies r c')) :
    (realizeMinimalD v fallback).FactorsThrough A :=
  fun _ _ hA ↦ by rw [realizeMinimalD, realizeMinimalD, realizeMinimal, realizeMinimal,
    selectMinimal_factorsThrough h hA, hd hA]

/-- Over a coherent vocabulary whose Elsewhere winners are comparable, the realized value is the
exponent of any Elsewhere winner, so it does not depend on the order of the vocabulary. -/
theorem realizeMinimalD_eq_of_isElsewhereWinner (hv : Coherent v)
    (hcmp : ∀ ⦃r s⦄, IsElsewhereWinner v c r → IsElsewhereWinner v c s → s ≤ r ∨ r ≤ s)
    (hr : IsElsewhereWinner v c r) : realizeMinimalD v fallback c = exponent r := by
  rw [realizeMinimalD, realizeMinimal_eq_of_isElsewhereWinner hv hcmp hr, Option.getD_some]

end Morphology.Exponence
