/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.PresentedMonoid.Basic
import Mathlib.GroupTheory.Congruence.Basic
import Linglib.Core.Data.List.Destutter

/-!
# The destutter quotient monoid of a free monoid

For `[DecidableEq α]`, `List.destutter (· ≠ ·)` collapses each maximal run of equal adjacent
elements to one; the lists it fixes are exactly the `List.IsChain (· ≠ ·)` lists (no two
adjacent elements equal). Under **append-then-destutter** these form a monoid, and
`List.destutter (· ≠ ·)` is the quotient homomorphism out of the free monoid:
`{l // l.IsChain (· ≠ ·)} ≃* FreeMonoid α ⧸ ker`.

Abstractly this is the monoid **presented by idempotent generators** `⟨α | a · a = a⟩`: the
defining relations `destutterRel` make each generator absorb its own repeat, the rewriting
system `a · a → a` is confluent and terminating, and `destutter (· ≠ ·)` computes its normal
forms — the stutter-free words. `presentedMonoidEquiv` packages this as a `MulEquiv`
`PresentedMonoid (destutterRel α) ≃* {l // l.IsChain (· ≠ ·)}`, identifying the abstract
presentation with the concrete normal-form model.

## Main definitions

* `Monoid {l : List α // l.IsChain (· ≠ ·)}` — the destutter quotient monoid, with
  multiplication `List.destutterConcat` (from `Core.Data.List.Destutter`).
* `FreeMonoid.destutterHom` — the quotient map `FreeMonoid α →* {l // l.IsChain (· ≠ ·)}`.
* `FreeMonoid.destutterRel` — the presentation `⟨α | a · a = a⟩`: each generator is idempotent.
* `FreeMonoid.destutterQuotientEquiv` — first isomorphism `FreeMonoid α ⧸ ker ≃* {l // …}`.
* `FreeMonoid.presentedMonoidEquiv` — the concrete model is the presented monoid
  `PresentedMonoid (destutterRel α) ≃* {l // l.IsChain (· ≠ ·)}`.
* `FreeMonoid.destutterLift` — the **universal property**: the destutter monoid is the free
  monoid on idempotent generators; any `f : α → M` with `f a * f a = f a` extends uniquely
  (`destutterLift_unique`) to a monoid hom `l ↦ (l.map f).prod`.

## Implementation notes

The `destutter`-vs-`++` congruence lemmas live in `Core.Data.List.Destutter` (candidates
for `Mathlib.Data.List.Destutter`); this file adds the monoid/presentation layer (candidate
for `Mathlib.Algebra.FreeMonoid`). The monoid multiplication is associative because
`destutter (· ≠ ·)` is a `++`-congruence (`destutter_append_left`/`_right` from that file);
the presentation is identified with the concrete model by the normalization lemma
`conGen_destutterRel_destutter`. Nothing here is specific to any application; the phonological
Obligatory Contour Principle (`Phonology.OCP`) is one consumer, reading the presentation as
autosegmental tier fusion.
-/

namespace List

variable {α : Type*} [DecidableEq α]

/-! ### The bundled quotient monoid

The multiplication `List.destutterConcat` (append then destutter) and its `List`-level laws
live in `Core.Data.List.Destutter`; here they are bundled into the monoid structure. -/

instance : Mul {l : List α // l.IsChain (· ≠ ·)} :=
  ⟨fun a b => ⟨destutterConcat a b, isChain_destutterConcat _ _⟩⟩

instance : One {l : List α // l.IsChain (· ≠ ·)} := ⟨⟨[], isChain_nil⟩⟩

@[simp] theorem coe_mul (a b : {l : List α // l.IsChain (· ≠ ·)}) :
    ((a * b : {l : List α // l.IsChain (· ≠ ·)}) : List α) = destutterConcat a b := rfl

omit [DecidableEq α] in
@[simp] theorem coe_one :
    ((1 : {l : List α // l.IsChain (· ≠ ·)}) : List α) = [] := rfl

/-- The destutter quotient monoid: `destutterConcat` multiplication, `[]` unit. -/
instance : Monoid {l : List α // l.IsChain (· ≠ ·)} where
  mul_assoc a b c := Subtype.ext (destutterConcat_assoc _ _ _)
  one_mul a := Subtype.ext (destutter_of_isChain _ _ a.2)
  mul_one a := Subtype.ext <| by simp [destutterConcat_nil, destutter_of_isChain _ _ a.2]

end List

namespace FreeMonoid

open List

variable {α : Type*} [DecidableEq α]

/-- The **destutter quotient map**: send a free-monoid word to its `destutter (· ≠ ·)`
normal form. `List.destutter_append_destutter` is its `map_mul`. -/
def destutterHom : FreeMonoid α →* {l : List α // l.IsChain (· ≠ ·)} where
  toFun l := ⟨l.toList.destutter (· ≠ ·), isChain_destutter _ _⟩
  map_one' := Subtype.ext (by simp [FreeMonoid.toList_one])
  map_mul' x y := Subtype.ext <| by
    simp [FreeMonoid.toList_mul, List.destutter_append_eq_destutterConcat]

/-- `ofList` of a stutter-free list is a right inverse of `destutterHom`: a chain is its own
destutter normal form. -/
@[simp] theorem destutterHom_ofList (c : {l : List α // l.IsChain (· ≠ ·)}) :
    destutterHom (FreeMonoid.ofList c.1) = c :=
  Subtype.ext <| by
    simp only [destutterHom, MonoidHom.coe_mk, OneHom.coe_mk, FreeMonoid.toList_ofList]
    exact destutter_of_isChain _ _ c.2

theorem destutterHom_surjective :
    Function.Surjective (destutterHom : FreeMonoid α →* {l : List α // l.IsChain (· ≠ ·)}) :=
  fun c => ⟨FreeMonoid.ofList c.1, destutterHom_ofList c⟩

/-- The destutter congruence on the free monoid: the kernel of `destutterHom`. -/
def destutterCon : Con (FreeMonoid α) := Con.ker destutterHom

/-- **First isomorphism theorem** for the destutter quotient: the abstract quotient
`FreeMonoid α ⧸ ker` is the concrete stutter-free model `{l // l.IsChain (· ≠ ·)}`.
Computable: `ofList` on chains is the right inverse. -/
def destutterQuotientEquiv :
    (destutterCon (α := α)).Quotient ≃* {l : List α // l.IsChain (· ≠ ·)} :=
  Con.quotientKerEquivOfRightInverse destutterHom (fun c => FreeMonoid.ofList c.1)
    destutterHom_ofList

/-! ### The monoid presentation `⟨α | a · a = a⟩` -/

/-- The defining relations of the destutter monoid: every generator is **idempotent**
(`a · a = a`). The presented monoid `PresentedMonoid (destutterRel α)` is `⟨α | a · a = a⟩`. -/
def destutterRel (α : Type*) : FreeMonoid α → FreeMonoid α → Prop :=
  fun x y => ∃ a : α, x = of a * of a ∧ y = of a

/-- `destutterHom` collapses each defining relation: `destutter [a, a] = [a]`. -/
theorem destutterHom_destutterRel {x y : FreeMonoid α} (h : destutterRel α x y) :
    destutterHom x = destutterHom y := by
  obtain ⟨a, rfl, rfl⟩ := h
  exact Subtype.ext (by simp [destutterHom, FreeMonoid.toList_mul, FreeMonoid.toList_of])

/-- Running-element form of the normalization lemma: prepending the running element `a`,
the word `a :: l` is congruent to its `destutter'`. -/
private theorem conGen_destutterRel_destutter' (a : α) (l : List α) :
    (conGen (destutterRel α)) (of a * ofList l) (ofList (l.destutter' (· ≠ ·) a)) := by
  induction l generalizing a with
  | nil => simpa [destutter'_nil, ofList_cons] using (conGen (destutterRel α)).refl (of a)
  | cons b l ih =>
    by_cases h : a ≠ b
    · rw [destutter'_cons_pos (h := h), ofList_cons, ofList_cons]
      exact (conGen (destutterRel α)).mul ((conGen (destutterRel α)).refl (of a)) (ih b)
    · obtain rfl : a = b := not_not.mp h
      have hbase : (conGen (destutterRel α)) (of a * of a) (of a) :=
        ConGen.Rel.of _ _ ⟨a, rfl, rfl⟩
      rw [destutter'_cons_neg (h := by simp), ofList_cons, ← mul_assoc]
      exact (conGen (destutterRel α)).trans
        ((conGen (destutterRel α)).mul hbase ((conGen (destutterRel α)).refl (ofList l))) (ih a)

/-- **Normalization**: every free-monoid word is congruent, modulo the idempotent-generator
relations, to its `destutter (· ≠ ·)` normal form. The rewriting system `a · a → a` reduces
each word to a stutter-free one. -/
theorem conGen_destutterRel_destutter (l : List α) :
    (conGen (destutterRel α)) (ofList l) (ofList (l.destutter (· ≠ ·))) := by
  cases l with
  | nil => exact (conGen (destutterRel α)).refl _
  | cons a l => rw [destutter_cons']; exact conGen_destutterRel_destutter' a l

/-- The destutter congruence **is** the presentation `⟨α | a · a = a⟩`: two words have the
same destutter exactly when the idempotent-generator relations identify them. -/
theorem destutterCon_eq_conGen : destutterCon (α := α) = conGen (destutterRel α) := by
  refine le_antisymm (fun x y hxy => ?_) (Con.conGen_le.2 ?_)
  · have hxy' : destutterHom x = destutterHom y := hxy
    have hval : x.toList.destutter (· ≠ ·) = y.toList.destutter (· ≠ ·) :=
      congrArg Subtype.val hxy'
    have nx := conGen_destutterRel_destutter (α := α) x.toList
    have ny := conGen_destutterRel_destutter (α := α) y.toList
    rw [hval] at nx
    exact (conGen (destutterRel α)).trans nx ((conGen (destutterRel α)).symm ny)
  · intro x y h
    exact destutterHom_destutterRel h

/-- The concrete stutter-free model **is** the monoid presented by idempotent generators
`⟨α | a · a = a⟩`, with `destutter (· ≠ ·)` computing normal forms. -/
def presentedMonoidEquiv :
    PresentedMonoid (destutterRel α) ≃* {l : List α // l.IsChain (· ≠ ·)} := by
  have h : (conGen (destutterRel α)).Quotient ≃* (destutterCon (α := α)).Quotient :=
    (destutterCon_eq_conGen (α := α)).symm ▸ MulEquiv.refl (destutterCon (α := α)).Quotient
  exact h.trans destutterQuotientEquiv

/-! ### Universal property: the free monoid on idempotent generators -/

variable {M : Type*} [Monoid M]

/-- `(· .map f).prod` is invariant under `destutter (· ≠ ·)` when each `f a` is idempotent:
collapsing an adjacent run replaces `f a * f a` by `f a`. The engine of `destutterLift`,
read off the normalization lemma `conGen_destutterRel_destutter`. -/
theorem destutter_map_prod (f : α → M) (hf : ∀ a, f a * f a = f a) (xs : List α) :
    ((xs.destutter (· ≠ ·)).map f).prod = (xs.map f).prod := by
  have hle : conGen (destutterRel α) ≤ Con.ker (FreeMonoid.lift f) :=
    Con.conGen_le.2 fun x y h => by obtain ⟨a, rfl, rfl⟩ := h; simp [hf]
  have h := hle (conGen_destutterRel_destutter xs)
  rw [Con.ker_apply, FreeMonoid.lift_ofList, FreeMonoid.lift_ofList] at h
  exact h.symm

/-- **Universal property** — the destutter monoid is the *free monoid on idempotent
generators*: any `f : α → M` sending each generator to an idempotent element of `M` extends
to the monoid hom `l ↦ (l.map f).prod` out of the stutter-free model. This realizes
`PresentedMonoid.lift`'s universal property for the presentation `⟨α | a · a = a⟩` (via
`presentedMonoidEquiv`) in concrete computable form — the destutter-monoid analogue of
`FreeMonoid.lift`. -/
def destutterLift (f : α → M) (hf : ∀ a, f a * f a = f a) :
    {l : List α // l.IsChain (· ≠ ·)} →* M where
  toFun l := (l.1.map f).prod
  map_one' := rfl
  map_mul' a b := by
    show ((destutterConcat a.1 b.1).map f).prod = (a.1.map f).prod * (b.1.map f).prod
    rw [← List.prod_append, ← List.map_append]
    exact destutter_map_prod f hf (a.1 ++ b.1)

@[simp] theorem destutterLift_singleton (f : α → M) (hf : ∀ a, f a * f a = f a) (a : α) :
    destutterLift f hf ⟨[a], isChain_singleton a⟩ = f a := by
  simp [destutterLift]

/-- A stutter-free list is the product of its single-element generators (no fusion occurs,
since it is already a chain): the generators generate. -/
theorem eq_prod_map_singleton {l : List α} (hl : l.IsChain (· ≠ ·)) :
    (⟨l, hl⟩ : {l : List α // l.IsChain (· ≠ ·)})
      = (l.map fun a => ⟨[a], isChain_singleton a⟩).prod := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ht : t.IsChain (· ≠ ·) := hl.tail
    rw [List.map_cons, List.prod_cons, ← ih ht]
    exact Subtype.ext (destutter_of_isChain _ _ hl).symm

/-- **Uniqueness** for the universal property: any monoid hom agreeing with `f` on the
single-autosegment generators is `destutterLift f hf`. -/
theorem destutterLift_unique (f : α → M) (hf : ∀ a, f a * f a = f a)
    (g : {l : List α // l.IsChain (· ≠ ·)} →* M)
    (hg : ∀ a, g ⟨[a], isChain_singleton a⟩ = f a) : g = destutterLift f hf := by
  ext ⟨l, hl⟩
  have hgprod : g ⟨l, hl⟩ = (l.map f).prod := by
    conv_lhs => rw [eq_prod_map_singleton hl]
    rw [g.map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun a _ => by simpa using hg a)
  rw [hgprod]; rfl

end FreeMonoid
