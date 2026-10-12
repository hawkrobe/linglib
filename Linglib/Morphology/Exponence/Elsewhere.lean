module

public import Linglib.Morphology.Exponence.Basic
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Data.Set.Finite.Basic

/-!
# The Elsewhere Condition

An Elsewhere winner of a vocabulary at a context is a rule that applies there and is minimal,
among the rules that apply, in Kiparsky's specificity preorder. This file defines Elsewhere
winners and the prediction relation they induce.

## Main definitions

* `Vocabulary.IsElsewhereWinner`: a `≤`-minimal applicable rule of a vocabulary at a
  context.
* `Vocabulary.Coherent`: equivalent rules carry the same exponent.
* `Vocabulary.Realizes`: some Elsewhere winner carries the given exponent.
* `Vocabulary.Antihomophonous`: distinct rules carry distinct exponents.

## Main results

* `Vocabulary.Realizes.eq`: where the Elsewhere winners form a chain, Pāṇinian Determinism, a
  coherent vocabulary makes a unique prediction.
* `Vocabulary.Realizes.of_realizes`: no ABA pattern across nested contexts.

## References

* [kiparsky-1973]
* [bobaljik-2012]
-/

@[expose] public section

namespace Morphology.Exponence.Vocabulary

variable {Ctx E : Type*} {R : Type*} [Rule R Ctx E] [Preorder R]
variable {v : Vocabulary R} {c : Ctx} {r s : R} {φ : E}

/-! ### Elsewhere winners -/

/-- Two comparable minimal elements of the same predicate are equivalent.
[UPSTREAM] candidate for `Mathlib/Order/Minimal.lean`. -/
theorem _root_.Minimal.antisymmRel {α : Type*} [Preorder α] {P : α → Prop} {x y : α}
    (hx : Minimal P x) (hy : Minimal P y) (h : y ≤ x ∨ x ≤ y) :
    AntisymmRel (· ≤ ·) x y :=
  h.elim (fun h ↦ ⟨hx.le_of_le hy.1 h, h⟩) (fun h ↦ ⟨h, hy.le_of_le hx.1 h⟩)

/-- A `≤`-minimal applicable rule of `v` at `c`. -/
abbrev IsElsewhereWinner (v : Vocabulary R) (c : Ctx) (r : R) : Prop :=
  Minimal (fun s ↦ s ∈ v ∧ Applies s c) r

/-- A vocabulary is coherent if equivalent rules carry the same exponent. -/
def Coherent (v : Vocabulary R) : Prop :=
  ∀ r ∈ v, ∀ s ∈ v, AntisymmRel (· ≤ ·) r s →
    exponent r = exponent s

/-- Comparable winners of a coherent vocabulary carry the same exponent. -/
theorem IsElsewhereWinner.exponent_eq
    (hv : v.Coherent) (hr : v.IsElsewhereWinner c r)
    (hs : v.IsElsewhereWinner c s) (h : s ≤ r ∨ r ≤ s) :
    exponent r = exponent s :=
  hv r hr.1.1 s hs.1.1 (hr.antisymmRel hs h)

/-- A vocabulary with an applicable rule has an Elsewhere winner. -/
theorem exists_isElsewhereWinner
    (h : ∃ r ∈ v, Applies r c) : ∃ r, v.IsElsewhereWinner c r :=
  (v.finite_toSet.subset fun _ hr ↦ hr.1).exists_minimal h

/-! ### The prediction relation -/

/-- `φ` is realized at `c` when some Elsewhere winner carries it. -/
def Realizes (v : Vocabulary R) (c : Ctx) (φ : E) : Prop :=
  ∃ r, v.IsElsewhereWinner c r ∧ exponent r = φ

/-- Over a coherent vocabulary whose Elsewhere winners form a chain, Stump's Pāṇinian
Determinism, the prediction is unique. -/
theorem Realizes.eq {ψ : E} (hv : v.Coherent) (hc : IsChain (· ≤ ·) {s | v.IsElsewhereWinner c s})
    (hφ : v.Realizes c φ) (hψ : v.Realizes c ψ) : φ = ψ := by
  obtain ⟨r, hr, rfl⟩ := hφ
  obtain ⟨s, hs, rfl⟩ := hψ
  exact hr.exponent_eq hv hs (hc.total hs hr)

/-! ### Containment -/

/-- A vocabulary is **antihomophonous** when distinct rules carry distinct exponents, the
Antihomophony assumption of [bobaljik-2012] that sets accidental homophony aside. -/
def Antihomophonous (v : Vocabulary R) : Prop :=
  Set.InjOn exponent {r | r ∈ v}

instance [DecidableEq R] [DecidableEq E] (v : Vocabulary R) : Decidable v.Antihomophonous :=
  inferInstanceAs (Decidable (∀ r ∈ v, ∀ s ∈ v, exponent r = exponent s → r = s))

/-- A winner at a context that applies at a smaller context, in the sense that every rule
applicable there is applicable at the larger, is a winner at the smaller. -/
theorem IsElsewhereWinner.of_applies {c' : Ctx} (h : ∀ s ∈ v, Applies s c' → Applies s c)
    (hr : v.IsElsewhereWinner c r) (hc' : Applies r c') : v.IsElsewhereWinner c' r :=
  hr.mono (fun s hs ↦ ⟨hs.1, h s hs.1 hs.2⟩) ⟨hr.1.1, hc'⟩

/-- There is no ABA across nested contexts. Over an antihomophonous vocabulary, an exponent
realized at the smallest and the largest of three nested contexts is realized at the middle
one. -/
theorem Realizes.of_realizes {c₁ c₂ : Ctx} (hv : v.Antihomophonous)
    (h₁ : ∀ s ∈ v, Applies s c₁ → Applies s c₂) (h₂ : ∀ s ∈ v, Applies s c₂ → Applies s c)
    (hr₁ : v.Realizes c₁ φ) (hr : v.Realizes c φ) : v.Realizes c₂ φ := by
  obtain ⟨t, ht, rfl⟩ := hr
  obtain ⟨u, hu, hut⟩ := hr₁
  obtain rfl := hv hu.1.1 ht.1.1 hut
  exact ⟨_, ht.of_applies h₂ (h₁ _ hu.1.1 hu.1.2), rfl⟩

end Morphology.Exponence.Vocabulary
