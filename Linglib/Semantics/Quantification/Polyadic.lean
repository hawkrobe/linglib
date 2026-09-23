module

public import Linglib.Semantics.Quantification.Basic

/-!
# Polyadic quantifiers

This file defines three ways of building a quantifier over binary relations from generalized
quantifiers over sets. Iteration nests one quantifier in the scope of another, as in
*every student read some book*. Resumption lets a single quantifier bind both argument places,
so that it sees only the diagonal of the relation, as in *most students like themselves*.
Branching evaluates two quantifiers independently, neither in the scope of the other, as
Hintikka proposed for *some relative of each villager and some friend of each townsman hate
each other*. Peters and Westerståhl treat all three.

A sentence with two quantifiers has two linear scope readings, which are the two orders of
iteration.

## Main definitions

* `Quantifier.Polyadic.iterate`: the iteration `Q₁x Q₂y R(x, y)` of two quantifiers.
* `Quantifier.Polyadic.resume`: the resumption `Qx R(x, x)` of a quantifier.
* `Quantifier.Polyadic.branch`: the branching of two quantifiers, witnessed by choice functions.
* `Quantifier.Polyadic.surfaceScope`, `Quantifier.Polyadic.inverseScope`: the two linear scope
  readings of a two-quantifier sentence.

## Main results

* `Quantifier.Polyadic.iterate_every_some_of_some_every`: `∃∀` entails `∀∃`, so the two linear
  readings of an *every*/*some* pair are nested.
* `Quantifier.Polyadic.iterate_mono`, `Quantifier.Polyadic.resume_mono`: iteration and resumption
  of scope-upward-monotone quantifiers are monotone in the relation.

## TODO

`branch` states branching with a pair of choice functions. Barwise's formulation for
upward-monotone quantifiers instead asks for sets `X ⊆ A` and `Y ⊆ B` with `Q₁ A X`, `Q₂ B Y`
and `X × Y ⊆ R`; the two should be compared against the sources.

## References

* [peters-westerstahl-2006]
* [hintikka-1996]
-/

@[expose] public section

namespace Quantifier.Polyadic

open Quantifier Quantifier.GQ

variable {α : Type*} {Q Q₁ Q₂ : GQ α} {A B : α → Prop} {R R' : α → α → Prop}

/-! ### Iteration, resumption and branching -/

/-- The iteration `Q₁x Q₂y R(x, y)` nests `Q₂` in the scope of `Q₁`, so that *every student
read some book* is `iterate every student some book read`. -/
def iterate (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  Q₁ A fun x ↦ Q₂ B fun y ↦ R x y

/-- The resumption `Qx R(x, x)` binds both argument places of `R` with one quantifier, so that
*most students like themselves* is `resume most student like`. -/
def resume (Q : GQ α) (A : α → Prop) (R : α → α → Prop) : Prop :=
  Q A fun x ↦ R x x

/-- The branching of `Q₁` and `Q₂` evaluates them independently, neither in the scope of the
other. There are choice functions `f` and `g` such that `Q₁` holds of the `x` related to their
`B`-witness `f x`, and `Q₂` of the `y` related to their `A`-witness `g y`. -/
def branch (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  ∃ f g : α → α,
    Q₁ A (fun x ↦ B (f x) ∧ R x (f x)) ∧
    Q₂ B (fun y ↦ A (g y) ∧ R (g y) y)

/-! ### Scope order -/

/-- The surface-scope reading of a two-quantifier sentence, on which the first quantifier
outscopes the second. -/
def surfaceScope (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  iterate Q₁ Q₂ A B R

/-- The inverse-scope reading of a two-quantifier sentence, on which the second quantifier
outscopes the first. -/
def inverseScope (Q₁ Q₂ : GQ α) (A B : α → Prop) (R : α → α → Prop) : Prop :=
  iterate Q₂ Q₁ B A fun y x ↦ R x y

/-- An existential scoping over a universal entails the universal scoping over the existential,
so the two linear readings of an *every*/*some* pair are nested. -/
theorem iterate_every_some_of_some_every (A B : α → Prop) (R : α → α → Prop)
    (h : iterate some_sem every_sem A B R) : iterate every_sem some_sem B A (flip R) :=
  let ⟨x, hx, hall⟩ := h; fun y hy ↦ ⟨x, hx, hall y hy⟩

/-! ### Monotonicity -/

/-- The iteration of two scope-upward-monotone quantifiers is monotone in the relation. -/
theorem iterate_mono (h₁ : ScopeUpwardMono Q₁) (h₂ : ScopeUpwardMono Q₂)
    (hR : ∀ x y, R x y → R' x y) : iterate Q₁ Q₂ A B R → iterate Q₁ Q₂ A B R' :=
  h₁ A _ _ fun x ↦ h₂ B _ _ (hR x)

/-- The resumption of a scope-upward-monotone quantifier is monotone in the diagonal of the
relation. -/
theorem resume_mono (h : ScopeUpwardMono Q) (hR : ∀ x, R x x → R' x x) :
    resume Q A R → resume Q A R' :=
  h A _ _ hR

end Quantifier.Polyadic
