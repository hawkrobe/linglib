import Mathlib.Order.Lattice

/-!
# Precedence-Conditional Closure

A shared substrate for the closure-under-componentwise-sum construction
that appears in two places in linglib's K98 formalization. The
construction takes a relation `θ' : α → β → Prop` and closes it under
`(x₁, e₁), (x₂, e₂) ↦ (x₁ ⊔ x₂, e₁ ⊔ e₂)`, optionally subject to an
inter-event constraint `cond : β → β → Prop`. Two specializations:

* **Unconditional** (`cond = fun _ _ ↦ True`): @cite{krifka-1998} §3.6
  eq. 59 incremental-theme closure (`IncClosure` in
  `Events/Aspect/Incremental.lean`). Permits arbitrary sum formation —
  models *read the article* (re-reading allowed).
* **Precedence-respecting** (`cond := precedes`): @cite{krifka-1998}
  §4.3 eq. 71 movement-relation closure (`MovementClosure` in
  `Studies/Krifka1998.lean` Part II). Only events in precedence order
  combine — prevents telekinetic concatenations.

## Main definitions

* `PrecedenceClosure` — the inductive `base | sum` closure family
* `PrecedenceClosure.closure_subset` — abstract `θ' ⊆ θ` + closure-under-sum
  ⇒ `PrecedenceClosure cond θ' ⊆ θ`. Consumed by both `inc_of_sinc`
  and `mr_of_smr` to discharge the `θ x e ↔ closure x e` reverse direction.

## References

* @cite{krifka-1998} §3.6 eq. 59 (incremental-theme closure)
* @cite{krifka-1998} §4.3 eq. 71 (movement-relation closure, modulo TANG_H)
-/

namespace Semantics.Aspect

/-- Smallest `α → β → Prop` relation containing `θ'` and closed under
    componentwise sum, when the summed events satisfy `cond`. Taking
    `cond := fun _ _ ↦ True` gives unconditional sum-closure (K98
    eq. 59); taking `cond := precedes` gives precedence-respecting
    sum-closure (K98 eq. 71). -/
inductive PrecedenceClosure {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]
    (cond : β → β → Prop) (θ' : α → β → Prop) : α → β → Prop where
  | base {x : α} {e : β} : θ' x e → PrecedenceClosure cond θ' x e
  | sum {x₁ x₂ : α} {e₁ e₂ : β} :
      PrecedenceClosure cond θ' x₁ e₁ →
      PrecedenceClosure cond θ' x₂ e₂ →
      cond e₁ e₂ →
      PrecedenceClosure cond θ' (x₁ ⊔ x₂) (e₁ ⊔ e₂)

/-- If `θ` contains `θ'` and is closed under sums whose events satisfy
    `cond`, then `PrecedenceClosure cond θ' x e → θ x e`. The `cond`
    premise is what differs between the two consumer call sites:
    `inc_of_sinc` instantiates with `cond = fun _ _ ↦ True` (so `hCond`
    is trivial); `mr_of_smr` propagates the precedence as the third
    argument of `hClosed`. -/
theorem PrecedenceClosure.closure_subset {α β : Type*}
    [SemilatticeSup α] [SemilatticeSup β]
    {cond : β → β → Prop} {θ' θ : α → β → Prop}
    (hBase   : ∀ x e, θ' x e → θ x e)
    (hClosed : ∀ x₁ x₂ e₁ e₂, θ x₁ e₁ → θ x₂ e₂ → cond e₁ e₂ →
               θ (x₁ ⊔ x₂) (e₁ ⊔ e₂))
    {x : α} {e : β} (hcl : PrecedenceClosure cond θ' x e) : θ x e := by
  induction hcl with
  | base h => exact hBase _ _ h
  | sum _ _ hC ih₁ ih₂ => exact hClosed _ _ _ _ ih₁ ih₂ hC

end Semantics.Aspect
