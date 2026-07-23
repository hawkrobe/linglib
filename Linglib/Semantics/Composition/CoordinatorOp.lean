import Linglib.Syntax.Category.Coordinator
import Linglib.Semantics.Intensional.Algebra

/-!
# The Coordinator operation on `Denot` carriers

The carrier-agnostic `Coordinator.op` (in `Defs`) specialised to the intensional-logic
`Denot` carriers: `and`/`or`/`but`/`nor` denote the meet/join/complement of the Boolean
algebra on whatever conjoinable type the conjuncts inhabit, and the [partee-rooth-1983]
`genConj`/`genDisj` recursion is proven to *be* it. This file sits below the composition
engine (the `tryCoord` mode, the CCG `.coord` rule), supplying the runtime-`Ty`-dispatch
form `engineOp` it consumes.

## Main definitions

* `Coordinator.engineOp` — the runtime-`Ty`-dispatch form (via `genConj`/`genDisj`/`genNeg`).

## Main results

* `genConj_eq_op_et`, `genDisj_eq_op_et`, `op_*_t` — the [partee-rooth-1983] recursion ARE
  `Coordinator.op` at the `Denot` carriers (flow-through bucket (a)).
-/

namespace Coordinator

open Intensional
open Intensional.Conjunction

/-! ### Bridges: the [partee-rooth-1983] recursion ARE `op` (bucket (a)) -/

theorem genConj_eq_op_et {E W : Type} (f g : Denot E W (.e ⇒ .t)) :
    genConj (.e ⇒ .t) E W f g = op .j f g := rfl

theorem genDisj_eq_op_et {E W : Type} (f g : Denot E W (.e ⇒ .t)) :
    genDisj (.e ⇒ .t) E W f g = op .disj f g := rfl

theorem op_j_t {E W : Type} (p q : Denot E W .t) : op .j p q = (p ⊓ q) := rfl
theorem op_disj_t {E W : Type} (p q : Denot E W .t) : op .disj p q = (p ⊔ q) := rfl
theorem op_nor_t {E W : Type} (p q : Denot E W .t) : op .negDisj p q = (p ⊔ q)ᶜ := rfl

/-- Engine-side operation: runtime dispatch on the type `τ` via the recursion forms, which
    the bridges above prove equal to `op` at every conjoinable type. The engine needs runtime
    `Ty` dispatch where `op` would need a statically-resolved instance. -/
def engineOp : Role → (τ : Ty) → (E W : Type) → Denot E W τ → Denot E W τ → Denot E W τ
  | .j, τ, E, W => genConj τ E W
  | .mu, τ, E, W => genConj τ E W
  | .advers, τ, E, W => genConj τ E W
  | .disj, τ, E, W => genDisj τ E W
  | .negDisj, τ, E, W => fun p q => genNeg τ E W (genDisj τ E W p q)
  | .negCoord, τ, E, W => fun p q => genNeg τ E W (genDisj τ E W p q)

theorem engineOp_j (τ : Ty) (E W : Type) : engineOp .j τ E W = genConj τ E W := rfl
theorem engineOp_disj (τ : Ty) (E W : Type) : engineOp .disj τ E W = genDisj τ E W := rfl

end Coordinator
