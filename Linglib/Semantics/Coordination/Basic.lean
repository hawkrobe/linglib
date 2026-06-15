import Linglib.Features.Coordination
import Linglib.Core.Logic.Intensional.Algebra

/-!
# The Coordinator API — the operation

`and`/`or`/`but`/`nor` denote the meet/join/complement of the Boolean algebra on
whatever conjoinable carrier the conjuncts inhabit. `Coordinator.op` is the single
operation, polymorphic over `[BooleanAlgebra α]` — one def, every Boolean carrier
(`Denot E W τ`, `Prop`, `Set E`, propositions, GQs). The [partee-rooth-1983]
`genConj`/`genDisj` recursion is proven to *be* it.

This file sits *below* the composition engine: the engine mode `tryCoord`
(`Semantics/Composition/Coordination.lean`), the CCG `.coord` rule, and the lexical
fragments all consume `Coordinator.op` from here. The naming target is
`Coordinator.Role` (the `Coord` prefix on `CoordRole` is absorbed at the marking
migration); for now `Role` aliases `Features.Coordination.CoordRole`.

## Main definitions

* `Coordinator.op` — the DO layer (role → Boolean operation), polymorphic.
* `Coordinator.engineOp` — the runtime-`Ty`-dispatch form (via `genConj`/`genDisj`/`genNeg`).
* `Features.Coordination.CoordEntry.op` — a lexical coordinator's operation = `op` of its role.

## Main results

* `genConj_eq_op_et`, `genDisj_eq_op_et`, `op_*_t` — the recursion / wrappers ARE `op`
  (flow-through bucket (a)).
-/

namespace Coordinator

open Core.Logic.Intensional
open Core.Logic.Intensional.Conjunction

/-- The role of a coordinator — which Boolean operation it denotes.
    Aliases `Features.Coordination.CoordRole` pending the marking migration. -/
abbrev Role := Features.Coordination.CoordRole

/-- **DO layer — the *at-issue* truth-conditional operation** a coordinator denotes,
    polymorphic over any Boolean-algebra carrier: the role selects the *method*
    (`⊓`/`⊔`/`·ᶜ∘⊔`), the instance supplies the *algebra*.

    **Faithfulness scope.** Faithful for `and` (`.j`), `or` (`.disj`), and `nor`
    (`.negDisj`/`.negCoord`). The additive `.mu` and adversative `.advers` give only the
    at-issue *meet* `⊓` (`op_mu_eq_j`, `op_advers_eq_j`): their extra content is NOT
    captured here and *diverges* —
    * `.mu` (M&S additive/focus particle) → `Studies/MitrovicSauerland2016`;
    * `.advers` (`but`) → the adversative *contrast* is a discourse relation, and `but`
      is non-commutative at that level, which the commutative `⊓` structurally cannot
      represent — it lives in the Contrast/discourse layer, not in `op`. -/
def op {α : Type*} [BooleanAlgebra α] : Role → α → α → α
  | .j | .mu | .advers => (· ⊓ ·)
  | .disj => (· ⊔ ·)
  | .negDisj | .negCoord => fun p q => (p ⊔ q)ᶜ

/-! ### Bridges: the [partee-rooth-1983] recursion / IL wrappers ARE `op` (bucket (a)) -/

theorem genConj_eq_op_et {E W : Type} (f g : Denot E W (.e ⇒ .t)) :
    genConj (.e ⇒ .t) E W f g = op .j f g := rfl

theorem genDisj_eq_op_et {E W : Type} (f g : Denot E W (.e ⇒ .t)) :
    genDisj (.e ⇒ .t) E W f g = op .disj f g := rfl

theorem op_j_t {E W : Type} (p q : Denot E W .t) : op .j p q = (p ⊓ q) := rfl
theorem op_disj_t {E W : Type} (p q : Denot E W .t) : op .disj p q = (p ⊔ q) := rfl
theorem op_nor_t {E W : Type} (p q : Denot E W .t) : op .negDisj p q = (p ⊔ q)ᶜ := rfl

/-! ### Faithfulness: `op` collapses additive/adversative onto `and` (visible divergence)

`op` is the at-issue truth-conditional core. `mu` (additive) and `but` (adversative)
collapse onto `and`'s meet here; the lemmas below make that collapse *explicit and
proven* rather than silent. The additional content (M&S additive/focus; adversative
contrast, including `but`'s discourse-level non-commutativity) is not in `op` — it
diverges to the M&S study / the Contrast layer. -/

/-- Additive `.mu` has the same at-issue denotation as `and`; its M&S additive/focus
    dimension diverges (see `Studies/MitrovicSauerland2016`). -/
theorem op_mu_eq_j {α : Type*} [BooleanAlgebra α] : (op .mu : α → α → α) = op .j := rfl

/-- Adversative `.advers` (`but`) has the same at-issue denotation as `and`; its contrast
    is a discourse relation outside `op` (and `but` is non-commutative at that level,
    which the commutative `⊓` cannot represent). -/
theorem op_advers_eq_j {α : Type*} [BooleanAlgebra α] : (op .advers : α → α → α) = op .j := rfl

/-- Engine-side operation: runtime dispatch on the type `τ` via the recursion forms,
    which the bridges above prove equal to `op` at every conjoinable type. The engine
    needs runtime `Ty` dispatch where `op` would need a statically-resolved instance. -/
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

namespace Features.Coordination

/-- **A lexical coordinator's operation** = `Coordinator.op` of its role. The 19 Fragment
    coordinators (English *and*/*or*, German *und*/*oder*, Japanese *to*/*mo*/*ka*, …)
    route their denotation through the single `Coordinator.op` here (flow-through
    bucket (b): the marking derives its operation from `op`). -/
def CoordEntry.op {α : Type*} [BooleanAlgebra α] (e : CoordEntry) : α → α → α :=
  Coordinator.op e.role

end Features.Coordination
