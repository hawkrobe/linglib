import Linglib.Semantics.Mereology.Relation

/-!
# Incrementality

This file defines [krifka-1998]'s incremental relations between objects and events. A
relation is strictly incremental when each part of a related object corresponds to exactly
one part of the event and conversely, and some related pair has proper parts: the object of
*eat* or *draw*, whose parts are consumed or created one after another. It is incremental
when it is the closure under sums of a strictly incremental relation, which admits the
backups of *read the article*. Verbs are classified by which of these their theme relation
satisfies.

## Main definitions

* `SINC` — strict incrementality: uniqueness of events and of objects, on a relation with an
  extended pair. The paper also lists mapping to subevents and to subobjects, which follow
  (`SINC.mse`, `SINC.mso`).
* `INC` — incrementality: the closure of a strictly incremental relation under sums,
  `AlgClosure` of its graph.
* `VerbIncClass` — the classification of verbs by the incrementality of their theme.

## Main results

* `SINC.inc_of_sum` — a summative strictly incremental relation is incremental, being its own
  closure.

## References

* [krifka-1998]
-/

namespace Aspect

open Mereology

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- Strict incrementality: a part of a related object is related to exactly one part of the
event and conversely, and some related pair has related proper parts, so the relation is not
confined to atoms. -/
structure SINC (θ : α → β → Prop) : Prop where
  ue : UE θ
  uo : UO θ
  /-- Some related pair has related proper parts. -/
  extended : ∃ (x y : α) (e e' : β), y < x ∧ e' < e ∧ θ x e ∧ θ y e'

variable {θ : α → β → Prop}

theorem SINC.mse (h : SINC θ) : MSE θ := h.ue.mse_of_uo h.uo

theorem SINC.mso (h : SINC θ) : MSO θ := h.uo.mso_of_ue h.ue

theorem SINC.me (h : SINC θ) : ME θ := h.ue.me

theorem SINC.mo (h : SINC θ) : MO θ := h.uo.mo

/-- Incrementality: the closure of some strictly incremental relation under sums. -/
def INC (θ : α → β → Prop) : Prop :=
  ∃ θ', SINC θ' ∧ ∀ x e, θ x e ↔ AlgClosure (Function.uncurry θ') (x, e)

/-- A summative strictly incremental relation is incremental: it is its own closure. -/
theorem SINC.inc_of_sum (h : SINC θ) (hs : SUM θ) : INC θ :=
  ⟨θ, h, λ x e => (algClosure_of_cum (x := (x, e)) (sum_iff_cum_uncurry.1 hs)).symm⟩

/-- The incrementality of a verb's theme relation: strictly incremental (*eat*, *draw*),
incremental (*read*), or summative without incrementality (*push*, *carry*). -/
inductive VerbIncClass where
  | sinc
  | inc
  | cumOnly
  deriving DecidableEq, Repr

end Aspect
