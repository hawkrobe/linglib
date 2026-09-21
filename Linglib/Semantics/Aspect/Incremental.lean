import Linglib.Semantics.Aspect.Defs
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
* `Incrementality.Holds` — the property an incrementality class of `Aspect/Defs.lean` names.

## Main results

* `SINC.inc_of_sum` — a summative strictly incremental relation is incremental, being its own
  closure.
* `INC.sum` — an incremental relation is summative.

## References

* [krifka-1998]
-/

namespace Aspect

open Mereology

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- A relation is strictly incremental when a part of a related object is related to exactly one
part of the event and conversely, and some related pair has related proper parts, so the
relation is not confined to atoms. -/
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

/-- A relation is incremental when it is the closure of some strictly incremental relation under
sums. -/
def INC (θ : α → β → Prop) : Prop :=
  ∃ θ', SINC θ' ∧ ∀ x e, θ x e ↔ AlgClosure (Function.uncurry θ') (x, e)

/-- A summative strictly incremental relation is incremental, being its own closure. -/
theorem SINC.inc_of_sum (h : SINC θ) (hs : SUM θ) : INC θ :=
  ⟨θ, h, fun x e ↦ (algClosure_of_cum (x := (x, e)) (sum_iff_cum_uncurry.1 hs)).symm⟩

/-- An incremental relation is summative, being a closure under sums. -/
theorem INC.sum (h : INC θ) : SUM θ := by
  obtain ⟨θ', -, hθ⟩ := h
  have : Function.uncurry θ = AlgClosure (Function.uncurry θ') :=
    funext fun ⟨x, e⟩ ↦ propext (hθ x e)
  exact sum_iff_cum_uncurry.2 (this ▸ algClosure_cum)

/-- The property of a thematic relation that an incrementality class names. A verb is classed
by the strongest that its theme relation has. -/
def Incrementality.Holds : Incrementality → (α → β → Prop) → Prop
  | .strict, θ => SINC θ
  | .incremental, θ => INC θ
  | .cumulative, θ => SUM θ

/-- The incremental class is included in the cumulative one. -/
theorem Incrementality.Holds.cumulative (h : Incrementality.incremental.Holds θ) :
    Incrementality.cumulative.Holds θ :=
  INC.sum h

/-- A summative relation of the strict class is of the incremental class. -/
theorem Incrementality.Holds.incremental (h : Incrementality.strict.Holds θ) (hs : SUM θ) :
    Incrementality.incremental.Holds θ :=
  SINC.inc_of_sum h hs

end Aspect
