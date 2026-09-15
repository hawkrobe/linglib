import Linglib.Semantics.Aspect.Incremental

/-!
# Cumulativity and quantization of verb phrases

This file defines the verb phrase of a thematic relation and an object predicate by
existential closure over the object, and proves [krifka-1998]'s transfer of reference
properties from the object to the verb phrase: cumulativity transfers along a summative
relation, so *eat apples* is cumulative, and quantization transfers along a relation with
uniqueness of participants and mapping to subobjects, so *eat two apples* is quantized.

## Main definitions

* `VP` — the verb phrase of a relation and an object predicate.

## Main results

* `vp_cum` — a summative relation carries cumulativity from the object to the verb phrase.
* `vp_qua` — uniqueness of participants and mapping to subobjects carry quantization.

## References

* [krifka-1989], [krifka-1998]
-/

namespace Aspect

open Mereology

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- The verb phrase of a relation and an object predicate: the events with some object of the
predicate. -/
def VP (θ : α → β → Prop) (OBJ : α → Prop) : β → Prop := λ e => ∃ y, OBJ y ∧ θ y e

variable {θ : α → β → Prop} {OBJ : α → Prop}

/-- A summative relation carries cumulativity from the object to the verb phrase. -/
theorem vp_cum (hθ : SUM θ) (hObj : CUM OBJ) : CUM (VP θ OBJ) :=
  λ _ ⟨_, h₁, hθ₁⟩ _ ⟨_, h₂, hθ₂⟩ => ⟨_, hObj h₁ h₂, hθ hθ₁ hθ₂⟩

/-- Uniqueness of participants and mapping to subobjects carry quantization from the object
to the verb phrase: the object of a proper subevent is a proper part of the object. -/
theorem vp_qua (hU : UP θ) (hm : MSO θ) (hObj : QUA OBJ) : QUA (VP θ OBJ) :=
  qua_of_forall λ _ _ ⟨_, hy, hθ⟩ hlt ⟨_, hz, hθz⟩ =>
    let ⟨_, hlt', hθ'⟩ := hm hθ hlt
    hObj (hU hθz hθ' ▸ hz) hy hlt'.ne hlt'.le

end Aspect
