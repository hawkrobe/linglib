import Linglib.Theories.Semantics.Tense.Aspect.Core

/-!
# The Subinterval Property

The subinterval property (Bennett & Partee 1972, Dowty 1979) is a fundamental
semantic property of event predicates that determines their aspectual class:

- **Statives and activities** have it: if John is sleeping for [1pm, 3pm],
  he is sleeping at every subinterval
- **Accomplishments and achievements** lack it: if John built a house in
  [Jan, Dec], he did not build a house in [Jan, Feb]

This property is central to the semantics of temporal adverbials
(@cite{rouillard-2026}), NPI licensing in boundary adverbials
(@cite{iatridou-zeijlstra-2021}), and the distribution of progressive
and imperfective aspect crosslinguistically.

Extracted from `MaximalInformativity.lean` because it is a general property
of event predicates, not specific to any particular analysis.
-/

namespace Semantics.Tense.Aspect.SubintervalProperty

open Core.Time
open Semantics.Tense.Aspect.Core

variable {W Time : Type*} [LinearOrder Time]

/-- **Subinterval property for event predicates** (mereological version).
    SUB(P) iff every subinterval of a P-event's runtime that is also
    the runtime of some event is the runtime of a P-event.
    States and activities have this property; accomplishments/achievements
    lack it. -/
def HasSubintervalProp (P : EventPred W Time) : Prop :=
  ∀ (e₁ : Eventuality Time) (w : W),
    P w e₁ →
    ∀ (t : Interval Time), t.subinterval e₁.τ →
    ∀ (e₂ : Eventuality Time), e₂.τ = t →
    P w e₂

/-- **Closed subinterval property** (CSUB).
    For any subinterval t of a P-event's runtime, there exists a P-event
    whose runtime is t. Stronger than SUB: guarantees witnesses exist,
    not just that predication is preserved. -/
def HasClosedSubintervalProp (P : EventPred W Time) : Prop :=
  ∀ (e₁ : Eventuality Time) (w : W),
    P w e₁ →
    ∀ (t : Interval Time), t.subinterval e₁.τ →
    ∃ (e₂ : Eventuality Time), e₂.τ = t ∧ P w e₂

end Semantics.Tense.Aspect.SubintervalProperty
