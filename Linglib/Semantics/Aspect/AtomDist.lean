import Linglib.Core.Order.Interval

/-!
# Atomic distributivity

[champollion-2015] [zhao-2025]

`AtomDist` is the event-quantifier-level form of [zhao-2025]'s
ATOM-DIST_t (Def. 5.36, p. 165): an event quantifier `V` satisfies
ATOM-DIST with respect to a trace `τ` iff whenever it applies to an
event property fixing the trace as `i`, it also applies to the property
fixing the trace as any subinterval `i'` of `i`.

Per the strata-theory unification ([champollion-2017]), this is
the quantifier-level form of stratified reference at point-interval
granularity along the time dimension — a sibling of the Bennett-Partee
1972 strict subinterval property (`HasSubintervalProp` in
`Semantics/Aspect/SubintervalProperty.lean`). The
bridge `EvQuant.ofPred` below lifts an event predicate to an event
quantifier; the witness-universal and quantifier-restriction
formulations live at the same parameter-space point but differ in
quantification structure and are not directly interderivable without
explicit witness-existence assumptions.

The `antiAtomDistLicensed` predicate is the licensing condition for
Mandarin perfective particles in [zhao-2025] (le, méi-yǒu).
-/

namespace Semantics.Aspect


/-- An event quantifier: a predicate on event predicates.
    V(P) holds iff "there is an event satisfying P" according to V's
    quantificational force. The Champollion 2015 typed shape. -/
abbrev EvQuant (Event : Type*) := (Event → Prop) → Prop

/-- ATOM-DIST_α ([zhao-2025] Def. 5.36, p. 165): an event quantifier
    V satisfies ATOM-DIST with respect to trace function τ iff for every
    event predicate P and subinterval i' of τ(e), V also holds for the
    restriction of P to events whose trace is i'.

    Formally: V(P) → ∀ e, P(e) → ∀ i', subinterval(i', τ(e)) →
              V(λ e'. P(e') ∧ τ(e') = i')

    This captures the subinterval property parameterized over any
    linearly ordered dimension α (Zhao §5.5 extends to space; the
    cross-domain hypothesis is that the same definition applies to any
    `[LinearOrder α]`). -/
def AtomDist {Event : Type*} {α : Type*} [LinearOrder α]
    (τ : Event → NonemptyInterval α) (V : EvQuant Event) : Prop :=
  ∀ (P : Event → Prop), V P →
    ∀ (e : Event), P e →
      ∀ (i' : NonemptyInterval α), i' ≤ τ e →
        V (λ e' => P e' ∧ τ e' = i')

/-- NOT-ATOM-DIST_α licensing condition:
    A particle is licensed by an event quantifier V (w.r.t. trace τ) iff
    V does NOT satisfy ATOM-DIST_α. This is the presupposition of
    Mandarin le and méi-yǒu ([zhao-2025] eq. 5.42). -/
def antiAtomDistLicensed {Event : Type*} {α : Type*} [LinearOrder α]
    (τ : Event → NonemptyInterval α) (V : EvQuant Event) : Prop :=
  ¬ AtomDist τ V

namespace EvQuant

/-- Existential lift of an event predicate to an event quantifier:
    `λf. ∃e, P e ∧ f e`. The standard way (per [champollion-2015])
    to view a verb's predicate denotation as an event quantifier; used
    to bridge the predicate-level strata theory (`SR_univ` etc.) to the
    quantifier-level `AtomDist`. -/
def ofPred {Event : Type*} (P : Event → Prop) : EvQuant Event :=
  fun f => ∃ e, P e ∧ f e

@[simp] theorem ofPred_apply {Event : Type*} (P : Event → Prop)
    (f : Event → Prop) :
    ofPred P f ↔ ∃ e, P e ∧ f e := Iff.rfl

end EvQuant

end Semantics.Aspect
