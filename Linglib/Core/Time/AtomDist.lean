import Linglib.Core.Time.Interval.Basic

/-!
# Atomic distributivity

@cite{champollion-2015} @cite{zhao-2025}

`AtomDist` is the subinterval property generalized to arbitrary linearly
ordered dimensions: an event quantifier `V` satisfies ATOM-DIST with
respect to a trace `τ` iff `V P → ∀ e, P e → ∀ i' ⊆ τ(e), V (P restricted
to events with trace = i')`.

The `antiAtomDistLicensed` predicate is the licensing condition for
Mandarin perfective particles in @cite{zhao-2025}.
-/

namespace Core.Time

/-- An event quantifier: a predicate on event predicates.
    V(P) holds iff "there is an event satisfying P" according to V's
    quantificational force. -/
abbrev EvQuant (Event : Type*) := (Event → Prop) → Prop

/-- ATOM-DIST_α (@cite{zhao-2025}, Def. 5.3): an event quantifier V satisfies
    ATOM-DIST with respect to trace function τ iff for every event predicate P
    and subinterval i' of τ(e), V also holds for the restriction of P to
    events whose trace is i'.

    Formally: V(P) → ∀ e, P(e) → ∀ i', subinterval(i', τ(e)) →
              V(λ e'. P(e') ∧ τ(e') = i')

    This captures the subinterval property parameterized over any
    linearly ordered dimension α. -/
def AtomDist {Event : Type*} {α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) : Prop :=
  ∀ (P : Event → Prop), V P →
    ∀ (e : Event), P e →
      ∀ (i' : Interval α), i'.subinterval (τ e) →
        V (λ e' => P e' ∧ τ e' = i')

/-- NOT-ATOM-DIST_α licensing condition:
    A particle is licensed by an event quantifier V (w.r.t. trace τ) iff
    V does NOT satisfy ATOM-DIST_α. This is the presupposition of
    Mandarin le and mei-you. -/
def antiAtomDistLicensed {Event : Type*} {α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) : Prop :=
  ¬ AtomDist τ V

end Core.Time
