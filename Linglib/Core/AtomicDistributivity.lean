import Linglib.Core.Time

/-!
# Atomic Distributivity (ATOM-DIST)

Domain-parameterized subinterval property from Zhao (2026, Def. 5.3).
@cite{zhao-2026}

An event quantifier V satisfies ATOM-DIST_α iff V distributes over
subintervals of dimension α (via a trace function τ : Event → Interval α).

- **ATOM-DIST_t (temporal)**: States satisfy it; non-states don't.
- **ATOM-DIST_d (degree)**: Bare comparatives satisfy it; differential
  comparatives don't.

The licensing condition for Mandarin le/mei-you (Zhao Ch. 6) is
NOT-ATOM-DIST_α: these particles presuppose that the event quantifier
does NOT distribute over α-subintervals.

## References

- Zhao, Z. (2026). Cross-Linguistic and Cross-Domain Parallels in the
  Semantics of Degree and Time. MIT dissertation.
- Champollion, L. (2015). The interaction of compositional semantics and
  event semantics. *Linguistics and Philosophy* 38(1):31–66.
-/

namespace Core.AtomicDistributivity

open Core.Time

/-- An event quantifier (Champollion 2015): a predicate on event predicates.
    V(P) holds iff "there is an event satisfying P" according to V's
    quantificational force. -/
abbrev EvQuant (Event : Type*) := (Event → Prop) → Prop

/-- ATOM-DIST_α (Zhao 2026, Def. 5.3): an event quantifier V satisfies
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

/-- ATOM-DIST_t: temporal atomic distributivity.
    Abbreviation for ATOM-DIST with respect to a temporal trace. -/
abbrev AtomDist_t {Event : Type*} {Time : Type*} [LinearOrder Time]
    (τ_t : Event → Interval Time) (V : EvQuant Event) : Prop :=
  AtomDist τ_t V

/-- ATOM-DIST_d: degree atomic distributivity.
    Abbreviation for ATOM-DIST with respect to a degree trace. -/
abbrev AtomDist_d {Event : Type*} {Deg : Type*} [LinearOrder Deg]
    (τ_d : Event → Interval Deg) (V : EvQuant Event) : Prop :=
  AtomDist τ_d V

/-- NOT-ATOM-DIST_α licensing condition (Zhao 2026, Ch. 6):
    A particle is licensed by an event quantifier V (w.r.t. trace τ) iff
    V does NOT satisfy ATOM-DIST_α. This is the presupposition of
    Mandarin le and mei-you. -/
def antiAtomDistLicensed {Event : Type*} {α : Type*} [LinearOrder α]
    (τ : Event → Interval α) (V : EvQuant Event) : Prop :=
  ¬ AtomDist τ V

end Core.AtomicDistributivity
