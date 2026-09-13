import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Focus-sensitive particles: even and only

This file defines the truth-conditional contribution of the focus particles *even* and
*only*, with propositions as `Set World`. A likelihood is a monotone map from propositions
into a partial order, so that a stronger proposition is at most as likely; the scalar
presupposition of *even* ([karttunen-peters-1979]) is that the prejacent is less likely than
every focus alternative, and the assertion of *only* ([rooth-1992]) that no focus alternative
holds.

## Main definitions

* `Focus.Particles.evenPresup`: the prejacent is less likely than every alternative under a
  likelihood.
* `Focus.Particles.onlyAssertion`: no focus alternative holds.

## Main results

* `Focus.Particles.not_evenPresup_of_subset`: under a monotone likelihood an alternative that
  entails the prejacent refutes the presupposition, the implicature clash from which
  [lahiri-1998] derives the distribution of *even one* items (cf. [crnic-2014]).
* `Focus.Particles.evenPresup_iff_ne`: when the prejacent entails every alternative, the
  presupposition asks only that no alternative be exactly as likely.

[francescotti-1995] weakens the universal force of the presupposition to a majority threshold,
in `Studies/Francescotti1995.lean`.

## References

* [karttunen-peters-1979]
* [rooth-1992]
* [lahiri-1998]
* [crnic-2014]
* [francescotti-1995]
-/

namespace Focus.Particles

variable {World α : Type*} [PartialOrder α] {μ : Set World → α} {p q : Set World}
  {alts : List (Set World)}

/-- The scalar presupposition of *even* ([karttunen-peters-1979]) under a likelihood `μ`: the
prejacent `p` is less likely than every focus alternative. -/
def evenPresup (μ : Set World → α) (p : Set World) (alts : List (Set World)) : Prop :=
  ∀ q ∈ alts, μ p < μ q

/-- The assertion of *only*: no focus alternative holds. The prejacent is presupposed
separately; the alternative list excludes it. -/
def onlyAssertion (alts : List (Set World)) : Set World :=
  {w | ∀ q ∈ alts, w ∉ q}

/-- Under a likelihood respecting entailment, an alternative that entails the prejacent is at
least as likely and so refutes the presupposition of *even*. -/
theorem not_evenPresup_of_subset (hμ : Monotone μ) (hq : q ∈ alts) (hqp : q ⊆ p) :
    ¬ evenPresup μ p alts :=
  λ h => lt_irrefl _ (lt_of_lt_of_le (h q hq) (hμ hqp))

/-- When the prejacent entails every alternative, the presupposition of *even* asks only that
no alternative be exactly as likely. -/
theorem evenPresup_iff_ne (hμ : Monotone μ) (h : ∀ q ∈ alts, p ⊆ q) :
    evenPresup μ p alts ↔ ∀ q ∈ alts, μ p ≠ μ q :=
  forall₂_congr λ q hq => lt_iff_le_and_ne.trans (and_iff_right (hμ (h q hq)))

end Focus.Particles
