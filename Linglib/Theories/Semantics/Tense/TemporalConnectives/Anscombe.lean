import Linglib.Theories.Semantics.Tense.TemporalConnectives.Basic

/-!
# Anscombe (1964) / Krifka (2010b): Under-specification Semantics
@cite{anscombe-1964} @cite{krifka-2010b}

Single lexical entry per connective. Both *before* and *after* are predicates
on time points; multiple readings arise from which point of B is relevant,
determined pragmatically by telicity.

- *before B* = λt. ∀t' ∈ B, t < t'   (all of B follows the reference time)
- *after B*  = λt. ∃t' ∈ B, t' < t   (some of B precedes the reference time)

The quantificational asymmetry (∀ in *before*, ∃ in *after*) is already present
here at Level 1 (point sets), though Anscombe did not highlight it as the source
of the veridicality contrast.

## Level

**Level 1 (point sets)**: operates on `timeTrace` projections of `SentDenotation`.

## References

- Anscombe, E. (1964). Before and after. *The Philosophical Review* 73, 3–24.
- Krifka, M. (2010b). *Before* and *after* without coercion. *NLLT* 28, 911–929.
-/

namespace Semantics.Tense.TemporalConnectives

open Core.Time

variable {Time : Type*} [LinearOrder Time]

-- ============================================================================
-- § Anscombe's Truth Conditions
-- ============================================================================

/-- Anscombe's *before B* as a predicate on times (Krifka 2010b, eq. 13a):
    λt. ∀t' ∈ times(B), t < t'. All times at which B holds follow t.

    "A before B" then holds when some time in A satisfies this predicate. -/
def Anscombe.before (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t < t'

/-- Anscombe's *after B* as a predicate on times (Krifka 2010b, eq. 13b):
    λt. ∃t' ∈ times(B), t' < t. Some time at which B holds precedes t.

    "A after B" then holds when some time in A satisfies this predicate. -/
def Anscombe.after (A B : SentDenotation Time) : Prop :=
  ∃ t ∈ timeTrace A, ∃ t' ∈ timeTrace B, t' < t

end Semantics.Tense.TemporalConnectives
