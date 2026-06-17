import Mathlib.Order.Basic

/-!
# Grammatical tense: the temporal relation

`GramTense` is the four-way grammatical-tense label (past/present/future/nonpast), and
`GramTense.constrains` is the ordering it imposes on a reference time relative to a perspective time,
grounded directly in the mathlib order on `T`. The order-requiring frame predicates
(`ReichenbachFrame.isPast`/`isFuture`/`isNonpast`) and the compositional tense operators are views of
`constrains`; `isPresent` is the order-free equality (definitionally `constrains .present`, but kept
bare so present-only theorems need no `LinearOrder`).

[klecha-2016] (the `nonpast` case) [kiparsky-2002]
-/

namespace Tense

/--
Grammatical tense: a temporal relation imposed by tense morphology.

Following the Reichenbach/Klein tradition:
- PAST: reference time before perspective time
- PRESENT: reference time overlaps perspective time
- FUTURE: reference time after perspective time
-/
inductive GramTense where
  | past
  | present
  | future
  /-- [klecha-2016]'s non-past tense: perspective ≤ ref (present or future).
      Distinct from `.present` (ref = perspective). The non-past is what allows
      embedded tense under circumstantial modals to have future-oriented readings:
      ⟦NPST⟧ = λp λt λu λh[p(t)(h) & u ≤ t], i.e., ref ≥ perspective. -/
  | nonpast
  deriving DecidableEq, Repr, Inhabited

namespace GramTense

/-- The temporal constraint imposed by a grammatical tense, grounded directly in the mathlib order
    on `T`. Past: ref < perspective. Present: ref = perspective. Future: ref > perspective.
    Nonpast: ref ≥ perspective (the present-or-future union, [klecha-2016]).
    This is the core ordering that Priorean operators assert and Abusch's tense pronouns presuppose. -/
def constrains {T : Type*} [LinearOrder T]
    (t : GramTense) (refTime perspTime : T) : Prop :=
  match t with
  | .past => refTime < perspTime
  | .present => refTime = perspTime
  | .future => refTime > perspTime
  | .nonpast => refTime ≥ perspTime

instance {T : Type*} [LinearOrder T] (t : GramTense) (r p : T) :
    Decidable (t.constrains r p) :=
  match t with
  | .past => inferInstanceAs (Decidable (r < p))
  | .present => inferInstanceAs (Decidable (r = p))
  | .future => inferInstanceAs (Decidable (r > p))
  | .nonpast => inferInstanceAs (Decidable (r ≥ p))

end GramTense

end Tense
