import Linglib.Semantics.Verb.Denotation
import Linglib.Semantics.Aspect.Stratified

/-!
# Verb distributivity — a derived property of `Verb.denote`
[champollion-2017]

Whether a verb distributes over the atomic fillers of a thematic role is a
DERIVED property of its event denotation `Verb.denote`, not a carried
feature — the Verb-API analogue of telicity/Vendler being read off the
denotation rather than stored. `Verb.StratifiesOver` evaluates
[champollion-2017]'s stratified distributive reference (relational form,
`Aspect/Stratified.RelationalDistributiveReference`) on the verb's
`CosModel` denotation along an actual role relation.

This is the owner-relative home (P-OWNER in the Verb-API roadmap) for
distributivity: it supersedes the Bool distributivity tags and the former
see/kill/meet-hardcoding postulate class, which asked distributivity of
free-floating event predicates rather than of a verb's denotation.

## Main definitions

* `Verb.StratifiesOver` — the verb's `CosModel` denotation has relational
  distributive reference along role `R`, for every argument assignment
  (Champollion's "the verb stratifies over R").
-/

open Semantics.Aspect.Stratified

namespace Verb

variable {Entity State Time : Type*} [LinearOrder Time] [PartialOrder Entity]
  [SemilatticeSup (Event Time)]

/-- A verb **stratifies over** the atomic fillers of role `R`: for every
    argument assignment `(y, x)`, the verb's `CosModel` denotation has
    relational Stratified Distributive Reference along `R`
    ([champollion-2017]; `RelationalDistributiveReference`). A DERIVED
    property of `Verb.denote` — read off the denotation, not stored as a
    feature. The universal-over-arguments form matches Champollion's
    `DistributiveReferenceUniv R ⟦V⟧`, which quantifies over all events in
    the verb's denotation. -/
def StratifiesOver (v : Verb) (M : CosModel Entity State Time)
    (R : Entity → Event Time → Prop) : Prop :=
  ∀ y x, RelationalDistributiveReferenceUniv R (M.denote v y x)

theorem stratifiesOver_iff (v : Verb) (M : CosModel Entity State Time)
    (R : Entity → Event Time → Prop) :
    v.StratifiesOver M R ↔
      ∀ y x, RelationalDistributiveReferenceUniv R (M.denote v y x) :=
  Iff.rfl

end Verb
