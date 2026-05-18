import Linglib.Theories.Semantics.TypeTheoretic.Core

/-!
# Pustejovsky (1995): Complement Coercion via Telic Quale
@cite{pustejovsky-1995}

The Generative Lexicon analysis of *complement coercion*: type-mismatch
at composition triggers a shift mediated by the noun's telic quale,
yielding event-typed readings of event-selecting verbs applied to
entity-typed complements ("Mary began the novel" → began *reading*
the novel; "John enjoyed the book" → enjoyed *reading* the book).

## Main definitions

* `ComplementCoercion A B`: meaning-changing type shift `A → B`,
  structurally parallel to `SubtypeOf` but semantically distinct.
* `coerceApply`: compose a `Ppty B` against an `A` via the coercion.
* `coerceApply_is_shift` vs `restrict_is_subsumption`: the structural
  distinction between meaning-changing coercion and identity-preserving
  subsumption.

## References

* @cite{pustejovsky-1995} ch. 4–5 (qualia structure, complement
  coercion via telic quale).
-/

namespace Pustejovsky1995

open Semantics.TypeTheoretic (Ppty IsTrue SubtypeOf)

/-- Complement coercion: a meaning-changing type shift triggered by
    type mismatch at composition. Distinct from `SubtypeOf`: the
    `coerce` function produces a new entity in the target type rather
    than a view of the original. -/
class ComplementCoercion (A B : Type) where
  coerce : A → B

/-- Compose a target-typed property against a source-typed argument
    via the coercion. Structurally parallel to subsumptive `restrict`
    (apply `P` after coercing) but the coercion changes meaning. -/
def coerceApply {A B : Type} [ComplementCoercion A B] (P : Ppty B) : Ppty A :=
  fun a => P (ComplementCoercion.coerce a)

/-- Restrict via subsumptive `SubtypeOf` (identity-preserving), for
    comparison with `coerceApply` below. -/
private def restrict {A B : Type} [h : SubtypeOf A B] (P : Ppty B) : Ppty A :=
  fun a => P (h.up a)

/-- `restrict` is subsumption: the value `a : A` becomes its image
    `h.up a : B`; identity preserved. -/
theorem restrict_is_subsumption {A B : Type} [h : SubtypeOf A B]
    (P : Ppty B) (a : A) : restrict P a = P (h.up a) := rfl

/-- `coerceApply` is a meaning-changing type shift: the value `a : A`
    is mapped to a *different* entity `h.coerce a : B` (not a view of
    the same entity). -/
theorem coerceApply_is_shift {A B : Type} [h : ComplementCoercion A B]
    (P : Ppty B) (a : A) : coerceApply P a = P (h.coerce a) := rfl

/-! ### Telic-quale instance: book → reading event -/

/-- Minimal physical-object type for the demonstration. -/
inductive Book where
  | hamlet
  | mobyDick
  deriving DecidableEq, Repr

/-- Minimal event type: reading a book. (Pustejovsky's telic quale
    for `book` is the reading-event.) -/
inductive ReadingEvent where
  | read : Book → ReadingEvent
  deriving DecidableEq, Repr

/-- Telic-quale coercion: `Book` coerces to `ReadingEvent` via the
    typical-use mapping. -/
instance : ComplementCoercion Book ReadingEvent where
  coerce := .read

/-- "enjoy" selects for event-typed complements. -/
def enjoy : Ppty ReadingEvent
  | .read _ => Unit

/-- "John enjoyed Hamlet" composes via complement coercion: the book
    `hamlet` coerces to `ReadingEvent.read hamlet`, and `enjoy` applies
    to the resulting event. -/
theorem enjoy_hamlet : IsTrue ((coerceApply enjoy : Ppty Book) .hamlet) := ⟨()⟩

theorem enjoy_mobyDick : IsTrue ((coerceApply enjoy : Ppty Book) .mobyDick) := ⟨()⟩

end Pustejovsky1995
