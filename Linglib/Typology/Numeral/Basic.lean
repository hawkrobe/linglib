import Linglib.Core.Order.Comparison

/-!
# Numeral — the lexical numeral object

Theory-neutral lexical core for numerals: the substrate a Fragment instantiates
and a semantics later interprets. A numeral word contributes a `Comparison`
(the relation it draws — bare / at-least / more-than / …) and a numeric
`argument`. The *measure* it compares against (cardinality, height, cost) is
supplied compositionally, so it is not a lexical field here.

The comparison vocabulary itself is **not** numeral-specific — it is the shared
degree-comparison primitive `Core.Order.Comparison` (also used by measure
phrases and gradable comparatives, per [kennedy-2015], [rett-2014]);
this file just records that a numeral *entry* carries one. The denotation (the
`Comparison.over`-based meaning, the Kennedy-vs-Horn bare-form choice) lives in
`Semantics/Numerals/`, which imports this object — the same object/denotation
split as `Syntax/Pronoun/Basic.lean` vs.
`Semantics/Reference/PronounDenotation.lean`.

## Main declarations

* `Numeral.Entry` — cross-linguistic lexical numeral entry (form, comparison,
  argument).
-/

namespace Numeral

open Core.Order (Comparison)
/-- Cross-linguistic lexical numeral entry: surface form, the `Comparison` it
    expresses, and its numeric argument. The measure compared against
    (cardinality, height, …) is compositional, supplied at denotation time
    rather than stored here. -/
structure Entry where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- The comparison the numeral expresses (bare or a modifier). -/
  comparison : Comparison
  /-- The numeric argument: the `m` in "more than `m`", "exactly `m`", … -/
  argument : Nat
  deriving Repr, DecidableEq

end Numeral
