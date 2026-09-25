module

public import Linglib.Syntax.Clause.Basic

/-!
# Danish verb second

This file records where the finite verb of Danish moves to the left periphery, as a
distribution over sentence types and embedding contexts. Danish is verb second in root
declaratives, wh-questions and yes/no-questions as Standard Norwegian is, and in some types of
exclamative, *Hvor er han sød!*, though not all, as Westergaard notes; imperatives are not verb
second.

## References

* [westergaard-2009]
-/

@[expose] public section

namespace Danish

open Clause

/-- Danish has obligatory verb second in the three root clause types, verb second in some
exclamatives, and none in imperatives. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .exclamative, .matrix => some .optional
  | .imperative, .matrix => some .excluded
  | _, _ => none

end Danish
