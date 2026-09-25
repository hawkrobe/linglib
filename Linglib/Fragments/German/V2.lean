module

public import Linglib.Syntax.Clause.Basic

/-!
# German verb second

This file records where the finite verb of German moves to the left periphery, as a
distribution over sentence types and embedding contexts. German is verb second in root
declaratives, wh-questions and yes/no-questions, and in an embedded declarative without a
complementizer, *Sie sagte, sie würde kommen*, where the verb fills the position the
complementizer *dass* otherwise occupies; with the complementizer the clause is verb final, as
are embedded questions. The yes/no-question setting records verb fronting that surfaces as V1,
with an empty specifier. Exclamatives and imperatives are not verb second.

## References

* [westergaard-2009]
-/

@[expose] public section

namespace German

open Clause

/-- German has obligatory verb second in the three root clause types and in a
complementizer-less embedded declarative, and none elsewhere. -/
def verbSecond : Distribution
  | .declarative, .matrix => some .obligatory
  | .polar, .matrix => some .obligatory
  | .constituent, .matrix => some .obligatory
  | .exclamative, .matrix => some .excluded
  | .imperative, .matrix => some .excluded
  | .declarative, .quasiSubordinated => some .obligatory
  | .declarative, .subordinated => some .excluded
  | .polar, .subordinated => some .excluded
  | .constituent, .subordinated => some .excluded
  | _, _ => none

end German
