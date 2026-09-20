import Linglib.Syntax.Minimalist.VerbSecond

/-!
# Danish verb second

This file records the verb-second grammar of Danish, the clause-type heads of the split ForceP
that the finite verb moves to, as Westergaard's Table 3.1 gives them: declaratives,
wh-questions and yes/no-questions as in Standard Norwegian, and exclamatives besides.

## References

* [westergaard-2009]
-/

namespace Danish

open Minimalist

/-- Danish moves the finite verb to Decl⁰, Int⁰, Pol⁰ and Excl⁰. -/
abbrev danish : V2Grammar := {.Decl, .Int, .Pol, .Excl}

end Danish
