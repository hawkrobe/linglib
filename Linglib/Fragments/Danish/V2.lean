module

public import Linglib.Syntax.Minimalist.VerbSecond

/-!
# Danish verb second

This file records the verb-second grammar of Danish, the clause-type heads of Westergaard's
split ForceP that the finite verb moves to, as her Table 3.1 gives them: declaratives,
wh-questions and yes/no-questions as in Standard Norwegian, and exclamatives besides, *Hvor er
han sød!*, though Westergaard notes that only certain types of Danish exclamative are verb
second.

## References

* [westergaard-2009]
-/

@[expose] public section

namespace Danish

open Minimalist

/-- Danish moves the finite verb to Decl⁰, Int⁰, Pol⁰ and Excl⁰. -/
abbrev verbSecond : V2Grammar := {.Decl, .Int, .Pol, .Excl}

end Danish
