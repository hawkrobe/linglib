import Linglib.Syntax.Minimalist.VerbSecond

/-!
# Norwegian verb second

This file records the verb-second grammars of Standard Norwegian and of the Nordmøre dialect,
the clause-type heads of the split ForceP that the finite verb moves to, as Westergaard's Table
3.1 gives them. Standard Norwegian moves the verb in declaratives, wh-questions and
yes/no-questions. Nordmøre Norwegian moves it in declaratives and yes/no-questions but not in
wh-questions, the mirror image of English on the declarative and wh-question heads.

## References

* [westergaard-2009]
-/

namespace Norwegian

open Minimalist

/-- Standard Norwegian moves the finite verb to Decl⁰, Int⁰ and Pol⁰. -/
abbrev stdNorwegian : V2Grammar := {.Decl, .Int, .Pol}

/-- Nordmøre Norwegian moves the finite verb to Decl⁰ and Pol⁰ but not to Int⁰. -/
abbrev nordmoreNorwegian : V2Grammar := {.Decl, .Pol}

end Norwegian
