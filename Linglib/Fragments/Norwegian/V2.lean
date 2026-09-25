module

public import Linglib.Syntax.Minimalist.VerbSecond

/-!
# Norwegian verb second

This file records the verb-second grammars of Standard Norwegian and of the Nordmøre dialect,
the clause-type heads of Westergaard's split ForceP that the finite verb moves to, as her Table
3.1 gives them. Standard Norwegian is verb second in declarative main clauses, where one
constituent precedes the finite verb, in yes/no-questions, which begin with the finite verb, and
in wh-questions, where the wh-phrase fills the forefield and the finite verb follows; these are
the three main-clause schemas of Faarlund, Lie and Vannebo's reference grammar. Nordmøre
Norwegian is strictly verb second in declaratives but allows the verb to stay low in every
wh-question, with short and long wh-phrases alike and the verb-second order still grammatical,
so the table gives it no movement to Int⁰; it is the mirror image of English on the declarative
and wh-question heads.

## References

* [westergaard-2009]
* [faarlund-lie-vannebo-1997]
-/

@[expose] public section

namespace Norwegian

open Minimalist

/-- Standard Norwegian moves the finite verb to Decl⁰, Int⁰ and Pol⁰. -/
abbrev verbSecond : V2Grammar := {.Decl, .Int, .Pol}

/-- Nordmøre Norwegian moves the finite verb to Decl⁰ and Pol⁰; its wh-questions allow both
orders, so no movement to Int⁰ is recorded. -/
abbrev Nordmore.verbSecond : V2Grammar := {.Decl, .Pol}

end Norwegian
