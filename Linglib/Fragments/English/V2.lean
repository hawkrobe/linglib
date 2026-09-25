module

public import Linglib.Syntax.Minimalist.VerbSecond

/-!
# English verb second

This file records the verb-second grammars of Standard English and Belfast English, the
clause-type heads of Westergaard's split ForceP that the finite verb moves to, as her Table 3.1
gives them. Standard English moves the verb, an auxiliary, only in matrix wh-questions and
yes/no-questions, the subject–auxiliary inversion. Belfast English adds imperatives, *Bring you
that with you!*, and embedded yes/no-questions, *They asked me was I going to the party*, the
examples Henry reports; Westergaard notes that the imperative movement may target a lower head.

## References

* [westergaard-2009]
* [henry-1997]
-/

@[expose] public section

namespace English

open Minimalist

/-- Standard English moves the finite verb to Int⁰ and Pol⁰ only. -/
abbrev verbSecond : V2Grammar := {.Int, .Pol}

/-- Belfast English moves the finite verb to Int⁰, Pol⁰, Imp⁰ and, in embedded questions,
Wh⁰. -/
abbrev Belfast.verbSecond : V2Grammar := {.Int, .Pol, .Imp, .Wh}

end English
