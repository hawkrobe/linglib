import Linglib.Syntax.Minimalist.VerbSecond

/-!
# English verb second

This file records the verb-second grammars of Standard English and Belfast English, the
clause-type heads of the split ForceP that the finite verb moves to, as Westergaard's Table 3.1
gives them. Standard English moves the verb only in matrix wh-questions and yes/no-questions,
the subject–auxiliary inversion. Belfast English adds embedded questions, Henry's *I wonder
could he come*.

## References

* [westergaard-2009]
* [henry-1995]
-/

namespace English

open Minimalist

/-- Standard English moves the finite verb to Int⁰ and Pol⁰ only. -/
abbrev stdEnglish : V2Grammar := {.Int, .Pol}

/-- Belfast English moves the finite verb to Int⁰, Pol⁰, Imp⁰ and, in embedded questions, Wh⁰.
-- UNVERIFIED: the Imp⁰ setting, matrix imperative verb movement distinct from Standard
-- English, reflects an earlier transcription and has not been confirmed against
-- [westergaard-2009] Table 3.1 or [henry-1995], whose monograph documents singular concord and
-- embedded inversion but no imperative micro-parameter for Belfast. -/
abbrev belfastEnglish : V2Grammar := {.Int, .Pol, .Imp, .Wh}

end English
