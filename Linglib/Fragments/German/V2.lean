module

public import Linglib.Syntax.Minimalist.VerbSecond

/-!
# German verb second

This file records the verb-second grammar of German, the clause-type heads of Westergaard's
split ForceP that the finite verb moves to, as her Table 3.1 gives them: root declaratives,
wh-questions and yes/no-questions, and embedded declaratives without a complementizer, *Sie
sagte, sie würde kommen*, where the verb fills the finiteness head that the complementizer
*dass* otherwise occupies. The yes/no-question setting records verb fronting that surfaces as
V1, with an empty specifier, and belongs with verb second because the target is in the CP
domain.

## References

* [westergaard-2009]
-/

@[expose] public section

namespace German

open Minimalist

/-- German moves the finite verb to Decl⁰, Int⁰ and Pol⁰, and to Fin⁰ in embedded clauses
without a complementizer. -/
abbrev verbSecond : V2Grammar := {.Decl, .Int, .Pol, .Fin}

end German
