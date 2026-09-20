import Linglib.Syntax.Minimalist.VerbSecond

/-!
# German verb second

This file records the verb-second grammar of German, the clause-type heads of the split ForceP
that the finite verb moves to, as Westergaard's Table 3.1 gives them: root declaratives,
wh-questions and yes/no-questions, and the finiteness head of embedded clauses. The
yes/no-question setting records verb fronting that surfaces as V1, with an empty specifier, and
belongs with verb second because the target is in the CP domain. The finiteness setting records
V-to-I in embedded clauses rather than V-to-C, which in German's verb-final base order yields
verb-final embedded order. That setting is Vikner's analysis; for Harizanov and Gribanova the
unification of T and V is postsyntactic amalgamation, V raising into T or T lowering as in
Danish, which Haider's evidence favours, and the verb-second step is syntactic movement of T,
see `Studies/HarizanovGribanova2019.lean`.

## References

* [westergaard-2009]
* [vikner-1995]
* [harizanov-gribanova-2019]
* [haider-2010]
-/

namespace German

open Minimalist

/-- German moves the finite verb to Decl⁰, Int⁰ and Pol⁰, and to Fin⁰ in embedded clauses. -/
abbrev german : V2Grammar := {.Decl, .Int, .Pol, .Fin}

end German
