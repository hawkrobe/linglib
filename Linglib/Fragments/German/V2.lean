import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# German V2 Profile
[westergaard-2009]

V2 micro-parameter profile for German (Table 3.1, row "German").

## Caveats

`.Pol` records the verb-fronting in matrix yes/no questions, which
surfaces as V1 (Spec-CP empty), not V2 — included with the V2 cluster
because the fronting target is in the CP domain.

`.Fin` records V-to-I in embedded clauses, NOT V-to-C. In German's
SOV base order, V-to-I yields verb-final embedded surface order. The
+Fin° claim is the [vikner-1995] analysis; for
[harizanov-gribanova-2019] the unification of T and V is postsyntactic
amalgamation rather than syntactic movement (V Raising into T in their
(59), or T Lowering as in Danish, which [haider-2010]'s evidence
favours), and the verb-second step is syntactic movement of T. See
`Studies/HarizanovGribanova2019.lean`.
-/

namespace German

open Minimalist (ForceHead V2Profile)

/-- German: V-to-C in root declaratives, matrix wh-questions, and
    yes/no-questions; +Fin° for V-to-I in embedded clauses (contested). -/
abbrev german : V2Profile :=
  {.Decl, .Int, .Pol, .Fin}

end German
