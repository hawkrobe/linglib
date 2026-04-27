import Linglib.Theories.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# German V2 Profile
@cite{westergaard-2009}

V2 micro-parameter profile for German (Table 3.1, row "German").

## Caveats

`.Pol` records the verb-fronting in matrix yes/no questions, which
surfaces as V1 (Spec-CP empty), not V2 — included with the V2 cluster
because the fronting target is in the CP domain.

`.Fin` records V-to-I in embedded clauses, NOT V-to-C. In German's
SOV base order, V-to-I yields verb-final embedded surface order. The
+Fin° claim is the @cite{vikner-1995} analysis;
@cite{harizanov-gribanova-2019} denies V-to-I in German embedded
clauses. See `Phenomena/WordOrder/Studies/HarizanovGribanova2019.lean`
for the formal contrast.
-/

namespace Fragments.German

open Minimalist (ForceHead V2Profile)

/-- German: V-to-C in root declaratives, matrix wh-questions, and
    yes/no-questions; +Fin° for V-to-I in embedded clauses (contested). -/
abbrev german : V2Profile :=
  {.Decl, .Int, .Pol, .Fin}

end Fragments.German
