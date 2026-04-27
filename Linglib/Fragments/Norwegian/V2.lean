import Linglib.Theories.Syntax.Minimalism.ExtendedProjection.Basic

/-!
# Norwegian V2 Profiles
@cite{westergaard-2009}

V2 micro-parameter profiles for Norwegian varieties (Table 3.1).
-/

namespace Fragments.Norwegian

open Minimalism (ForceHead V2Profile)

/-- Standard Norwegian: V-to-C in declaratives, wh-questions, and
    yes/no-questions. -/
abbrev stdNorwegian : V2Profile :=
  {.Decl, .Int, .Pol}

/-- Nordmøre Norwegian: V-to-C in declaratives and yes/no-questions but
    NOT in wh-questions. Mirror image of English on Decl vs. Int. -/
abbrev nordmoreNorwegian : V2Profile :=
  {.Decl, .Pol}

end Fragments.Norwegian
