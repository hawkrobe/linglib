import Linglib.Theories.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# Danish V2 Profile
@cite{westergaard-2009}

V2 micro-parameter profile for Danish (Table 3.1).
-/

namespace Fragments.Danish

open Minimalist (ForceHead V2Profile)

/-- Danish: like Standard Norwegian plus V-to-C in exclamatives. -/
abbrev danish : V2Profile :=
  {.Decl, .Int, .Pol, .Excl}

end Fragments.Danish
