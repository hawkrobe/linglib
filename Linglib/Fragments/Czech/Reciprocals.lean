import Linglib.Core.Lexical.Pronouns

/-!
# Czech Reciprocal Fragment
@cite{nordlinger-2023} @cite{siloni-2008}

Czech uses the reflexive clitic "se" for reciprocal meaning (monovalent,
identical to reflexive). Syntactically formed per @cite{siloni-2008}:
CANNOT form discontinuous reciprocals.

@cite{nordlinger-2023} ex. 29.

WALS Ch 106 classifies Czech as "identical to reflexive."
-/

namespace Fragments.Czech.Reciprocals

open Core.Pronouns

/-- se — reflexive/reciprocal clitic. -/
def se : PronounEntry :=
  { form := "se", person := some .third }

/-- The same form serves both reciprocal and reflexive functions. -/
def isIdenticalToReflexive : Bool := true

end Fragments.Czech.Reciprocals
