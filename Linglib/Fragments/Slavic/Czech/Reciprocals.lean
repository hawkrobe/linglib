import Linglib.Syntax.Pronoun.Basic

/-!
# Czech Reciprocal Fragment
@cite{nordlinger-2023} @cite{siloni-2008}

Czech uses the reflexive clitic "se" for reciprocal meaning (monovalent,
identical to reflexive). Syntactically formed per @cite{siloni-2008}:
CANNOT form discontinuous reciprocals.

@cite{nordlinger-2023} ex. 29.

Czech is not in the WALS Ch 106 sample, but "se" is shared between
reflexive and reciprocal uses, consistent with "identical to reflexive."
-/

namespace Czech.Reciprocals

open Pronoun

/-- se — reflexive/reciprocal clitic. -/
def se : PersonalPronoun :=
  { form := "se", person := some .third }

/-- The same form serves both reciprocal and reflexive functions. -/
def isIdenticalToReflexive : Bool := true

end Czech.Reciprocals
