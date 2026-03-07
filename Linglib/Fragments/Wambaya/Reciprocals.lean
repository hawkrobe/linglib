import Linglib.Core.Lexical.Word

/-!
# Wambaya Reciprocal Fragment
@cite{nordlinger-2023}

Wambaya (Australian, Mirndi) uses the clitic "nyurrunyurru" for both
reciprocal and reflexive meanings. This is a clitic strategy (bivalent):
the reciprocal form attaches to the auxiliary and the clause retains
its transitive structure.

Example: @cite{nordlinger-2023} ex. 11 (citing Nordlinger 1998).

WALS Ch 106 classifies Wambaya as "identical to reflexive."
-/

namespace Fragments.Wambaya.Reciprocals

/-- nyurrunyurru — reciprocal/reflexive clitic. -/
def nyurrunyurru : Word :=
  ⟨"nyurrunyurru", .PART, {}⟩

/-- The same form serves both reciprocal and reflexive functions. -/
def isIdenticalToReflexive : Bool := true

end Fragments.Wambaya.Reciprocals
