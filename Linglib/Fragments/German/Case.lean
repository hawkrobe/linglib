module

public import Linglib.Syntax.Case.Basic

/-!
# German Case Inventory [blake-1994]

German has **4 cases**: NOM, ACC, GEN, DAT, one of the four-case systems
[blake-1994] cites (`Studies/Blake1994.lean`).

## Syncretism

German has extensive syncretism, especially in the definite article:
- NOM/ACC syncretism: neuter and feminine (der/das/die paradigm)
- DAT/GEN syncretism: rare but occurs in some dialects

-/

@[expose] public section

namespace German.Case

/-- German 4-case inventory. -/
def inventory : Finset Case :=
  {.nom, .acc, .gen, .dat}

end German.Case
