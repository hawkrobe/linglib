module

public import Linglib.Syntax.Case.Basic

/-!
# Mongolian case

Mongolian (Khalkha and Chakhar) has seven cases: nominative, accusative, genitive, dative,
ablative, instrumental and comitative. The inventory has no dedicated locative, which
postpositions express. [gong-2022]'s account of how the structural cases are assigned is in
`Studies/Gong2022.lean`.

## References

* [gong-2022]
-/

@[expose] public section

namespace Mongolian

/-- The seven cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  /-- The ablative. -/
  | abl
  /-- The instrumental. -/
  | inst
  /-- The comitative. -/
  | com
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat
  | abl => .abl
  | inst => .inst
  | com => .com

end Mongolian
