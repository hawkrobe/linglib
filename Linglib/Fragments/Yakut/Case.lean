module

public import Linglib.Syntax.Case.Basic

/-!
# Yakut (Sakha) case

Sakha has eight cases: nominative, accusative, genitive, dative, ablative, instrumental,
comitative and partitive. The genitive is homophonous with the nominative except after a
third-person possessive suffix. [baker-vinokurova-2010]'s account of how the structural cases
are assigned is in `Studies/BakerVinokurova2010.lean`.

## References

* [baker-vinokurova-2010]
-/

@[expose] public section

namespace Yakut

/-- The eight cases. -/
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
  /-- The partitive. -/
  | part
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
  | part => .part

end Yakut
