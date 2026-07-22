/-!
# Adjectival constructions

`AdjectivalConstruction`: the surface constructions whose evaluativity
[rett-2015] tracks, consumed by evaluativity analyses and markedness
implicature. The Deg⁰ head inventory is `Degree.Head` in
`Syntax/Category/Degree`.
-/

namespace Degree

/-- Surface adjectival constructions, as tracked by evaluativity analyses
and markedness implicature. -/
inductive AdjectivalConstruction where
  /-- "Kim is tall" — unmarked form. -/
  | positive
  /-- "Kim is taller than Sam". -/
  | comparative
  /-- "Kim is as tall as Sam". -/
  | equative
  /-- "Kim is 6 feet tall" — explicit measure phrase. -/
  | measurePhrase
  /-- "How tall is Kim?". -/
  | degreeQuestion
  deriving DecidableEq, Repr

/-- Bare lowercase construction names for diagnostic messages, distinct
from `Repr` (which prefixes the namespace). -/
instance : ToString AdjectivalConstruction where
  toString
    | .positive => "positive"
    | .comparative => "comparative"
    | .equative => "equative"
    | .measurePhrase => "measurePhrase"
    | .degreeQuestion => "degreeQuestion"

end Degree
