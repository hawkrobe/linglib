/-!
# Shape enums for degree constructions

The shared taxonomies of degree morphosyntax: `DegreeHead` (the Deg⁰
inventory — comparison heads per [beck-2011], the *too* ~ *enough* pair per
[meier-2003]) and `AdjectivalConstruction` (the surface constructions whose
evaluativity [rett-2015] tracks).
-/

namespace Degree

/-- The degree-head (Deg⁰) inventory of a Degree Phrase. The phrase's
internal structure is framework-dependent — [kennedy-1999] posits a
than-clause complement to Deg, [heim-2000] a scopal degree operator — but
the head inventory itself is framework-independent. -/
inductive DegreeHead where
  /-- `-er` / *more*. -/
  | comparative
  /-- `as...as`. -/
  | equative
  /-- `-est` / *most*. -/
  | superlative
  /-- *too*. -/
  | excessive
  /-- *enough*. -/
  | sufficiency
  deriving DecidableEq, Repr

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
