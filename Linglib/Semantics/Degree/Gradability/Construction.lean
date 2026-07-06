/-!
# Adjectival construction types

The surface constructions a gradable adjective participates in — positive,
comparative, equative, measure phrase, degree question. Evaluativity analyses
track which constructions trigger evaluative readings ([rett-2015]); markedness
implicature computes alternatives over them
(`Pragmatics/Implicature/Markedness.lean`).

The degree-substrate DegP taxonomy (`DegPType`, covering degree *heads* rather
than adjectival surface constructions) lives in `Semantics/Degree/Comparative.lean`.
-/

namespace Degree

/-- Degree construction type. Used by evaluativity analyses to track which
surface constructions trigger evaluative readings. -/
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
  deriving Repr, DecidableEq

/-- User-facing rendering, distinct from `Repr` (which prefixes the
namespace). Consumed by Studies files that string-interpolate construction
names into diagnostic messages — see e.g.
`Studies/Rett2015Implicature.lean`. -/
instance : ToString AdjectivalConstruction where
  toString
    | .positive => "positive"
    | .comparative => "comparative"
    | .equative => "equative"
    | .measurePhrase => "measurePhrase"
    | .degreeQuestion => "degreeQuestion"

end Degree
