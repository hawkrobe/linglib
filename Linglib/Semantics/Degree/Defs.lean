import Linglib.Core.Order.Boundedness

/-!
# Shape enums for degree constructions
[rett-2015] [beck-2011]

The shared taxonomies of degree morphosyntax: `DegPType` (degree heads) and
`AdjectivalConstruction` (surface constructions, tracked by evaluativity
analyses and markedness implicature). Antonym polarity is the spine's
`Core.Order.ScalePolarity` directly — no local alias.
-/

namespace Degree

open Core.Order (ScalePolarity)


/-- The compositional structure of a Degree Phrase (DegP).

In all degree frameworks, DegP is the syntactic locus where degree
comparison happens. The internal structure varies — Kennedy posits
`[DegP [Deg -er/as/est] [DegComplement than-clause]]`, Heim posits a
sentential `-er` operator — but the framework-independent taxonomy is
captured here. -/
inductive DegPType where
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
