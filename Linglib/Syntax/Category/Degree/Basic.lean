/-!
# The degree head (Deg)

The functional category Deg heading the adjectival extended projection
([abney-1987]; refined against Q by [corver-1997]). `Degree.Head` is the
Deg⁰ inventory — comparison heads per [beck-2011], the *too* ~ *enough*
pair per [meier-2003].
-/

namespace Degree

/-- The Deg⁰ inventory of a Degree Phrase. The phrase's internal structure
is framework-dependent — [kennedy-1999] posits a than-clause complement to
Deg, [heim-2000] a scopal degree operator — but the head inventory itself
is framework-independent. -/
inductive Head where
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

end Degree
