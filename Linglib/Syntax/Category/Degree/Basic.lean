/-!
# The degree head (Deg)

This file defines `Degree.Head`, the inventory of the functional category
Deg that heads the adjectival extended projection ([abney-1987];
[corver-1997]). The comparison heads are surveyed in [beck-2011]; the
*too* ~ *enough* pair belongs to the sufficiency-excess literature
([meier-2003]).
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
