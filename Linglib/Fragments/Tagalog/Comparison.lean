import Linglib.Syntax.Comparative

/-!
# Tagalog comparative data

Tagalog compares with *mas Adj si X kaysa (kay) Y* — the Spanish-derived
degree word *mas* plus the standard marker *kaysa* — or with *higit na Adj sa
Y* built on *higit* 'exceed' with an oblique *sa*-marked standard. Tagalog is
uncoded in WALS Ch 121A, and neither construction's anatomy is recorded here
pending a grammar source: *kaysa* itself embeds the oblique marker *kay*, and
the *higit* standard is oblique rather than a direct object, so neither the
particle nor the exceed classification can be derived responsibly.
-/

set_option autoImplicit false

namespace Tagalog.Comparison

open Comparative

/-- Free degree words *mas* and *higit*. -/
def degreeWord : DegreeWordType := .hasDegreeWord

end Tagalog.Comparison
