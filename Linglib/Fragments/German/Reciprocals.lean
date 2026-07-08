import Linglib.Syntax.Pronoun.Basic
import Linglib.Syntax.Reciprocal

/-!
# German Reciprocal Fragment
[nordlinger-2023]

German has two reciprocal strategies:

1. **"sich"** — reflexive pronoun, also used for reciprocal (bivalent).
   Occupies the object position; both "sich" uses preserve transitivity.

2. **"einander"** — dedicated reciprocal pronoun (bivalent).
   A single-word pronoun (not a bipartite NP like English "each other"
   or Icelandic "hvor...annad"). Unambiguously reciprocal, used to
   disambiguate from reflexive reading.

WALS Ch 106 classifies German as "mixed" because "sich" is shared
between reflexive and reciprocal uses.
-/

namespace German.Reciprocals

open Reciprocal

/-- einander — dedicated reciprocal pronoun. -/
def einander : ReciprocalMarker :=
  { form := "einander", strategy := .recipPronoun }

/-- sich — reflexive pronoun in reciprocal use ([siloni-2012] fn. 13
    treats *sich*-reciprocals as syntactic reciprocal verbs). -/
def sich : ReciprocalMarker :=
  { form := "sich", strategy := .recipPronoun
  , readings := [.reciprocal, .reflexive] }

/-- The dedicated reciprocal form is distinct from the reflexive. -/
theorem einander_distinct_from_sich :
    einander.form ≠ sich.form := by decide

/-- Marker inventory: dedicated *einander* plus reflexive-identical
    *sich* — jointly the WALS "mixed" configuration. -/
def markers : List ReciprocalMarker := [einander, sich]

end German.Reciprocals
