import Linglib.Typology.Pronoun.Basic

/-!
# German Reciprocal Fragment
@cite{nordlinger-2023}

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

open Pronoun

/-- sich — reflexive/reciprocal pronoun (3rd person). -/
def sich : Entry :=
  { form := "sich", person := some .third }

/-- einander — dedicated reciprocal pronoun. -/
def einander : Entry :=
  { form := "einander", person := some .third, number := some .pl }

/-- The dedicated reciprocal form is distinct from the reflexive. -/
theorem einander_distinct_from_sich :
    einander.form ≠ sich.form := by decide

end German.Reciprocals
