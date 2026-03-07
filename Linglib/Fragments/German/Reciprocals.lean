import Linglib.Core.Lexical.Pronouns

/-!
# German Reciprocal Fragment
@cite{nordlinger-2023}

German has two reciprocal strategies:

1. **"sich"** — reflexive pronoun, also used for reciprocal (bivalent).
   Occupies the object position; both "sich" uses preserve transitivity.

2. **"einander"** — dedicated reciprocal pronoun (bivalent, bipartite NP).
   Unambiguously reciprocal, used to disambiguate from reflexive reading.

WALS Ch 106 classifies German as "mixed" because "sich" is shared
between reflexive and reciprocal uses.
-/

namespace Fragments.German.Reciprocals

open Core.Pronouns

/-- sich — reflexive/reciprocal pronoun (3rd person). -/
def sich : PronounEntry :=
  { form := "sich", person := some .third }

/-- einander — dedicated reciprocal pronoun. -/
def einander : PronounEntry :=
  { form := "einander", person := some .third, number := some .pl }

/-- The dedicated reciprocal form is distinct from the reflexive. -/
theorem einander_distinct_from_sich :
    einander.form ≠ sich.form := by decide

end Fragments.German.Reciprocals
