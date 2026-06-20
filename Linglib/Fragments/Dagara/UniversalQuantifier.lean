import Linglib.Typology.UniversalQuantifier

/-!
# Dagara universal quantifier

[haslinger-etal-2025-nllt]

Dagara (Mabia) is a **1-form** language: the single UQ lexeme `'hà` yields a
distributive ([+dist]) reading with a singular count complement (`'hà`+NP.sg)
and a non-distributive ([−dist]) reading with a plural complement (`'hà`+DP.pl).
The reading is fixed by complement number, not by a lexical [±dist] split.
-/

namespace Dagara

open Typology.UniversalQuantifier

/-- Dagara `'hà` — the sole DP-internal universal quantifier. [+dist] with a
singular complement, [−dist] with a plural complement. -/
def universalQuantifier : UQProfile :=
  { language := "Dagara"
  , family := "Mabia"
  , systemType := .oneForm
  , distForm := "'hà"
  , source := "[haslinger-etal-2025-nllt] (author elicitation; one author is a native speaker)" }

end Dagara
