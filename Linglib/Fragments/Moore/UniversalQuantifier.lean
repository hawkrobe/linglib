import Linglib.Typology.UniversalQuantifier

/-!
# Moore universal quantifier

[haslinger-etal-2025-nllt]

Moore (Mabia) is a **1-form** language: the single UQ lexeme `fãa` yields a
distributive ([+dist]) reading with a singular complement and a non-distributive
([−dist]) reading with a plural complement.
-/

namespace Moore

open Typology.UniversalQuantifier

/-- Moore `fãa` — the sole DP-internal universal quantifier. [+dist] with a
singular complement, [−dist] with a plural complement. -/
def universalQuantifier : UQProfile :=
  { language := "Moore"
  , family := "Mabia"
  , systemType := .oneForm
  , distForm := "fãa"
  , source := "[haslinger-etal-2025-nllt] (elicited, two native-speaker consultants)" }

end Moore
