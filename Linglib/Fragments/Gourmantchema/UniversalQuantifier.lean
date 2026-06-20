import Linglib.Typology.UniversalQuantifier

/-!
# Gourmantchema universal quantifier

[haslinger-etal-2025-nllt]

Gourmantchema (Mabia) is a **1-form** language: the single UQ lexeme `kuli`
yields a distributive ([+dist]) reading with a singular complement and a
non-distributive ([−dist]) reading with a plural complement.
-/

namespace Gourmantchema

open Typology.UniversalQuantifier

/-- Gourmantchema `kuli` — the sole DP-internal universal quantifier. [+dist]
with a singular complement, [−dist] with a plural complement. -/
def universalQuantifier : UQProfile :=
  { language := "Gourmantchema"
  , family := "Mabia"
  , systemType := .oneForm
  , distForm := "kuli"
  , source := "[haslinger-etal-2025-nllt] (elicited, native-speaker consultant)" }

end Gourmantchema
