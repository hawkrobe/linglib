import Linglib.Typology.UniversalQuantifier

/-!
# Wolof universal quantifier

[haslinger-etal-2025-nllt]

Wolof (Atlantic) is a **1-form** language: the noun-class-agreeing UQ exponent
`-epp` (e.g. `b-epp`, `y-epp`) yields a distributive ([+dist]) reading with a
singular complement and a non-distributive ([−dist]) reading with a plural
complement. Data as reported by Tamba, Torrence & Zribi-Hertz (2012) and
surveyed in [haslinger-etal-2025-nllt].
-/

namespace Wolof

open Typology.UniversalQuantifier

/-- Wolof `-epp` — the sole DP-internal universal quantifier (noun-class
agreeing). [+dist] with a singular complement, [−dist] with a plural
complement. -/
def universalQuantifier : UQProfile :=
  { language := "Wolof"
  , family := "Atlantic"
  , systemType := .oneForm
  , distForm := "-epp"
  , source := "[haslinger-etal-2025-nllt] (Tamba, Torrence & Zribi-Hertz 2012)" }

end Wolof
