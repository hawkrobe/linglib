import Linglib.Typology.UniversalQuantifier

/-!
# Syrian Arabic universal quantifier

[haslinger-etal-2025-nllt]

Syrian Arabic (Semitic) is a **1-form** language: the UQ lexeme `kul` yields a
distributive ([+dist]) reading with a singular complement (`kul`+NP.sg) and a
non-distributive ([−dist]) reading with a plural complement (`kul`+DP.pl). The
same item is the Standard Arabic `kull` discussed by Fassi Fehri (2020).
-/

namespace Arabic.Syrian

open Typology.UniversalQuantifier

/-- Syrian Arabic `kul` — the sole DP-internal universal quantifier. [+dist]
with a singular complement, [−dist] with a plural complement. -/
def universalQuantifier : UQProfile :=
  { language := "Syrian Arabic"
  , family := "Semitic"
  , systemType := .oneForm
  , distForm := "kul"
  , source := "[haslinger-etal-2025-nllt] (native-speaker consultant; cf. Fassi Fehri 2020 for Standard Arabic kull)" }

end Arabic.Syrian
