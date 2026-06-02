import Linglib.Semantics.Evidential.Defs

/-!
# West Greenlandic Evidentiality
@cite{de-haan-2013} @cite{aikhenvald-2004}

Inferential mood via verbal suffix; no dedicated direct-evidence marker.
WALS and Aikhenvald agree.
-/

namespace WestGreenlandic.Evidentiality

/-! ### Typed evidential inventory

West Greenlandic's inferential mood: a single verbal-affix marker
covering inference; no dedicated direct or reportative marker. -/

open Semantics.Evidential

def evidentials : List Entry :=
  [ .inferential { form := "-gunarpoq", exponent := .verbalAffix } ]

example : evidentials.length = 1 := by decide
example : (evidentials.filter Entry.IsInferential).length = 1 := by decide

end WestGreenlandic.Evidentiality
