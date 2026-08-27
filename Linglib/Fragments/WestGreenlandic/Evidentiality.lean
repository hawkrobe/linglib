import Linglib.Semantics.Evidential.Defs

/-!
# West Greenlandic Evidentiality
[de-haan-2013] [aikhenvald-2004]

Inferential mood via verbal suffix; no dedicated direct-evidence marker.
WALS and Aikhenvald agree.
-/

namespace WestGreenlandic.Evidentiality

/-! ### Typed evidential inventory

West Greenlandic's inferential mood: a single verbal-affix marker
covering inference; no dedicated direct or reportative marker. -/

open Evidential

def evidentials : List Evidential :=
  [ { form := "-gunarpoq", exponent := .verbalAffix, covers := {.inference, .assumption} } ]

end WestGreenlandic.Evidentiality
