import Linglib.Features.V2

/-!
# German V2 Profile
@cite{westergaard-2009}

V2 verb-placement data for German (Table 3.1).
-/

namespace Fragments.German

open Features

/-- German: V2 in root declaratives, wh-questions, and yes/no-questions;
    additionally V-to-I in embedded clauses, yielding verb-final surface
    order due to SOV base. -/
def german : V2Data where
  name := "German"
  declarativeV2 := true;  whQuestionV2 := true;  yesNoQuestionV2 := true
  exclamativeV2 := false; imperativeV2 := false; embeddedFinV2 := true; embeddedQuestionV2 := false

end Fragments.German
