import Linglib.Core.Grammar

/-!
# German V2 Profile
@cite{westergaard-2009}

V2 verb-placement data for German (Table 3.1).
-/

namespace Fragments.German

/-- German: V2 in root declaratives, wh-questions, and yes/no-questions;
    additionally V-to-I in embedded clauses, yielding verb-final surface
    order due to SOV base. -/
def german : V2Data where
  name := "German"
  declV2 := true;  whQV2 := true;  ynQV2 := true
  exclV2 := false; impV2 := false; embFinV2 := true; embQV2 := false

end Fragments.German
