import Linglib.Features.V2

/-!
# Norwegian V2 Profiles
@cite{westergaard-2009}

V2 verb-placement data for Norwegian varieties (Table 3.1).
-/

namespace Fragments.Norwegian

open Features

/-- Standard Norwegian: V2 in declaratives, wh-questions, and
    yes/no-questions. No V2 in exclamatives, imperatives, embedded
    clauses, or embedded questions. -/
def stdNorwegian : V2Data where
  name := "Standard Norwegian"
  declarativeV2 := true;  whQuestionV2 := true;   yesNoQuestionV2 := true
  exclamativeV2 := false; imperativeV2 := false;  embeddedFinV2 := false; embeddedQuestionV2 := false

/-- Nordmøre Norwegian: V2 in declaratives and yes/no-questions,
    but NOT in wh-questions. Mirror image of English on
    declaratives vs. wh-questions. -/
def nordmoreNorwegian : V2Data where
  name := "Nordmøre Norwegian"
  declarativeV2 := true;  whQuestionV2 := false;  yesNoQuestionV2 := true
  exclamativeV2 := false; imperativeV2 := false;  embeddedFinV2 := false; embeddedQuestionV2 := false

end Fragments.Norwegian
