import Linglib.Features.V2

/-!
# English V2 Profiles
@cite{westergaard-2009}

V2 verb-placement data for English varieties (Table 3.1).
-/

namespace Fragments.English

open Features

/-- Standard English: V2 only in wh-questions and yes/no-questions
    (via subject-auxiliary inversion). -/
def stdEnglish : V2Data where
  name := "Standard English"
  declarativeV2 := false; whQuestionV2 := true;  yesNoQuestionV2 := true
  exclamativeV2 := false; imperativeV2 := false; embeddedFinV2 := false; embeddedQuestionV2 := false

/-- Belfast English: like Standard English but with V2 also in
    imperatives and embedded questions (@cite{henry-1995}). -/
def belfastEnglish : V2Data where
  name := "Belfast English"
  declarativeV2 := false; whQuestionV2 := true;  yesNoQuestionV2 := true
  exclamativeV2 := false; imperativeV2 := true;  embeddedFinV2 := false; embeddedQuestionV2 := true

end Fragments.English
