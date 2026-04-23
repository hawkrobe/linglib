import Linglib.Features.V2

/-!
# Danish V2 Profile
@cite{westergaard-2009}

V2 verb-placement data for Danish (Table 3.1).
-/

namespace Fragments.Danish

open Features

/-- Danish: like Standard Norwegian but with V2 also in exclamatives. -/
def danish : V2Data where
  name := "Danish"
  declarativeV2 := true;  whQuestionV2 := true;  yesNoQuestionV2 := true
  exclamativeV2 := true;  imperativeV2 := false; embeddedFinV2 := false; embeddedQuestionV2 := false

end Fragments.Danish
