import Linglib.Core.Grammar

/-!
# English V2 Profiles
@cite{westergaard-2009}

V2 verb-placement data for English varieties (Table 3.1).
-/

namespace Fragments.English

/-- Standard English: V2 only in wh-questions and yes/no-questions
    (via subject-auxiliary inversion). -/
def stdEnglish : V2Data where
  name := "Standard English"
  declV2 := false; whQV2 := true;  ynQV2 := true
  exclV2 := false; impV2 := false; embFinV2 := false; embQV2 := false

/-- Belfast English: like Standard English but with V2 also in
    imperatives and embedded questions (@cite{henry-1995}). -/
def belfastEnglish : V2Data where
  name := "Belfast English"
  declV2 := false; whQV2 := true;  ynQV2 := true
  exclV2 := false; impV2 := true;  embFinV2 := false; embQV2 := true

end Fragments.English
