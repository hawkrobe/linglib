import Linglib.Features.V2

/-!
# Danish V2 Profile
@cite{westergaard-2009}

V2 verb-placement data for Danish (Table 3.1).
-/

namespace Fragments.Danish

/-- Danish: like Standard Norwegian but with V2 also in exclamatives. -/
def danish : V2Data where
  name := "Danish"
  declV2 := true;  whQV2 := true;  ynQV2 := true
  exclV2 := true;  impV2 := false; embFinV2 := false; embQV2 := false

end Fragments.Danish
