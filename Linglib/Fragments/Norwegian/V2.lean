import Linglib.Core.Grammar

/-!
# Norwegian V2 Profiles
@cite{westergaard-2009}

V2 verb-placement data for Norwegian varieties (Table 3.1).
-/

namespace Fragments.Norwegian

/-- Standard Norwegian: V2 in declaratives, wh-questions, and
    yes/no-questions. No V2 in exclamatives, imperatives, embedded
    clauses, or embedded questions. -/
def stdNorwegian : V2Data where
  name := "Standard Norwegian"
  declV2 := true;  whQV2 := true;   ynQV2 := true
  exclV2 := false; impV2 := false;  embFinV2 := false; embQV2 := false

/-- Nordmøre Norwegian: V2 in declaratives and yes/no-questions,
    but NOT in wh-questions. Mirror image of English on
    declaratives vs. wh-questions. -/
def nordmoreNorwegian : V2Data where
  name := "Nordmøre Norwegian"
  declV2 := true;  whQV2 := false;  ynQV2 := true
  exclV2 := false; impV2 := false;  embFinV2 := false; embQV2 := false

end Fragments.Norwegian
