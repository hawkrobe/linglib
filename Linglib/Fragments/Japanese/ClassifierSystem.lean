import Linglib.Typology.ClassifierSystem
import Linglib.Fragments.Japanese.Classifier

/-!
# Japanese noun-categorization system
@cite{aikhenvald-2000} @cite{downing-1996}

Classifier-system metadata for Japanese (ISO `jpn`). The lexical
classifier inventory itself lives in `Fragments/Japanese/Classifier.lean`;
this file aggregates that inventory into the typological-system summary
(`NounCategorizationSystem`).
-/

namespace Fragments.Japanese

/-- Japanese numeral classifier system: obligatory CL suffixing on
    numerals; default つ tsu; preferred semantics derived from the
    lexical inventory. -/
def classifierSystem : Typology.NounCategorizationSystem :=
  { family := "Japonic"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP]
  , assignment := .semantic
  , realizations := [.suffix]  -- classifiers suffix to numerals
  , hasAgreement := false
  , inventorySize := Classifier.all.length
  , isObligatory := true
  , hasUnmarkedDefault := true  -- つ tsu is default
  , preferredSemantics := Classifier.allEncodedParams
  , source := "@cite{aikhenvald-2000}; @cite{downing-1996}" }

end Fragments.Japanese
