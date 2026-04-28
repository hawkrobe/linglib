import Linglib.Typology.ClassifierSystem
import Linglib.Fragments.Mandarin.Classifiers

/-!
# Mandarin noun-categorization system
@cite{aikhenvald-2000}

Classifier-system metadata for Mandarin (ISO `cmn`). The lexical
classifier inventory itself lives in `Fragments/Mandarin/Classifiers.lean`;
this file aggregates that inventory into the typological-system summary
(`NounCategorizationSystem`) consumed by `Phenomena/Classifiers/Typology.lean`.
-/

namespace Fragments.Mandarin

open Core.NounCategorization (collectSemantics) in
/-- Mandarin numeral classifier system: obligatory CL with numerals and
    demonstratives; default 个 gè; preferred semantics derived from the
    lexical inventory. -/
def classifierSystem : Typology.NounCategorizationSystem :=
  { family := "Sino-Tibetan"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP, .attributiveNP]  -- CLF with numerals AND demonstratives (那本书)
  , assignment := .semantic
  , realizations := [.freeForm]
  , hasAgreement := false
  , inventorySize := Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true  -- 个 gè is default
  , preferredSemantics := collectSemantics Classifiers.allClassifiers
  , source := "@cite{aikhenvald-2000} §4, §11.2.3" }

end Fragments.Mandarin
