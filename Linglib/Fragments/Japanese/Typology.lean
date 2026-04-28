import Linglib.Typology.LanguageProfile
import Linglib.Fragments.Japanese.Morph
import Linglib.Fragments.Japanese.Classifier

/-!
# Japanese typological profile

Aggregate WALS-style typological profile for Japanese (ISO 639-3 `jpn`).
-/

namespace Fragments.Japanese

open Typology in
/-- Japanese: SOV, postpositional, canonical head-final. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "jpn" "Japanese"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .gap
        , rcPosition := .preNominal
        , lowestRelativizable := .genitive
        , notes := "Gap strategy throughout; pre-nominal RC; no relative "
                ++ "pronoun; genitive relativization possible but rare" }
    |>.withClassifierSystem
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
