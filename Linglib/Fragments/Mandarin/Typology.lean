import Linglib.Typology.LanguageProfile
import Linglib.Fragments.Mandarin.Morph
import Linglib.Fragments.Mandarin.Classifiers

/-!
# Mandarin typological profile

Aggregate WALS-style typological profile for Mandarin (ISO 639-3 `cmn`).
-/

namespace Fragments.Mandarin

open Typology in
open Core.NounCategorization (collectSemantics) in
/-- Mandarin: SVO, mixed adpositions, mixed headedness. -/
def typology : LanguageProfile :=
  LanguageProfile.empty "cmn" "Mandarin"
    |>.withWordOrderFromWALS
    |>.withAdpositionFromWALS
    |>.withMorph morphProfile
    |>.withRelativization
        { subjStrategy := .gap
        , oblStrategy := .gap
        , rcPosition := .preNominal
        , lowestRelativizable := .oblique
        , notes := "Gap + relativizer de; pre-nominal RC; SVO but RC-N order" }
    |>.withClassifierSystem
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
