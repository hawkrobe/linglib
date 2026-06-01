import Linglib.Typology.ClassifierSystem
import Linglib.Fragments.Mayan.Chol.Classifiers

/-!
# Ch'ol noun-categorization system
@cite{aikhenvald-2000} (typological schema); @cite{bale-coon-2014} (Ch'ol empirical anchor)

Classifier-system metadata for Ch'ol (ISO `ctu`). The lexical classifier
inventory lives in `Fragments/Mayan/Chol/Classifiers.lean`; this file
aggregates that inventory into a `NounCategorizationSystem` summary.

Per-language claims (consensus, see @cite{bale-coon-2014},
@cite{bale-et-al-2019}, @cite{little-moroney-royer-2022}): suffix
realization on the numeral stem; classifier obligatory with Ch'ol-native
numerals; Spanish loan numerals are ungrammatical *with* CLF; *-p'ej*
serves as the generic default; CLF/PL co-occurrence is attested.
Theoretical-strategy assignments (CLF-for-NUM vs CLF-for-N) live in the
paper-anchored Studies that consume this profile.
-/

namespace Chol

open Typology (collectSemantics) in
/-- Ch'ol numeral classifier system: suffix on the numeral stem,
restricted to numeralNP scope, with CLF/PL co-occurrence. -/
def classifierSystem : Typology.NounCategorizationSystem :=
  { family := "Mayan"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP]
  , assignment := .semantic
  , realizations := [.suffix]
  , hasAgreement := false
  , inventorySize := Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true
  , preferredSemantics := collectSemantics Classifiers.allClassifiers
  , pluralClfCooccur := true
  , source := "@cite{bale-coon-2014}; @cite{aikhenvald-2000} (schema)" }

end Chol
