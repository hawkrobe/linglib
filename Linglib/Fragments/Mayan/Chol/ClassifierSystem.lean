import Linglib.Features.NounCategorization.Basic
import Linglib.Fragments.Mayan.Chol.Classifiers

/-!
# Ch'ol noun-categorization system

Classifier-system metadata for Ch'ol (ISO `ctu`), aggregating the lexical
classifier inventory into a `System` summary against [aikhenvald-2000]'s
typological schema, with Ch'ol as the empirical anchor ([bale-coon-2014]).

## Implementation notes

The lexical classifier inventory lives in
`Fragments/Mayan/Chol/Classifiers.lean`; this file aggregates it.
Per-language claims (consensus, see [bale-coon-2014], [bale-et-al-2019],
[little-moroney-royer-2022]): suffix realization on the numeral stem;
classifier obligatory with Ch'ol-native numerals; Spanish loan numerals are
ungrammatical *with* CLF; *-p'ej* serves as the generic default; CLF/PL
co-occurrence is attested. Theoretical-strategy assignments (CLF-for-NUM vs
CLF-for-N) live in the paper-anchored Studies that consume this profile.
-/

namespace Chol

open NounCategorization (collectSemantics) in
/-- Ch'ol numeral classifier system: suffix on the numeral stem,
restricted to numeralNP scope, with CLF/PL co-occurrence. -/
def classifierSystem : NounCategorization.System :=
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
  , source := "[bale-coon-2014]; [aikhenvald-2000] (schema)" }

end Chol
