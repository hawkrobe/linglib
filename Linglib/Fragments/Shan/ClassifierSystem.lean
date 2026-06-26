import Linglib.Features.NounCategorization.Basic
import Linglib.Fragments.Shan.Classifiers

/-!
# Shan noun-categorization system
[aikhenvald-2000] (typological schema); [moroney-2021] (Shan empirical anchor)

Classifier-system metadata for Shan (ISO `shn`). The lexical classifier
inventory lives in `Fragments/Shan/Classifiers.lean`; this file
aggregates that inventory into a `System` summary.

Per-language claims (consensus, see [moroney-2021],
[little-moroney-royer-2022]): free-morpheme classifiers derived
from nominal elements (e.g. *tǒ* = 'body'); uniform classifier
requirement on numerals; scope extending beyond numerals to
quantifiers, demonstratives, and relative clauses.
-/

namespace Shan

open NounCategorization (collectSemantics) in
/-- Shan numeral classifier system: free morphemes appearing with
numerals and broader DP scope. -/
def classifierSystem : NounCategorization.System :=
  { family := "Kra-Dai"
  , classifierType := .numeralClassifier
  , scopes := [.numeralNP, .attributiveNP]
  , assignment := .semantic
  , realizations := [.freeForm]
  , hasAgreement := false
  , inventorySize := Classifiers.allClassifiers.length
  , isObligatory := true
  , hasUnmarkedDefault := true
  , preferredSemantics := collectSemantics Classifiers.allClassifiers
  , pluralClfCooccur := false
  , source := "[moroney-2021]; [aikhenvald-2000] (schema)" }

end Shan
