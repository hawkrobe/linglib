import Linglib.Typology.ClassifierSystem

/-!
# Western Armenian noun-categorization system
@cite{bale-khanjian-2014} @cite{bale-khanjian-2008}

Classifier-system data for Western Armenian (ISO `hyw`). WALS Ch 55 has
no direct `hyw` entry; the related `arz`/`hye` entries are Iranian
Armenian, not Western Armenian. Non-obligatory status follows directly
from @cite{bale-khanjian-2014}'s data: numerals combine with bare nouns
(eq. 10a *yergu dəgha vaze-ts* "two boys ran") and also with the plural
form (eq. 10b *yergu dəgha-ner vaze-ts-in*, same meaning). Plural nouns
are additionally *incompatible* with classifiers (footnote 3, citing
@cite{borer-2005} and @cite{bale-khanjian-2008}).

The Aikhenvald `numeralClassifier` category is a misfit for Western
Armenian: with `isObligatory := false` and an essentially empty
inventory, WA arguably has no classifier system in Aikhenvald's sense
at all. The `.numeralClassifier` tag is retained pragmatically so cross-
language theorems can filter on `classifierType`.
-/

namespace Fragments.Armenian

/-- Western Armenian noun-categorization system: non-obligatory per
    @cite{bale-khanjian-2014} eq. 10. Empty inventory; plurals are
    incompatible with classifiers. -/
def classifierSystem : Typology.NounCategorizationSystem :=
  { family := "Indo-European"
  , classifierType := .numeralClassifier  -- Aikhenvald misfit, see docstring
  , scopes := [.numeralNP]
  , assignment := .semantic
  , realizations := [.freeForm]
  , hasAgreement := false
  , inventorySize := 0
  , isObligatory := false  -- KEY: numerals combine with bare nouns (BK 2014 eq. 10a)
  , hasUnmarkedDefault := false
  , preferredSemantics := []
  , hasObligatoryNumber := false  -- general-number singular per BK 2014
  , pluralClfCooccur := false  -- plurals incompatible with CLs (BK 2014 fn 3)
  , source := "@cite{bale-khanjian-2014} eq. 10; @cite{bale-khanjian-2008}" }

end Fragments.Armenian
