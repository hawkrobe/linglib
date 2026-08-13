import Linglib.Syntax.Category.Determiner.Basic

/-!
# Fering determiner inventory

Fering (North Frisian, ISO `frr`) has two full paradigms of the definite
article, described by [ebert-1971]: the A-form (*a/at*), the weak article
marking situational uniqueness, and the D-form (*di/det*), the strong
article marking anaphoric reference, including covarying (donkey) uses.

## References

* [ebert-1971]
* [schwarz-2013], §3 and §5.2
-/

namespace Fering.Determiners

/-- The Fering determiners are the weak A-form *a/at* and the strong D-form
    *di/det*. -/
def inventory : Determiner.Inventory :=
  [ .article { form := "a", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.immediateSituation, .largerSituation] },
    .article { form := "di", definiteness := .definite, exponent := .dedicatedMorpheme,
               uses := [.anaphoric, .donkey] } ]

/-- Fering derives the `.bipartite` Moroney cell. -/
theorem marking : inventory.markingStrategy = .bipartite := by decide

end Fering.Determiners
