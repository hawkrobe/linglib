/-!
# Bantu noun classes

This file defines the types shared by the Bantu noun-class fragments: the semantic cores a
gender may bear, [human], [animal] and [inanimate], or the [non-human] of a two-way system, and
the status of a gender as interpretable, bearing a core, or uninterpretable, purely formal
([carstens-2026]). Each language's fragment pairs its singular and plural classes into genders
([carstens-1991]) and records the status of each gender.

## References

* [carstens-1991]
* [carstens-2026]
-/

namespace Bantu

/-- A semantic core, the salient class of entities a gender is associated with: Xhosa has
[human], [animal] and [inanimate], Shona [human] and [non-human]. -/
inductive SemanticCore where
  | human
  | animal
  | inanimate
  | nonhuman
  deriving DecidableEq, Repr

/-- The status of a gender: interpretable, bearing a semantic core, or uninterpretable, with no
association to a class of entities. -/
inductive GenderStatus where
  | interpretable : SemanticCore → GenderStatus
  | uninterpretable : GenderStatus
  deriving DecidableEq, Repr

/-- The core an interpretable gender bears. -/
def GenderStatus.core : GenderStatus → Option SemanticCore
  | .interpretable c => some c
  | .uninterpretable => none

end Bantu
