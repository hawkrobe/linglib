module

public import Linglib.Morphology.DistributedMorphology.Categorizer.Basic

/-!
# Gender on the nominal categorizer

This file defines the gender features of the nominal categorizer n in Distributed Morphology. A
gender feature is a binary dimension such as [±FEM] with a sign, and it is interpretable for
natural gender and uninterpretable for arbitrary gender. A categorizing head may also bear the
selectional feature {D}, which licenses an inalienable possessor.

## Main definitions

* `GenderValue`: a binary gender dimension with a sign.
* `GenderFeature`: a gender value with its interpretability.
* `Categorizer.Head`: a categorizer with its gender feature and {D}.

## References

* [kramer-2015]
* [adamson-2024]
* [myler-2016]
-/

@[expose] public section

namespace DistributedMorphology

open Minimalist

/-! ### Gender features -/

/-- A binary gender dimension. -/
inductive GenderDimension where
  /-- [±FEM], as in Amharic, Spanish and Maa. -/
  | fem
  /-- [±MASC], as in Jarawara. -/
  | masc
  /-- [±ANIM], as in Lealao Chinantec, Algonquian and Teop. -/
  | anim
  deriving DecidableEq, Repr, Fintype

/-- The sign of a binary feature. -/
inductive GenderValue.Pole where
  | pos
  | neg
  deriving DecidableEq, Repr, Fintype

/-- A valued gender feature is a dimension with a sign, as in [+FEM], [−FEM] and [+ANIM]. -/
structure GenderValue where
  /-- The dimension. -/
  dim : GenderDimension
  /-- The sign. -/
  pole : GenderValue.Pole
  deriving DecidableEq, Repr, Fintype

/-- A gender value together with its interpretability. -/
structure GenderFeature where
  /-- Whether the feature is legible at LF. -/
  interp : Interpretability
  /-- The value. -/
  val : GenderValue
  deriving DecidableEq, Repr

/-! ### Categorizing heads -/

/-- A categorizing head with its gender feature and the selectional feature {D}. These are the
head leaves of `WordStructure Categorizer.Head`. -/
structure Categorizer.Head where
  /-- The categorizer n, v or a. -/
  categorizer : Categorizer
  /-- The gender feature, if any. -/
  gender : Option GenderFeature := none
  /-- The selectional feature {D}. -/
  selectsD : Bool := false
  deriving DecidableEq, Repr

namespace Categorizer.Head

/-- The n bearing the gender feature of interpretability `interp` and value `v`. -/
def gendered (interp : Interpretability) (v : GenderValue) : Categorizer.Head where
  categorizer := .n
  gender := some ⟨interp, v⟩

/-- The n with no gender feature. -/
def n_plain : Categorizer.Head where
  categorizer := .n

/-- The n bearing interpretable [+FEM], the natural feminine. -/
def n_iFem : Categorizer.Head := gendered .interpretable ⟨.fem, .pos⟩

/-- The n bearing interpretable [−FEM], the natural masculine. -/
def n_iMasc : Categorizer.Head := gendered .interpretable ⟨.fem, .neg⟩

/-- The n bearing uninterpretable [+FEM], the arbitrary feminine. -/
def n_uFem : Categorizer.Head := gendered .uninterpretable ⟨.fem, .pos⟩

/-- The n bearing uninterpretable [+ANIM], the nominalizer of Teop body-part roots. -/
def n_uAnim : Categorizer.Head := gendered .uninterpretable ⟨.anim, .pos⟩

end Categorizer.Head

end DistributedMorphology
