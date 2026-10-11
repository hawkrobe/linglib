module

public import Linglib.Morphology.DistributedMorphology.Categorizer.Basic
public import Linglib.Syntax.Minimalist.Features
public import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# Gender on the nominal categorizer

This file defines the gender features of the nominal categorizer n in Distributed Morphology. A
gender feature is a binary dimension such as [±FEM] with a sign, and it is interpretable for
natural gender and uninterpretable for arbitrary gender. A categorizing head may also bear the
selectional feature {D}, which licenses an inalienable possessor.

Agreement in gender is a probe relativized to gender, searching the n's of a nominal from the
top; when it finds none, Agree fails and the default gender is spelled out. When several n's are
stacked, Kramer's Highest Gender Hypothesis makes the gender of the highest n the agreeing
gender. On her hierarchical explanation the probe searches every n; on her cyclic explanation
the highest n has sent the lower ones to spell-out, so the probe sees the highest n alone. The
two differ exactly when a plain n tops a gendered one.

## Main definitions

* `GenderValue`: a binary gender dimension with a sign.
* `GenderFeature`: a gender value with its interpretability.
* `Categorizer.Head`: a categorizer with its gender feature and {D}.
* `agreeingGender`: the gender a gender probe agrees in, or the default on failed Agree.

## Main results

* `agreeingGender_take_one`: the cyclic and hierarchical explanations agree when the highest n
  bears a gender.
* `agreeingGender_plain_cons`: they differ on a plain n over a gendered one.

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

/-! ### Agreement in gender -/

section HighestGender

open Minimalist

variable {H G : Type*} (gender : H → Option G) (default : G)

/-- The probe for gender, relativized to the heads that bear one. -/
def genderProbe : Probe H := Probe.relativized fun h ↦ (gender h).isSome

/-- The gender a gender probe agrees in when it searches `goals`, nearest first, or `default`
when Agree fails. -/
def agreeingGender (goals : List H) : G :=
  (((genderProbe gender).search goals).bind gender).getD default

variable {gender default} {h h' : H} {hs : List H} {g : G}

@[simp] theorem agreeingGender_nil : agreeingGender gender default [] = default := rfl

theorem agreeingGender_cons_of_eq_some (hg : gender h = some g) :
    agreeingGender gender default (h :: hs) = g := by
  simp [agreeingGender, genderProbe, Probe.search, hg]

theorem agreeingGender_cons_of_eq_none (hh : gender h = none) :
    agreeingGender gender default (h :: hs) = agreeingGender gender default hs := by
  simp [agreeingGender, genderProbe, Probe.search, hh]

/-- The cyclic explanation, on which the probe sees the highest n alone, agrees with the
hierarchical one when that n bears a gender. -/
theorem agreeingGender_take_one (hg : gender h = some g) :
    agreeingGender gender default ((h :: hs).take 1) = agreeingGender gender default (h :: hs) := by
  simp [agreeingGender_cons_of_eq_some hg]

/-- On a plain n over an n of gender `g`, the cyclic explanation gives the default and the
hierarchical one gives `g`. -/
theorem agreeingGender_plain_cons (hh : gender h = none) (hg : gender h' = some g) :
    agreeingGender gender default ((h :: h' :: hs).take 1) = default ∧
      agreeingGender gender default (h :: h' :: hs) = g := by
  simp [agreeingGender_cons_of_eq_none hh, agreeingGender_cons_of_eq_some hg]

end HighestGender

end DistributedMorphology
