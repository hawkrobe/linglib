import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NormNum

/-!
# Ochs (1992): Indexing Gender

This file formalizes the model of indirect indexicality in [ochs-1992]. Few features of
language index gender directly and exclusively; linguistic forms directly index stances,
acts, and activities, and these in turn help to constitute gender, so the relation of
language to gender is non-exclusive, constitutive, and mediated. The Japanese sentence-final
particles of [uyeno-1971] are the running example: *ze* directly indexes coarse intensity
and *wa* delicate intensity, and the affective dispositions so indexed are part of the
preferred images of men and women. The two steps are association fields, from form to stance
(`formStance`) and from stance to gender (`stanceGender`), and the indirect form–gender
association is their product (`composed`), an index of the second order in the sense of
[silverstein-2003]. *ze* indexes masculinity more than femininity and *wa* the reverse, through
the stances alone, and both particles carry a positive association with both genders, the
non-exclusivity that follows from every stance being available to both sexes.

## Implementation notes

The form-to-stance map is categorical and the stance-to-gender strengths are illustrative
proportions with a positive floor; the argument rests on the composition, not on the
numbers. The third property of the chapter, that the relation is temporally transcendent,
is not represented.

## References

* [ochs-1992]
* [uyeno-1971]
* [silverstein-1976]
* [silverstein-2003]
* [eckert-2008]
* [west-zimmerman-1987]
-/

namespace Ochs1992

open SocialMeaning

/-- The two interactional stances of the chapter's example are coarse intensity, the rough
forceful style, and delicate intensity, the gentle refined one. -/
inductive Stance where
  | coarse
  | delicate
  deriving DecidableEq

instance : Fintype Stance := ⟨{.coarse, .delicate}, λ s => by cases s <;> simp⟩

/-- The poles of the social gender dimension ([west-zimmerman-1987]). -/
inductive GenderPole where
  | masculine
  | feminine
  deriving DecidableEq

/-- The two sentence-final particles, *ze*, coarse, and *wa*, delicate. -/
inductive SFP where
  | ze
  | wa
  deriving DecidableEq

/-- The direct index has each particle index exactly one stance. -/
def formStance : AssociationField SFP Stance ℚ := .of λ
  | .ze, .coarse => 1
  | .wa, .delicate => 1
  | _, _ => 0

/-- The constitutive relation makes coarse intensity part of the preferred image of men and
delicate intensity of women, each stance keeping a positive association with both poles since
both sexes use both. -/
def stanceGender : AssociationField Stance GenderPole ℚ := .of λ
  | .coarse, .masculine => 3/4
  | .coarse, .feminine => 1/4
  | .delicate, .masculine => 1/4
  | .delicate, .feminine => 3/4

/-- The indirect index of gender by a particle composes the two maps through the stances. -/
def composed : AssociationField SFP GenderPole ℚ := formStance * stanceGender

theorem composed_apply (sfp : SFP) (g : GenderPole) :
    composed sfp g = formStance sfp .coarse * stanceGender .coarse g +
      formStance sfp .delicate * stanceGender .delicate g := by
  simp [composed, Matrix.mul_apply, Finset.univ, Fintype.elems, Finset.sum_insert]

/-- *ze* indexes masculinity more than femininity, mediated by coarse intensity. -/
theorem ze_indexes_masculine : composed .ze .feminine < composed .ze .masculine := by
  norm_num [composed_apply, formStance, stanceGender]

/-- *wa* indexes femininity more than masculinity, mediated by delicate intensity. -/
theorem wa_indexes_feminine : composed .wa .masculine < composed .wa .feminine := by
  norm_num [composed_apply, formStance, stanceGender]

/-- Every particle indexes both poles, since every stance does and every particle indexes a
stance, the non-exclusivity of the relation. -/
theorem indexes_all (sfp : SFP) (g : GenderPole) : composed.Indexes sfp g := by
  cases sfp <;> cases g <;> norm_num [AssociationField.Indexes, composed_apply, formStance,
    stanceGender]

/-- The two particles contrast on each pole. -/
theorem composed_ze_ne_wa (g : GenderPole) : composed .ze g ≠ composed .wa g := by
  cases g <;> norm_num [composed_apply, formStance, stanceGender]

end Ochs1992
