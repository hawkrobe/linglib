import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Mathlib.Tactic.NormNum

/-!
# Ochs (1992): Indexing Gender

This file formalizes the model of indirect indexicality in [ochs-1992]. Few features of
language index gender directly and exclusively; linguistic forms directly index stances,
acts, and activities, and these in turn help to constitute gender, so the relation of
language to gender is non-exclusive, constitutive, and mediated. The Japanese sentence-final
particles of [uyeno-1971] are the running example: *ze* directly indexes coarse intensity
and *wa* delicate intensity, and the affective dispositions so indexed are part of the
preferred images of men and women. The two steps are association maps, from form to stance
(`formStanceAssoc`) and from stance to gender (`stanceGenderAssoc`), and the indirect
form–gender association is their composition (`composedAssoc`), a field of the second
indexical order in the sense of [silverstein-2003] (`composedField`). *ze* indexes
masculinity more than femininity and *wa* the reverse, through the stances alone
(`ze_indexes_masculine`, `wa_indexes_feminine`), and both particles carry a positive
association with both genders, the non-exclusivity that follows from every stance being
available to both sexes (`all_nonexclusive`).

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

open SocialMeaning.IndexicalField

/-- The two interactional stances of the chapter's example: coarse intensity, the rough
forceful style, and delicate intensity, the gentle refined one. -/
inductive Stance where
  | coarse
  | delicate
  deriving DecidableEq

/-- The stances, for composition. -/
def Stance.all : List Stance := [.coarse, .delicate]

/-- The poles of the social gender dimension ([west-zimmerman-1987]). -/
inductive GenderPole where
  | masculine
  | feminine
  deriving DecidableEq

/-- The two sentence-final particles: *ze*, coarse, and *wa*, delicate. -/
inductive SFP where
  | ze
  | wa
  deriving DecidableEq

/-- The direct index: each particle indexes exactly one stance. -/
def formStanceAssoc : SFP → Stance → ℚ
  | .ze, .coarse => 1
  | .wa, .delicate => 1
  | _, _ => 0

/-- The constitutive relation: coarse intensity is part of the preferred image of men and
delicate intensity of women, each stance keeping a positive association with both poles
since both sexes use both. -/
def stanceGenderAssoc : Stance → GenderPole → ℚ
  | .coarse, .masculine => 3/4
  | .coarse, .feminine => 1/4
  | .delicate, .masculine => 1/4
  | .delicate, .feminine => 3/4

/-- The indirect index of gender by a particle: the composition of the two maps through
the stances. -/
def composedAssoc (sfp : SFP) (g : GenderPole) : ℚ :=
  composeIndex formStanceAssoc stanceGenderAssoc Stance.all sfp g

/-- *ze* indexes masculinity more than femininity, mediated by coarse intensity. -/
theorem ze_indexes_masculine : composedAssoc .ze .feminine < composedAssoc .ze .masculine := by
  norm_num [composedAssoc, composeIndex, Stance.all, formStanceAssoc, stanceGenderAssoc]

/-- *wa* indexes femininity more than masculinity, mediated by delicate intensity. -/
theorem wa_indexes_feminine : composedAssoc .wa .masculine < composedAssoc .wa .feminine := by
  norm_num [composedAssoc, composeIndex, Stance.all, formStanceAssoc, stanceGenderAssoc]

/-- Non-exclusivity: every particle carries a positive association with both poles, since
every stance does and every particle indexes a stance. -/
theorem all_nonexclusive (sfp : SFP) (g : GenderPole) : 0 < composedAssoc sfp g := by
  cases sfp <;> cases g <;>
    norm_num [composedAssoc, composeIndex, Stance.all, formStanceAssoc, stanceGenderAssoc]

/-- The composed relation as an indexical field of the second order: the particles are
consciously manipulable markers ([silverstein-2003]). -/
def composedField : IndexicalField SFP GenderPole where
  association := composedAssoc
  order := .second

/-- The composed field indexes *ze* toward masculinity and *wa* toward femininity, and the
two particles contrast on each pole. -/
theorem composedField_indexes :
    composedField.indexes .ze .masculine ∧ composedField.indexes .wa .feminine ∧
      composedField.contrasts .ze .wa .masculine := by
  refine ⟨all_nonexclusive .ze .masculine, all_nonexclusive .wa .feminine, ?_⟩
  show composedAssoc .ze .masculine ≠ composedAssoc .wa .masculine
  norm_num [composedAssoc, composeIndex, Stance.all, formStanceAssoc, stanceGenderAssoc]

end Ochs1992
