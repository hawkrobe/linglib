import Mathlib.Data.Rat.Defs

/-!
# Modal Concord Data — Dieuleveut, Hsu & Bhatt (2025)

Empirical data from "A Register Approach to Modal Non-Concord in English:
An Experimental Study of Linguistic and Social Meaning."

## Key finding

Stacked necessity modals (*must have to VP*) yield a single-necessity reading
(concord), not the compositionally expected double-necessity. The stacked form
receives intermediate formality ratings (between *must* and *have to*) and
carries social meaning (perceived as less educated, non-standard dialect).

## Experiments

* **Experiment 1** (n=76): Formality and meaning strength ratings on a 7-point
  Likert scale for three conditions: *must VP*, *have to VP*, *must have to VP*.
* **Experiment 2** (n=89): Social meaning ratings (educated, standard dialect,
  friendly, attractive) for speakers of each condition.

## Reference

Dieuleveut, A., Hsu, B., & Bhatt, R. (2025). A Register Approach to Modal
Non-Concord in English: An Experimental Study of Linguistic and Social Meaning.
-/

namespace Phenomena.ModalConcord

/-- Experimental conditions: the three modal constructions under study. -/
inductive Condition where
  | must          -- "Students must take four classes"
  | haveTo        -- "Students have to take four classes"
  | mustHaveTo    -- "Students must have to take four classes" (concord)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Dimensions of social meaning measured in Experiment 2. -/
inductive SocialDimension where
  | educated        -- "How educated does the speaker sound?"
  | standardDialect -- "Does the speaker speak a standard dialect?"
  | friendly        -- "How friendly does the speaker sound?"
  | attractive      -- "How attractive does the speaker sound?"
  deriving DecidableEq, BEq, Repr

/-- A Likert-scale rating (mean on a 7-point scale). -/
structure LikertRating where
  mean : ℚ
  sd : ℚ
  deriving Repr

/-! ## Experiment 1: Formality and Meaning Strength

76 native English speakers rated sentences on 7-point Likert scales for
formality and meaning strength (paraphrase matching with *have to*). -/

/-- Experiment 1 formality ratings (7-point Likert, 1=very informal, 7=very formal).
    F(2, 140.09) = 54.0, p < .001. All pairwise comparisons significant
    after Bonferroni correction. -/
def formalityRating : Condition → LikertRating
  | .must        => ⟨478/100, 124/100⟩  -- M=4.78, SD=1.24
  | .haveTo      => ⟨362/100, 120/100⟩  -- M=3.62, SD=1.20
  | .mustHaveTo  => ⟨413/100, 118/100⟩  -- M=4.13, SD=1.18

/-- Experiment 1 meaning strength ratings (7-point Likert).
    "How well does [*have to* paraphrase] capture the meaning of the sentence?"
    F(2, 140.28) = 6.5, p < .01. Post-hoc: only *have to* vs *must have to*
    significant (p = .003); neither differs reliably from *must*. -/
def meaningRating : Condition → LikertRating
  | .must        => ⟨518/100, 145/100⟩  -- M=5.18, SD=1.45
  | .haveTo      => ⟨543/100, 122/100⟩  -- M=5.43, SD=1.22
  | .mustHaveTo  => ⟨486/100, 156/100⟩  -- M=4.86, SD=1.56

/-! ### Key Experiment 1 empirical generalizations -/

/-- **Formality gradient**: must > must_have_to > have_to.
    All three pairwise comparisons significant after Bonferroni correction. -/
theorem formality_gradient :
    (formalityRating .must).mean > (formalityRating .mustHaveTo).mean ∧
    (formalityRating .mustHaveTo).mean > (formalityRating .haveTo).mean := by
  constructor <;> native_decide

/-- **Intermediate formality**: The stacked form is strictly between the
    two single-modal forms. This is the key prediction of the register
    approach (Dieuleveut, Hsu & Bhatt 2025 §4) and is NOT predicted by
    the syntactic agreement approach (Zeijlstra 2007), which treats one
    modal as semantically vacuous. -/
theorem intermediate_formality :
    (formalityRating .haveTo).mean < (formalityRating .mustHaveTo).mean ∧
    (formalityRating .mustHaveTo).mean < (formalityRating .must).mean := by
  constructor <;> native_decide

/-- **Meaning strength comparable**: All three conditions receive high
    meaning ratings (above scale midpoint 4), indicating concord (single
    necessity) rather than double necessity. -/
theorem meaning_above_midpoint :
    (meaningRating .must).mean > 4 ∧
    (meaningRating .haveTo).mean > 4 ∧
    (meaningRating .mustHaveTo).mean > 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **No reliable meaning difference between must and must_have_to**:
    Post-hoc comparison not significant. The concord reading (single
    necessity) is the dominant interpretation. -/
theorem meaning_must_close_to_mustHaveTo :
    (meaningRating .must).mean - (meaningRating .mustHaveTo).mean < 1/2 := by
  native_decide

/-! ## Experiment 2: Social Meaning

89 native English speakers rated the *speaker* (not the sentence) on four
social dimensions after hearing sentences in each condition. -/

/-- Experiment 2 social meaning ratings (7-point Likert).

    **Significant effects**:
    * Educated: F(2, 175.22) = 5.0, p = .008
    * Standard dialect: F(2, 175.20) = 12.32, p < .001

    **Non-significant effects**:
    * Friendly: F(2, 174.96) = 2.1, p = .13
    * Attractive: F(2, 175.23) = 1.2, p = .30 -/
def socialRating : Condition → SocialDimension → LikertRating
  -- Educated: must speakers perceived as most educated
  | .must,        .educated        => ⟨490/100, 112/100⟩  -- M=4.90, SD=1.12
  | .haveTo,      .educated        => ⟨449/100, 116/100⟩  -- M=4.49, SD=1.16
  | .mustHaveTo,  .educated        => ⟨429/100, 138/100⟩  -- M=4.29, SD=1.38
  -- Standard dialect: must speakers perceived as most standard
  | .must,        .standardDialect => ⟨462/100, 127/100⟩  -- M=4.62, SD=1.27
  | .haveTo,      .standardDialect => ⟨398/100, 137/100⟩  -- M=3.98, SD=1.37
  | .mustHaveTo,  .standardDialect => ⟨361/100, 152/100⟩  -- M=3.61, SD=1.52
  -- Friendly: no significant effect of condition
  | _,            .friendly        => ⟨442/100, 107/100⟩  -- grand mean ≈ 4.42
  -- Attractive: no significant effect of condition
  | _,            .attractive      => ⟨377/100, 112/100⟩  -- grand mean ≈ 3.77

/-! ### Key Experiment 2 empirical generalizations -/

/-- **Education effect**: *must* speakers perceived as more educated than
    *must have to* speakers. Post-hoc: must vs must_have_to significant. -/
theorem education_must_gt_mustHaveTo :
    (socialRating .must .educated).mean >
    (socialRating .mustHaveTo .educated).mean := by native_decide

/-- **Dialect standardness gradient**: must > have_to > must_have_to.
    Post-hoc: must vs have_to and must vs must_have_to both significant. -/
theorem dialect_gradient :
    (socialRating .must .standardDialect).mean >
    (socialRating .haveTo .standardDialect).mean ∧
    (socialRating .haveTo .standardDialect).mean >
    (socialRating .mustHaveTo .standardDialect).mean := by
  constructor <;> native_decide

/-- **Social meaning is selective**: Education and dialect show effects
    (> 0.4 point spread), while friendliness and attractiveness do not.
    Register mixing affects perceived *competence*, not *warmth*. -/
theorem social_meaning_selective :
    -- Competence dimensions: must > must_have_to spread > 0.4 points
    (socialRating .must .educated).mean -
    (socialRating .mustHaveTo .educated).mean > 4/10 ∧
    (socialRating .must .standardDialect).mean -
    (socialRating .mustHaveTo .standardDialect).mean > 4/10 := by
  constructor <;> native_decide

/-! ## Cross-cutting empirical generalizations -/

/-- **Concord with social cost**: *must have to* preserves the meaning
    of single-modal necessity (comparable meaning ratings) while incurring
    a social cost (lower education and dialect ratings). -/
theorem concord_with_social_cost :
    -- Meaning is preserved (within 0.5 of must)
    (meaningRating .must).mean - (meaningRating .mustHaveTo).mean < 1/2 ∧
    -- But social cost is real (education and dialect drop)
    (socialRating .must .educated).mean >
    (socialRating .mustHaveTo .educated).mean ∧
    (socialRating .must .standardDialect).mean >
    (socialRating .mustHaveTo .standardDialect).mean := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

end Phenomena.ModalConcord
