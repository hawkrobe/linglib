import Linglib.Fragments.English.Auxiliaries
import Linglib.Features.Register
import Linglib.Semantics.Modality.Typology
import Mathlib.Data.Rat.Defs

/-!
# Modal Concord — Register Approach
[rotter-liu-2025] [van-de-pol-etal-2023] [zeijlstra-2007]

Experimental data and analysis from "A Register Approach to Modal
Non-Concord in English: An Experimental Study of Linguistic and Social
Meaning" [rotter-liu-2025].

Stacked necessity modals (*must have to VP*) yield a single-necessity
reading (concord), not the compositionally expected double-necessity. The
stacked form receives intermediate formality ratings (between *must* and
*have to*) and carries social meaning (perceived as less educated,
non-standard dialect).

* **Experiment 1** (n=76): formality and meaning-strength ratings (7-point
  Likert) for *must VP*, *have to VP*, *must have to VP*.
* **Experiment 2** (n=89): social meaning ratings (educated, standard
  dialect, friendly, attractive) for speakers of each condition.
* **Section A**: *must* and *have to* share deontic necessity in the
  force-flavor space — the precondition for concord.
* **Section B**: *must* and *have to* are register variants (same modal
  meaning, different register level), derived from the fragment's
  `AuxEntry.register` field.
* **Section C**: the register approach predicts intermediate formality for
  the stacked form; the syntactic agreement approach does not. The data
  confirms the register approach.
* **Section D**: connection to modal typology — IFF-satisfying necessity
  modals are natural concord candidates.
-/

namespace RotterLiu2025Concord

open English.Auxiliaries
open Semantics.Modality (ModalForce ModalFlavor ForceFlavor)
open Features.Register (Level areVariants)
open Semantics.Modality.Typology (satisfiesIFF satisfiesSAV)

/-! ## Experimental conditions and measures -/

/-- Experimental conditions: the three modal constructions under study. -/
inductive Condition where
  | must          -- "Students must take four classes"
  | haveTo        -- "Students have to take four classes"
  | mustHaveTo    -- "Students must have to take four classes" (concord)
  deriving DecidableEq, Repr, Inhabited

/-- Dimensions of social meaning measured in Experiment 2. -/
inductive SocialDimension where
  | educated        -- "How educated does the speaker sound?"
  | standardDialect -- "Does the speaker speak a standard dialect?"
  | friendly        -- "How friendly does the speaker sound?"
  | attractive      -- "How attractive does the speaker sound?"
  deriving DecidableEq, Repr

/-- A Likert-scale rating (mean on a 7-point scale). -/
structure LikertRating where
  mean : ℚ
  sd : ℚ
  deriving Repr

/-! ## Experiment 1: formality and meaning strength

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

/-- **Formality gradient**: must > must_have_to > have_to.
    All three pairwise comparisons significant after Bonferroni correction. -/
theorem formality_gradient :
    (formalityRating .must).mean > (formalityRating .mustHaveTo).mean ∧
    (formalityRating .mustHaveTo).mean > (formalityRating .haveTo).mean := by
  constructor <;> native_decide

/-- **Intermediate formality**: The stacked form is strictly between the
    two single-modal forms. This is the key prediction of the register
    approach ([rotter-liu-2025] §4) and is NOT predicted by
    the syntactic agreement approach, which treats one
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

/-! ## Experiment 2: social meaning

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

/-! ## Section A: Semantic equivalence in the fragment -/

/-- Deontic necessity: the force-flavor pair ⟨necessity, deontic⟩. -/
private abbrev deoNec := ForceFlavor.mk .necessity .deontic

/-- *Must* expresses deontic necessity (from the English fragment). -/
theorem must_has_deontic_necessity :
    must.modalMeaning.contains deoNec = true := by native_decide

/-- *Have to* expresses deontic necessity (from the English fragment). -/
theorem haveTo_has_deontic_necessity :
    haveTo.modalMeaning.contains deoNec = true := by native_decide

/-- **Semantic overlap**: *must* and *have to* share deontic necessity.
    This shared meaning is the precondition for concord — two forms can
    only undergo concord if they express the same modal meaning. -/
theorem shared_deontic_necessity :
    must.modalMeaning.contains deoNec = true ∧
    haveTo.modalMeaning.contains deoNec = true := by
  constructor <;> native_decide

/-- *Have to* has the same deontic-circumstantial meaning as *must*
    restricted to the non-epistemic flavors. Both express necessity
    over deontic and circumstantial domains. -/
theorem haveTo_meaning_subset_of_must :
    haveTo.modalMeaning.all (must.modalMeaning.contains ·) = true := by native_decide

/-- Both *must* and *have to* satisfy IFF (Independence of Force and Flavor).
    Their meanings are Cartesian products of forces and flavors. -/
theorem both_satisfy_iff :
    satisfiesIFF must.modalMeaning = true ∧
    satisfiesIFF haveTo.modalMeaning = true := by
  constructor <;> native_decide

/-- Both satisfy SAV (Single Axis of Variability): they vary on flavor
    only, with fixed necessity force. -/
theorem both_satisfy_sav :
    satisfiesSAV must.modalMeaning = true ∧
    satisfiesSAV haveTo.modalMeaning = true := by
  constructor <;> native_decide

/-! ## Section B: Register variants

Register properties are derived directly from the fragment's `AuxEntry.register`
field, which uses `Features.Register.Level` (formal/neutral/informal). -/

/-- *Must* is marked formal in the fragment. -/
theorem must_is_formal : must.register = Level.formal := rfl

/-- *Have to* is marked informal in the fragment. -/
theorem haveTo_is_informal : haveTo.register = Level.informal := rfl

/-- **Register opposition**: *must* and *have to* are register variants —
    they differ in register level. Derived from the fragment entries. -/
theorem register_opposition : areVariants must.register haveTo.register := by decide

/-- **Register ordering**: *have to* < *must* on the formality scale
    (informal < formal). -/
theorem register_ordering : haveTo.register < must.register := by decide

/-- **Shared deontic core**: Both register variants express deontic necessity.
    Same modal meaning, different register. -/
theorem shared_deontic_core :
    must.modalMeaning.contains deoNec = true ∧
    haveTo.modalMeaning.contains deoNec = true := by
  constructor <;> native_decide

/-! ## Section C: Competing predictions

Two theories of modal concord make different predictions about the
formality of stacked modals:

**Register approach**:
- *Must* and *have to* are register variants of the same meaning
- Stacking creates a "split register" construction
- **Prediction**: intermediate formality (between *must* and *have to*)

**Syntactic agreement**:
- One modal carries interpretable [iNec], the other uninterpretable [uNec]
- The [uNec] modal is semantically vacuous (like negative concord)
- **Prediction**: formality of stacked form = formality of single form
  (the vacuous modal contributes nothing)
-/

/-- **Register prediction confirmed**: The empirical formality rating
    of *must have to* is strictly between *must* and *have to*.
    This is the register approach's central prediction ([rotter-liu-2025] §4):
    mixing a formal variant with an informal variant yields intermediate
    formality. -/
theorem register_prediction_confirmed :
    (formalityRating .haveTo).mean < (formalityRating .mustHaveTo).mean ∧
    (formalityRating .mustHaveTo).mean < (formalityRating .must).mean :=
  intermediate_formality

/-- **Syntactic agreement prediction refuted (vs must)**: If *have to*
    were semantically vacuous [uNec], *must have to* should be as formal
    as bare *must*. It is not. -/
theorem agreement_refuted_vs_must :
    (formalityRating .mustHaveTo).mean ≠ (formalityRating .must).mean := by
  native_decide

/-- **Syntactic agreement prediction refuted (vs have to)**: If *must*
    were semantically vacuous [uNec], *must have to* should be as formal
    as bare *have to*. It is not. -/
theorem agreement_refuted_vs_haveTo :
    (formalityRating .mustHaveTo).mean ≠ (formalityRating .haveTo).mean := by
  native_decide

/-- **Concord preserves modal force**: The meaning ratings for all three
    conditions are above midpoint and close to each other, confirming
    that *must have to VP* expresses single necessity (concord), not
    double necessity. If the stacked form expressed □□p, the meaning
    rating (paraphrase match with *have to*) should be much lower. -/
theorem concord_preserves_force :
    ((meaningRating .must).mean > 4 ∧
     (meaningRating .haveTo).mean > 4 ∧
     (meaningRating .mustHaveTo).mean > 4) ∧
    (meaningRating .must).mean - (meaningRating .mustHaveTo).mean < 1/2 :=
  ⟨meaning_above_midpoint, meaning_must_close_to_mustHaveTo⟩

/-! ## Section D: Connection to modal typology

Modal concord only arises between forms with overlapping force-flavor
meanings. The IFF universal
predicts that natural-language modals have Cartesian-product meanings.
Since Cartesian products with the same force axis share all force-flavor
pairs, IFF-satisfying necessity modals are natural concord candidates. -/

/-- The deontic necessity overlap between *must* and *have to* is
    non-accidental: both are IFF-satisfying necessity modals. Any two
    IFF modals with singleton force {necessity} and overlapping flavor
    sets share deontic necessity whenever both express it. -/
theorem iff_enables_concord :
    satisfiesIFF must.modalMeaning = true ∧
    satisfiesIFF haveTo.modalMeaning = true ∧
    must.modalMeaning.contains deoNec = true ∧
    haveTo.modalMeaning.contains deoNec = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end RotterLiu2025Concord
