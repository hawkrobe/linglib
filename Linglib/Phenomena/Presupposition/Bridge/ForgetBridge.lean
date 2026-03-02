import Linglib.Phenomena.Presupposition.ForgetPresuppositions
import Linglib.Theories.Semantics.Attitudes.PreExistence
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Forget Bridge: Pre-Existence Theory vs. Empirical Data
@cite{white-2014}

Connects the pre-existence theory (from `PreExistence.lean`) to
empirical data about *forget*'s presuppositions (from
`ForgetPresuppositions.lean`) and to the English verb Fragment.

## What This File Tests

1. **Pre-existence predictions match data** — `needsModalInsertion`
   correctly predicts which frames get modal vs. non-modal presuppositions

2. **MCA overprediction** — the Modalized Complement Analysis
   wrongly predicts a modal presupposition for the gerund case

3. **Fragment consistency** — the two Fragment entries for *forget*
   (implicative and factive/rogative) align with the theory

-/

namespace Phenomena.Presupposition.Bridge.ForgetBridge

open Core.Verbs (ComplementType)
open Phenomena.Presupposition.ForgetPresuppositions
open Semantics.Attitudes.PreExistence
open Fragments.English.Predicates.Verbal

-- ============================================================================
-- §1. Pre-Existence Predictions Match Data
-- ============================================================================

/-! The pre-existence theory predicts: modal presupposition iff the
    complement type does NOT satisfy pre-existence. We verify this
    against each judgment from @cite{ippolito-kiss-williams-2025}. -/

/-- Finite CP: pre-existence satisfied → non-modal presupposition.
    Matches: "forgot that she stopped" presupposes she stopped. -/
theorem preEx_correct_finiteCP :
    needsModalInsertion forget_finiteCP.frame = false ∧
    forget_finiteCP.content = .nonModal :=
  ⟨rfl, rfl⟩

/-- Gerund: pre-existence satisfied → non-modal presupposition.
    Matches: "forgot stopping by" presupposes stopped.
    This is the case that refutes the MCA's overprediction. -/
theorem preEx_correct_gerund :
    needsModalInsertion forget_gerund.frame = false ∧
    forget_gerund.content = .nonModal :=
  ⟨rfl, rfl⟩

/-- Plain infinitive: pre-existence NOT satisfied → modal presupposition.
    Matches: "forgot to stop by" presupposes was supposed to stop. -/
theorem preEx_correct_infinitival :
    needsModalInsertion forget_infinitival.frame = true ∧
    forget_infinitival.content = .modal :=
  ⟨rfl, rfl⟩

/-- Aggregate: the pre-existence theory matches all data points.
    Modal content arises iff modal insertion is needed. -/
theorem preEx_matches_all_data :
    allForgetJudgments.all (λ j =>
      (j.content == .modal) == needsModalInsertion j.frame) = true := by
  native_decide

-- ============================================================================
-- §2. MCA Overprediction
-- ============================================================================

/-! The Modalized Complement Analysis predicts modal
    presuppositions for ALL non-finite complements. This overgenerates
    for gerunds: "forgot stopping by" has a non-modal presupposition. -/

/-- MCA wrongly predicts a modal presupposition for the gerund case. -/
theorem mca_wrong_on_gerund :
    mcaPrediction forget_gerund.frame = true ∧
    forget_gerund.content = .nonModal :=
  ⟨rfl, rfl⟩

/-- MCA correctly handles the finite case. -/
theorem mca_correct_finiteCP :
    mcaPrediction forget_finiteCP.frame = false := rfl

/-- MCA correctly handles the infinitival case. -/
theorem mca_correct_infinitival :
    mcaPrediction forget_infinitival.frame = true := rfl

/-- MCA matches only 2 of 3 data points; pre-existence matches all 3. -/
theorem mca_score :
    (allForgetJudgments.filter (λ j =>
      (j.content == .modal) == mcaPrediction j.frame)).length = 2 := by
  native_decide

theorem preEx_score :
    (allForgetJudgments.filter (λ j =>
      (j.content == .modal) == needsModalInsertion j.frame)).length = 3 := by
  native_decide

-- ============================================================================
-- §3. Fragment Consistency
-- ============================================================================

/-! The English Fragment has two entries for *forget*:
    - `forget` (implicative, infinitival complement): "forgot to VP"
    - `forget_rog` (factive/rogative, finite complement): "forgot that p"

    Un@cite{ippolito-kiss-williams-2025}, these are NOT two distinct lexical items but
    one verb with uniform factivity. The Fragment's split is a practical
    choice: it separates the implicative entailment pattern (forgot to VP
    → didn't VP) from the rogative/factive pattern (forgot that p / forgot
    whether p). Williams's pre-existence analysis explains why these two
    uses surface differently without positing lexical ambiguity. -/

/-- The factive entry (forget_rog) has factivePresup = true. -/
theorem forget_rog_is_factive :
    forget_rog.factivePresup = true := by native_decide

/-- The implicative entry takes infinitival complements. -/
theorem forget_takes_infinitival :
    forget.complementType = .infinitival := by native_decide

/-- The factive entry takes finite complements. -/
theorem forget_rog_takes_finite :
    forget_rog.complementType = .finiteClause := by native_decide

/-- The factive entry's primary complement satisfies pre-existence. -/
theorem forget_rog_satisfies_preExistence :
    satisfiesPreExistence forget_rog.complementType = true := by native_decide

/-- The implicative entry's complement does NOT satisfy pre-existence.
    This is why the modal is inserted, yielding the obligation reading. -/
theorem forget_inf_violates_preExistence :
    satisfiesPreExistence forget.complementType = false := by native_decide

-- ============================================================================
-- §4. isFinite Infrastructure Verification
-- ============================================================================

/-! Basic verification that ComplementType.isFinite classifies correctly.
    These hold independently of any theory of factivity. -/

theorem finiteClause_isFinite : ComplementType.isFinite .finiteClause = true := rfl
theorem question_isFinite : ComplementType.isFinite .question = true := rfl
theorem infinitival_not_finite : ComplementType.isFinite .infinitival = false := rfl
theorem gerund_not_finite : ComplementType.isFinite .gerund = false := rfl

end Phenomena.Presupposition.Bridge.ForgetBridge
