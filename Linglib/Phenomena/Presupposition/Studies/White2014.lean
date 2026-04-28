import Linglib.Phenomena.Presupposition.Studies.Williams2026
import Linglib.Theories.Semantics.Attitudes.PreExistence
import Linglib.Fragments.English.Predicates.Verbal

/-!
# White 2014: The Modalized Complement Analysis of *forget*
@cite{white-2014}

White 2014 maintains a uniformly factive denotation for *forget* by
positing a covert root modal in non-finite complements (the Modalized
Complement Analysis, MCA). The MCA captures Williams' (1)/(4) and (2)/(5)
data straightforwardly but was later shown to overgenerate: PRO-ing
gerunds get a non-modal presupposition (cf. @cite{williams-2026}, §3.1.1)
that the MCA cannot predict.

This file (a) verifies the MCA's coverage of finite-CP and plain-infinitive
data, (b) records the gerund overprediction as a check against the
empirical record in `Studies/Williams2026.lean`, and (c) confirms
Fragment-level consistency: the English Fragment's split of *forget* into
`forget` (negative implicative, infinitival) and `forget_rog` (factive,
finite) aligns with the typology MCA + pre-existence together predict.

The pre-existence apparatus in `Theories/Semantics/Attitudes/PreExistence.lean`
is post-2014 (Bondarenko 2019/2020, taken up by @cite{williams-2026});
where this file uses `needsModalInsertion`, treat that as the project-canonical
upgrade of White's structural prediction, with the gerund case flagged as
a known overprediction of the original MCA.

-/

namespace Phenomena.Presupposition.Studies.White2014

open Core.Verbs (ComplementType)
open Phenomena.Presupposition.Studies.Williams2026
open Semantics.Attitudes.PreExistence
open Fragments.English.Predicates.Verbal

/-! ## §1. MCA coverage of the canonical contrast

White 2014 was designed to capture the finite-CP / plain-infinitive
asymmetry uniformly. The MCA succeeds on these two cases.
-/

/-- Finite CP: MCA correctly predicts no modal insertion. -/
theorem mca_correct_finiteCP :
    mcaPrediction forget_finiteCP.frame = false := rfl

/-- Plain infinitive: MCA correctly predicts modal insertion. -/
theorem mca_correct_infinitival :
    mcaPrediction forget_infinitival.frame = true := rfl

/-! ## §2. The gerund overprediction

The PRO-ing gerund is non-finite but its presupposition is non-modal
(Williams §3.1.1). The MCA's `mcaPrediction` is `!isFinite`, so it
predicts modal insertion for the gerund — wrong.
-/

/-- The MCA predicts a modal presupposition for the gerund, but the
    Williams 2026 datum is non-modal. -/
theorem mca_overpredicts_gerund :
    mcaPrediction forget_gerund.frame = true ∧
    forget_gerund.content = .nonModal :=
  ⟨rfl, rfl⟩

/-! ## §3. Pre-existence as the post-2014 fix

The pre-existence-based `needsModalInsertion` correctly predicts
non-modal for the gerund. This is post-2014 territory; the theorems
here document the contrast between White's MCA and its successor.
-/

/-- Pre-existence and MCA agree on finite CP and plain infinitive,
    but diverge on gerunds. -/
theorem mca_vs_preExistence_gerund :
    mcaPrediction .gerund ≠ needsModalInsertion .gerund := by decide

/-- Pre-existence prediction matches all three data points. -/
theorem preEx_matches_all_data :
    allForgetJudgments.all
      (fun j => (decide (j.content = .modal)) == needsModalInsertion j.frame) = true := by
  decide

/-- MCA matches two of three data points (loses on the gerund). -/
theorem mca_score :
    (allForgetJudgments.filter
      (fun j => (decide (j.content = .modal)) == mcaPrediction j.frame)).length = 2 := by
  decide

/-! ## §4. Fragment consistency

The English Fragment splits *forget* into two `VerbEntry` records, one
for the implicative use and one for the factive/rogative use. The split
is a practical separation of entailment patterns, not a claim of lexical
ambiguity (which Williams 2026 explicitly rejects). These theorems
document that the Fragment's complement-type and factivity assignments
align with the MCA's predictions, restricted to the cases MCA gets right.
-/

theorem forget_takes_infinitival :
    forget.complementType = .infinitival := by decide

theorem forget_rog_takes_finite :
    forget_rog.complementType = .finiteClause := by decide

theorem forget_rog_is_factive :
    forget_rog.factivePresup = true := by decide

theorem forget_rog_satisfies_preExistence :
    satisfiesPreExistence forget_rog.complementType = true := by decide

theorem forget_inf_violates_preExistence :
    satisfiesPreExistence forget.complementType = false := by decide

end Phenomena.Presupposition.Studies.White2014
