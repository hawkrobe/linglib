import Linglib.Phenomena.ModalConcord.LiuRotter2025
import Linglib.Fragments.English.FunctionWords

/-!
# Modal Concord Bridge — Liu & Rotter (2025)

Connects Liu & Rotter's empirical data to the English modal and adverb
fragments, the general concord infrastructure, and Dieuleveut, Hsu &
Bhatt (2025).

## Section A: Semantic overlap via ModalItem

Each experimental aux-adverb pair shares modal force when projected to
the shared `ModalItem` type. This is the structural precondition for concord.

## Section B: Force determines commitment direction

The paper's FORCE × NUMBER interaction can be predicted from modal force:
necessity doubling strengthens, possibility doubling weakens.

## Section C: Connection to Dieuleveut et al. (2025)

Both studies find that MC preserves modal force (single reading, not double).

## Section D: Cross-phenomenon concord

Modal concord is an instance of the general concord pattern. Possibility MC
patterns with negative concord (solidarity), necessity MC contrasts (competence).

## References

* Liu & Rotter (2025). Non-redundant modal concord.
* Dieuleveut, Hsu & Bhatt (2025). A Register Approach to Modal Non-Concord.
* Zeijlstra (2004). Sentential Negation and Negative Concord.
* Fiske, Cuddy, Glick & Xu (2002). A model of (often mixed) stereotype content.
-/

namespace Phenomena.ModalConcord.LiuRotter2025.Bridge

open Phenomena.ModalConcord.LiuRotter2025
open Fragments.English.FunctionWords
open Core.ModalLogic (ModalForce ModalItem ConcordType)
open Core.Register (SocialIndex)

/-! ## Section A: Semantic overlap via ModalItem

Each aux-adverb pair from the stimuli shares force when projected to
`ModalItem`. The `sharesForce` operation lives in `Core/ModalLogic.lean`
and works generically across any modal items. -/

-- Necessity pairs

/-- *must* + *certainly* share necessity force. -/
theorem must_certainly_share :
    must.toModalItem.sharesForce certainly.toModalItem = true := by native_decide

/-- *should* + *definitely* share necessity force. -/
theorem should_definitely_share :
    should.toModalItem.sharesForce definitely.toModalItem = true := by native_decide

/-- *have to* + *necessarily* share necessity force. -/
theorem haveTo_necessarily_share :
    haveTo.toModalItem.sharesForce necessarily.toModalItem = true := by native_decide

-- Possibility pairs

/-- *may* + *possibly* share possibility force. -/
theorem may_possibly_share :
    may.toModalItem.sharesForce possibly.toModalItem = true := by native_decide

/-- *might* + *perhaps* share possibility force. -/
theorem might_perhaps_share :
    might.toModalItem.sharesForce perhaps.toModalItem = true := by native_decide

/-- *could* + *potentially* share possibility force. -/
theorem could_potentially_share :
    could.toModalItem.sharesForce potentially.toModalItem = true := by native_decide

/-- **All six stimulus pairs share force**. -/
theorem all_pairs_share_force :
    must.toModalItem.sharesForce certainly.toModalItem = true ∧
    should.toModalItem.sharesForce definitely.toModalItem = true ∧
    haveTo.toModalItem.sharesForce necessarily.toModalItem = true ∧
    may.toModalItem.sharesForce possibly.toModalItem = true ∧
    might.toModalItem.sharesForce perhaps.toModalItem = true ∧
    could.toModalItem.sharesForce potentially.toModalItem = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- Register variants

/-- *must* (formal) and *certainly* (formal) are NOT register variants —
    they share the same register level. Concord here is not register mixing
    but force agreement between syntactically distinct categories. -/
theorem must_certainly_same_register :
    must.toModalItem.areRegisterVariants certainly.toModalItem = false := by native_decide

/-- *may* (neutral) and *possibly* (neutral) are also not register variants. -/
theorem may_possibly_same_register :
    may.toModalItem.areRegisterVariants possibly.toModalItem = false := by native_decide

/-! ## Section B: Force determines commitment direction

The paper's central finding — that necessity MC strengthens while
possibility MC weakens — can be encoded as a function from modal
force to predicted direction. -/

/-- Predicted commitment effect of concord given modal force.
    `true` = strengthening (MC > SM), `false` = weakening (MC < SM). -/
def concordStrengthens : ModalForce → Bool
  | .necessity  => true
  | .possibility => false

/-- The data matches the force-based prediction for necessity. -/
theorem necessity_matches_prediction :
    concordStrengthens .necessity = true ∧
    (commitmentRating necMC).mean > (commitmentRating necSM).mean :=
  ⟨rfl, necessity_mc_strengthens⟩

/-- The data matches the force-based prediction for possibility. -/
theorem possibility_matches_prediction :
    concordStrengthens .possibility = false ∧
    (commitmentRating posMC).mean < (commitmentRating posSM).mean :=
  ⟨rfl, possibility_mc_weakens⟩

/-! ## Section C: Connection to Dieuleveut et al. (2025)

Both studies agree that MC preserves modal force (single reading). -/

/-- Both studies: necessity MC yields single necessity. -/
theorem both_studies_single_necessity :
    (Phenomena.ModalConcord.meaningRating .must).mean -
    (Phenomena.ModalConcord.meaningRating .mustHaveTo).mean < 1/2 ∧
    (commitmentRating necMC).mean > 4 := by
  constructor <;> native_decide

/-- Register and commitment are complementary diagnostics. -/
theorem complementary_diagnostics :
    (Phenomena.ModalConcord.formalityRating .haveTo).mean <
    (Phenomena.ModalConcord.formalityRating .mustHaveTo).mean ∧
    (commitmentRating necMC).mean ≠ (commitmentRating necSM).mean := by
  constructor <;> native_decide

/-! ## Section D: Cross-phenomenon concord

Modal concord is an instance of the general `ConcordType` from
`Core/ModalLogic.lean`. The social indexation of MC depends on force:
necessity MC → competence, possibility MC → solidarity. This connects
to negative concord, which also indexes solidarity.

The `socialIndex` mapping is defined here (not in Core) because it
encodes an empirical claim from Liu & Rotter (2025) §4. -/

/-- Social indexation of each concord type.
    NC and MC possibility both index solidarity;
    MC necessity indexes competence (Liu & Rotter 2025 §4). -/
def socialIndex : ConcordType → SocialIndex
  | .negation         => .solidarity
  | .modalNecessity   => .competence
  | .modalPossibility => .solidarity

/-- Necessity MC is a competence-indexing concord phenomenon. -/
theorem necessity_mc_competence :
    socialIndex (ConcordType.fromModalForce .necessity) = .competence := rfl

/-- Possibility MC is a solidarity-indexing concord phenomenon. -/
theorem possibility_mc_solidarity :
    socialIndex (ConcordType.fromModalForce .possibility) = .solidarity := rfl

/-- **Possibility MC patterns with negative concord**: Both are
    solidarity-indexing concord phenomena. This is the cross-phenomenon
    generalization from Liu & Rotter (2025) §4. -/
theorem possibility_mc_like_nc :
    socialIndex (ConcordType.fromModalForce .possibility) =
    socialIndex .negation := rfl

/-- **Necessity MC contrasts with negative concord**. -/
theorem necessity_mc_unlike_nc :
    socialIndex (ConcordType.fromModalForce .necessity) ≠
    socialIndex .negation := by decide

/-- **Force determines social meaning**: Necessity and possibility
    modal concord receive opposite social indexation. -/
theorem force_determines_social_index :
    socialIndex .modalNecessity ≠
    socialIndex .modalPossibility := by decide

/-- **Social meaning mirrors commitment direction**: The concord type's
    social index aligns with the commitment data — competence-indexing
    necessity MC strengthens commitment, solidarity-indexing possibility
    MC weakens it. -/
theorem social_index_aligns_with_commitment :
    -- Necessity: competence index + strengthening
    socialIndex (ConcordType.fromModalForce .necessity) = .competence ∧
    (commitmentRating necMC).mean > (commitmentRating necSM).mean ∧
    -- Possibility: solidarity index + weakening
    socialIndex (ConcordType.fromModalForce .possibility) = .solidarity ∧
    (commitmentRating posMC).mean < (commitmentRating posSM).mean := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> native_decide

end Phenomena.ModalConcord.LiuRotter2025.Bridge
