import Linglib.Phenomena.ModalConcord.LiuRotter2025
import Linglib.Fragments.English.FunctionWords

/-!
# Modal Concord Bridge — Liu & Rotter (2025)

Connects Liu & Rotter's empirical data to the English modal and adverb
fragments and to Dieuleveut, Hsu & Bhatt (2025).

## Section A: Semantic overlap

Each experimental aux-adverb pair shares modal force in the force-flavor
space. This is the structural precondition for concord.

## Section B: Force determines commitment direction

The paper's FORCE × NUMBER interaction can be predicted from modal force:
necessity doubling strengthens, possibility doubling weakens.

## Section C: Connection to Dieuleveut et al. (2025)

Both studies find that MC preserves modal force (single reading, not double).
Dieuleveut et al. shows intermediate formality; Liu & Rotter adds the
commitment and social meaning dimensions.

## References

* Liu & Rotter (2025). Non-redundant modal concord.
* Dieuleveut, Hsu & Bhatt (2025). A Register Approach to Modal Non-Concord.
-/

namespace Phenomena.ModalConcord.LiuRotter2025.Bridge

open Phenomena.ModalConcord.LiuRotter2025
open Fragments.English.FunctionWords
open Core.ModalLogic (ModalForce ForceFlavor)

/-! ## Section A: Semantic overlap

Each aux-adverb pair from the stimuli shares at least one ForceFlavor
with the same force. This is the precondition for concord: two
expressions must "agree" on force to undergo modal doubling. -/

/-- Shared force between two modal meanings: at least one ForceFlavor
    with matching force appears in both. -/
def shareForce (m1 m2 : List ForceFlavor) : Bool :=
  m1.any fun ff1 => m2.any fun ff2 => ff1.force == ff2.force

-- Necessity pairs

/-- *must* + *certainly* share necessity force. -/
theorem must_certainly_share :
    shareForce must.modalMeaning certainly.modalMeaning = true := by native_decide

/-- *should* + *definitely* share necessity force. -/
theorem should_definitely_share :
    shareForce should.modalMeaning definitely.modalMeaning = true := by native_decide

/-- *have to* + *necessarily* share necessity force. -/
theorem haveTo_necessarily_share :
    shareForce haveTo.modalMeaning necessarily.modalMeaning = true := by native_decide

-- Possibility pairs

/-- *may* + *possibly* share possibility force. -/
theorem may_possibly_share :
    shareForce may.modalMeaning possibly.modalMeaning = true := by native_decide

/-- *might* + *perhaps* share possibility force. -/
theorem might_perhaps_share :
    shareForce might.modalMeaning perhaps.modalMeaning = true := by native_decide

/-- *could* + *potentially* share possibility force. -/
theorem could_potentially_share :
    shareForce could.modalMeaning potentially.modalMeaning = true := by native_decide

/-- **All six stimulus pairs share force**: Every aux-adverb pairing
    in the experiment satisfies the shared-force precondition. -/
theorem all_pairs_share_force :
    shareForce must.modalMeaning certainly.modalMeaning = true ∧
    shareForce should.modalMeaning definitely.modalMeaning = true ∧
    shareForce haveTo.modalMeaning necessarily.modalMeaning = true ∧
    shareForce may.modalMeaning possibly.modalMeaning = true ∧
    shareForce might.modalMeaning perhaps.modalMeaning = true ∧
    shareForce could.modalMeaning potentially.modalMeaning = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## Section B: Force determines commitment direction

The paper's central finding — that necessity MC strengthens while
possibility MC weakens — can be encoded as a function from modal
force to predicted direction. -/

/-- Predicted commitment effect of concord given modal force.
    `true` = strengthening (MC > SM), `false` = weakening (MC < SM). -/
def concordStrengthens : ModalForce → Bool
  | .necessity  => true
  | .possibility => false

/-- The data matches the force-based prediction for necessity:
    necessity MC has higher commitment than necessity SM. -/
theorem necessity_matches_prediction :
    concordStrengthens .necessity = true ∧
    (commitmentRating necMC).mean > (commitmentRating necSM).mean :=
  ⟨rfl, necessity_mc_strengthens⟩

/-- The data matches the force-based prediction for possibility:
    possibility MC has lower commitment than possibility SM. -/
theorem possibility_matches_prediction :
    concordStrengthens .possibility = false ∧
    (commitmentRating posMC).mean < (commitmentRating posSM).mean :=
  ⟨rfl, possibility_mc_weakens⟩

/-! ## Section C: Connection to Dieuleveut et al. (2025)

Both studies agree that MC preserves modal force (single reading).
Dieuleveut et al. (necessity only): *must have to* has intermediate
formality and comparable meaning ratings to bare *must*.
Liu & Rotter: extends to possibility, adds commitment + social meaning. -/

/-- Both studies agree: necessity MC does not yield double necessity.
    Dieuleveut: *must have to* meaning close to *must* (within 0.5).
    Liu & Rotter: necessity MC commitment above midpoint. -/
theorem both_studies_single_necessity :
    -- Dieuleveut: must_have_to meaning close to must
    (Phenomena.ModalConcord.meaningRating .must).mean -
    (Phenomena.ModalConcord.meaningRating .mustHaveTo).mean < 1/2 ∧
    -- Liu & Rotter: necessity MC above midpoint (single necessity)
    (commitmentRating necMC).mean > 4 := by
  constructor <;> native_decide

/-- **Register and commitment are complementary diagnostics.**
    Dieuleveut et al. finds MC has intermediate formality (register mixing).
    Liu & Rotter finds MC shifts commitment (non-vacuous doubling).
    Together: MC is neither purely register-driven nor purely semantic —
    it has both a register signature and a commitment signature. -/
theorem complementary_diagnostics :
    -- Dieuleveut: intermediate formality (register effect exists)
    (Phenomena.ModalConcord.formalityRating .haveTo).mean <
    (Phenomena.ModalConcord.formalityRating .mustHaveTo).mean ∧
    -- Liu & Rotter: commitment shift (semantic effect exists)
    (commitmentRating necMC).mean ≠ (commitmentRating necSM).mean := by
  constructor <;> native_decide

end Phenomena.ModalConcord.LiuRotter2025.Bridge
