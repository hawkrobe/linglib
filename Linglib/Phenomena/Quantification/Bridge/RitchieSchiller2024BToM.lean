import Linglib.Phenomena.Quantification.Studies.RitchieSchiller2024
import Linglib.Theories.Pragmatics.RSA.Core.BToMGrounding
import Linglib.Core.Semantics.CommonGround

/-!
# DDRP–BToM–Common Ground Integration

@cite{ritchie-schiller-2024}

Connects Ritchie & Schiller's (2024) DDRPs to Baker et al.'s (2017) BToM
architecture and Stalnaker's (2002) common ground.

## The Argument

DDRPs currently float free of perception and common ground. This file makes
them a *consequence* of BToM's perception module, constrained by common ground:

1. **Perception-generated DDRPs** (§1): A spatial scene assigns each entity a
   zone. The perception function `perceivable` determines visibility at each
   scale threshold. `sceneToDDRP` converts any scene to a valid DDRP —
   monotonicity follows from transitivity of ≤ on `SpatialScale`.

2. **BToM instantiation** (§2): The existing `RSAConfig.toBToM` bridge gives
   us a BToM model for the domain restriction RSA config. The RSA-BToM bridge
   theorem `L1_eq_btom_worldMarginal` proves L1 IS BToM world-marginal inference.

3. **Common-ground constraint** (§3): Domain restriction works because
   interlocutors share perceptual access (R&S §4). When the scene is common
   ground, speaker and hearer derive the same DDRP.

4. **Perfect-perception collapse** (§4): Under perfect perception, the
   perception-generated DDRP equals the hand-written one, so the RSA model
   uses exactly the DDRP that perception would generate.

5. **Latent classification** (§5): SpatialScale is a mental state (speaker's
   private choice); the scene is shared (perceptual co-presence).

6. **Imperfect perception** (§6): When the hearer has different perceptual
   access, domain restriction can fail — motivating R&S's requirement of
   perceptual co-presence.

## References

- Baker, Jara-Ettinger, Saxe & Tenenbaum (2017). Rational quantitative
  attribution of beliefs, desires and percepts in human mentalizing.
- Clark, H. (1996). Using Language. Cambridge University Press.
- Stalnaker, R. (2002). Common Ground. L&P 25: 701–721.
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Bridge.RitchieSchiller2024BToM

open Semantics.Lexical.Determiner.DomainRestriction
open Phenomena.Quantification.Studies.RitchieSchiller2024
open Core.BToM
open Core.CommonGround

-- ============================================================================
-- §1. Perception-Generated DDRPs
-- ============================================================================

/-- A spatial scene: each entity occupies a spatial zone. -/
def SpatialScene (E : Type*) := E → SpatialScale

/-- Entities perceivable at a given scale threshold: those whose zone ≤ threshold. -/
def perceivable {E : Type*} (scene : SpatialScene E) (threshold : SpatialScale)
    (e : E) : Bool :=
  decide (scene e ≤ threshold)

/-- A spatial scene induces a DDRP. Region s contains entities in zone ≤ s. -/
def sceneToDDRP {E : Type*} (scene : SpatialScene E) : DDRP SpatialScale E where
  region s := perceivable scene s
  monotone {s₁ s₂} h e hr := by
    simp only [perceivable, decide_eq_true_eq] at hr ⊢
    exact le_trans hr h
  top_total e := by
    simp only [perceivable, decide_eq_true_eq]
    exact le_top

/-- The dinner-party scene: b1,b2 peripersonal, b3 action, b4 vista. -/
def dinnerScene : SpatialScene Entity
  | .b1 => .peripersonal
  | .b2 => .peripersonal
  | .b3 => .action
  | .b4 => .vista

/-- `sceneToDDRP dinnerScene` agrees with `sceneDDRP` from RitchieSchiller2024.
    The hand-written DDRP is exactly the perception-generated one. -/
theorem sceneToDDRP_eq_sceneDDRP :
    (sceneToDDRP dinnerScene).region = sceneDDRP.region := by
  funext s e; cases s <;> cases e <;> native_decide

-- ============================================================================
-- §2. BToM Bridge
-- ============================================================================

/-- The RSA-BToM bridge from BToMGrounding applies to the domain restriction
    RSA config, proving that L1 IS BToM world-marginal inference.

    The mapping: Action = Utterance, Percept = Belief = World (perfect
    perception), Desire = SpatialScale (the latent domain restriction),
    Shared = Medium = Unit. See `RSAConfig.toBToM` for the full mapping. -/
theorem rsa_btom_bridge (u : Utterance) (w : World) :
    domainRestrictionRSA.L1agent.score u w =
      (domainRestrictionRSA.toBToM).worldMarginal u w :=
  RSA.RSAConfig.L1_eq_btom_worldMarginal domainRestrictionRSA u w

-- ============================================================================
-- §3. Common-Ground Constraint on DDRPs
-- ============================================================================

/-- The actual scene at each world. In this scenario, the spatial arrangement
    is constant across worlds (only emptiness varies). -/
def actualScene (_w : World) : SpatialScene Entity := dinnerScene

/-- A DDRP is grounded in common ground when the spatial scene is
    common knowledge among discourse participants. -/
def ddprGroundedInCG (scene : SpatialScene Entity) (cg : BContextSet World)
    : Prop :=
  ∀ w, cg w = true → actualScene w = scene

/-- The dinner scene is common ground: all worlds share the same spatial
    arrangement (only bottle emptiness varies, not bottle locations). -/
theorem dinnerScene_is_cg :
    ddprGroundedInCG dinnerScene (λ _ => true) := by
  intro _ _; rfl

/-- When the scene is common ground, speaker and hearer derive the same DDRP. -/
theorem shared_scene_shared_ddrp (scene : SpatialScene Entity)
    (cg : BContextSet World)
    (hcg : ddprGroundedInCG scene cg) :
    ∀ w, cg w = true →
      sceneToDDRP (actualScene w) = sceneToDDRP scene := by
  intro w hw
  exact congrArg sceneToDDRP (hcg w hw)

-- ============================================================================
-- §4. Perfect-Perception Collapse
-- ============================================================================

/-- Under perfect perception with a fixed scene, the perception-generated
    DDRP yields the same truth conditions as the hand-written one.

    This connects to `L1_eq_btom_worldMarginal` from BToMGrounding.lean:
    the existing RSA config collapses to a BToM model with perfect
    perception. Here we verify the additional structure: the perception
    module generates the same DDRP that the RSA model uses directly. -/
theorem perception_generates_rsa_ddrp :
    ∀ (s : SpatialScale) (w : World),
      everyBottleEmpty s w =
        every_restricted bottleModel ((sceneToDDRP dinnerScene).region s)
          isBottle (emptyIn w) := by
  intro s w
  cases s <;> cases w <;> native_decide

-- ============================================================================
-- §5. Latent Classification
-- ============================================================================

/-- SpatialScale (intended domain restriction) is a mental state:
    the speaker's private choice of which spatial zone to restrict to.
    Different speakers at the same dinner party might intend different
    domain restrictions (e.g., one gestures at nearby bottles, another
    at all visible bottles). -/
def scaleCategory : LatentCategory := .mental

/-- The spatial scene is a shared state: perceptual co-presence
    is intersubjective (R&S §3.1, Clark 1996 on joint attention).
    Both speaker and hearer can see which bottles are where. -/
def sceneCategory : LatentCategory := .shared

/-- Scale is correctly classified as mental. -/
theorem scale_is_mental : scaleCategory = LatentCategory.mental := rfl

/-- Scene is correctly classified as shared. -/
theorem scene_is_shared : sceneCategory = LatentCategory.shared := rfl

/-- Full latent classification for the domain restriction model. -/
def ddprClassification : RSA.BToMGrounding.LatentClassification SpatialScale where
  classify _ := .mental
  dynamics _ := .episodic

-- ============================================================================
-- §6. Imperfect Perception
-- ============================================================================

/-- An alternative scene where the hearer cannot see b3 (it's behind a
    partition), so b3 is classified as vista rather than action space. -/
def partitionScene : SpatialScene Entity
  | .b1 => .peripersonal
  | .b2 => .peripersonal
  | .b3 => .vista
  | .b4 => .vista

/-- The two scenes assign b3 to different zones. -/
theorem scenes_differ_on_b3 :
    dinnerScene .b3 ≠ partitionScene .b3 := by native_decide

/-- Different spatial scenes yield different DDRPs.
    Specifically, the action-space region differs between the two scenes:
    dinnerScene includes b3 in action space, partitionScene does not. -/
theorem different_scenes_different_ddrps :
    (sceneToDDRP dinnerScene).region ≠ (sceneToDDRP partitionScene).region := by
  intro h
  exact absurd (congrFun (congrFun h .action) .b3) (by native_decide)

/-- When the hearer's scene differs, they may assign different truth values
    to domain-restricted quantifiers. In w_near (only b1,b2 empty), the
    speaker's scene includes b3 in action space (b3 not empty → false),
    but the hearer's partition scene excludes b3 (only b1,b2 checked → true).
    This demonstrates that without perceptual co-presence, domain-restricted
    quantifiers can receive different truth values. -/
theorem perception_mismatch_changes_truth :
    every_restricted bottleModel ((sceneToDDRP dinnerScene).region .action)
      isBottle (emptyIn .nearEmpty) = false ∧
    every_restricted bottleModel ((sceneToDDRP partitionScene).region .action)
      isBottle (emptyIn .nearEmpty) = true := by
  constructor <;> native_decide

end Phenomena.Quantification.Bridge.RitchieSchiller2024BToM
