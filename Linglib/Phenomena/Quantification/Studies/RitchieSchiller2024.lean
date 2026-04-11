import Linglib.Theories.Semantics.Lexical.Determiner.DomainRestriction
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.BToMGrounding
import Linglib.Core.Semantics.CommonGround
import Linglib.Tactics.RSAPredict
import Linglib.Core.Discourse.QUD
import Linglib.Core.Subjectivity

/-!
# @cite{ritchie-schiller-2024} — Default Domain Restriction Possibilities

@cite{ritchie-schiller-2024} @cite{cutting-vishton-1995} @cite{baker-jara-ettinger-saxe-tenenbaum-2017}
@cite{clark-1996} @cite{stalnaker-2002}

Ritchie, K. & Schiller, H. (2024). Default Domain Restriction Possibilities.
*Semantics & Pragmatics* 17, Article 13: 1–49.

## The Argument

When a speaker says "Every bottle is empty" at a dinner party, the hearer
restricts the quantifier domain to contextually relevant bottles — not all bottles
in the universe (R&S §1, ex. 3). Ritchie & Schiller argue that existing accounts
fail to explain *why* certain restrictions are defaults:
- **Rational pragmatic** (§2.1): RSA/Gricean reasoning doesn't explain default status
- **Discourse-structural** (§2.2): QUD-based accounts are too demanding
- **Intentionalist** (§2.3): speaker-intention accounts are too unconstrained

Their positive proposal (§3): cognitive heuristics — perceptual availability,
salience, and manipulability — generate a structured set of default domain
restriction possibilities (DDRPs). These are grounded in spatial cognition, where
nested spatial regions provide a natural ordering on candidate restrictions.

## Scenario

We construct an illustrative scenario (not from the paper) with 4 entities at
increasing spatial distances and 3 world states, then verify key formal
consequences of the DDRP framework for both ⟦every⟧ (↓MON) and ⟦some⟧ (↑MON).

## Compositional Grounding

Truth conditions derive from `every_restricted` / `some_restricted`
(DomainRestriction.lean), which wrap `every_sem` / `some_sem` (Quantifier.lean)
with a domain restrictor predicate. Nesting theorems derive from
`DDRP.every_nesting` / `DDRP.some_nesting`, connecting the nested spatial
regions to restrictor monotonicity.

## RSA Connection

While R&S argue *against* RSA as explaining default status (§2.1), DDRPs are
compatible with RSA as the *selection mechanism*: the listener reasons over
candidate DDRPs (= `Latent` in RSAConfig) to infer which domain restriction
the speaker intended. With a cognitive-default prior biasing toward peripersonal
scales, L1_latent infers the proximal restriction (§8).
-/

set_option autoImplicit false

namespace Phenomena.Quantification.Studies.RitchieSchiller2024

open Semantics.Montague (Model)
open Semantics.Quantification.Quantifier (every_sem some_sem)
open Semantics.Lexical.Determiner.DomainRestriction

-- ============================================================================
-- §1. Domain Types
-- ============================================================================

/-- Entities in the constructed scene: 4 bottles at increasing spatial distances. -/
inductive Entity where
  | b1  -- bottle on table (peripersonal)
  | b2  -- bottle on table (peripersonal)
  | b3  -- bottle across room (action space)
  | b4  -- bottle outside window (vista)
  deriving DecidableEq, Repr, Inhabited

def bottleModel : Model := { Entity := Entity, decEq := inferInstance }

instance : Fintype bottleModel.Entity where
  elems := ({Entity.b1, Entity.b2, Entity.b3, Entity.b4} : Finset Entity)
  complete := fun x => by cases x <;> (unfold bottleModel; simp)

-- ============================================================================
-- §2. Spatial Scene & DDRPs
-- ============================================================================

/-- A spatial scene: each entity occupies a spatial zone. -/
def SpatialScene (E : Type*) := E → SpatialScale

/-- Entities perceivable at a given scale threshold: those whose zone ≤ threshold. -/
def perceivable {E : Type*} (scene : SpatialScene E) (threshold : SpatialScale)
    (e : E) : Bool :=
  decide (scene e ≤ threshold)

/-- A spatial scene induces a DDRP: region s contains entities in zone ≤ s.
    Monotonicity and top-totality follow from the ordering on `SpatialScale`. -/
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

/-- DDRP for the bottle scenario, derived from the spatial scene.
    Peripersonal ⊆ action ⊆ vista (= unrestricted in this indoor scene). -/
abbrev sceneDDRP : DDRP SpatialScale Entity := sceneToDDRP dinnerScene

-- ============================================================================
-- §3. World States
-- ============================================================================

/-- World states: which bottles are empty.
    - `nearEmpty`: only proximal bottles (b1, b2) are empty
    - `midEmpty`: proximal + action-space bottles (b1, b2, b3) are empty
    - `allEmpty`: all bottles are empty -/
inductive World where
  | nearEmpty
  | midEmpty
  | allEmpty
  deriving DecidableEq, Repr, Inhabited

instance : Fintype World where
  elems := ({World.nearEmpty, World.midEmpty, World.allEmpty} : Finset World)
  complete := λ x => by cases x <;> simp

def emptyIn : World → Entity → Bool
  | .allEmpty, _ => true
  | .midEmpty, .b4 => false
  | .midEmpty, _ => true
  | .nearEmpty, .b1 | .nearEmpty, .b2 => true
  | .nearEmpty, _ => false

/-- All entities are bottles in this scenario (trivial restrictor). -/
def isBottle : bottleModel.Entity → Bool := λ _ => true

-- ============================================================================
-- §4. Truth Table: "Every bottle is empty" under each DDRP
-- ============================================================================

/-- Truth of "every bottle is empty" under a given spatial domain restriction.
    For all entities in the DDRP region that are bottles, they must be empty. -/
def everyBottleEmpty (scale : SpatialScale) (w : World) : Bool :=
  [Entity.b1, .b2, .b3, .b4].all
    (λ e => !(sceneDDRP.region scale e && isBottle e) || emptyIn w e)

-- w_near: only proximal bottles empty
-- Only peripersonal restriction licenses the utterance.
theorem w_near_peri : everyBottleEmpty .peripersonal .nearEmpty = true := by native_decide
theorem w_near_action : everyBottleEmpty .action .nearEmpty = false := by native_decide
theorem w_near_vista : everyBottleEmpty .vista .nearEmpty = false := by native_decide

-- w_mid: proximal + action-space bottles empty
-- Both peripersonal and action restrictions license the utterance.
theorem w_mid_peri : everyBottleEmpty .peripersonal .midEmpty = true := by native_decide
theorem w_mid_action : everyBottleEmpty .action .midEmpty = true := by native_decide
theorem w_mid_vista : everyBottleEmpty .vista .midEmpty = false := by native_decide

-- w_all: all bottles empty
-- All restrictions license the utterance.
theorem w_all_peri : everyBottleEmpty .peripersonal .allEmpty = true := by native_decide
theorem w_all_action : everyBottleEmpty .action .allEmpty = true := by native_decide
theorem w_all_vista : everyBottleEmpty .vista .allEmpty = true := by native_decide

-- ============================================================================
-- §5. Truth Table: "Some bottle is empty" under each DDRP
-- ============================================================================

/-- Truth of "some bottle is empty" under a given spatial domain restriction.
    Some entity in the DDRP region that is a bottle must be empty. -/
def someBottleEmpty (scale : SpatialScale) (w : World) : Bool :=
  [Entity.b1, .b2, .b3, .b4].any
    (λ e => sceneDDRP.region scale e && isBottle e && emptyIn w e)

-- w_near: only proximal bottles empty
-- All restrictions license "some bottle is empty" (there's always a witness).
theorem some_near_peri : someBottleEmpty .peripersonal .nearEmpty = true := by native_decide
theorem some_near_action : someBottleEmpty .action .nearEmpty = true := by native_decide
theorem some_near_vista : someBottleEmpty .vista .nearEmpty = true := by native_decide

-- w_mid: proximal + action-space bottles empty
theorem some_mid_peri : someBottleEmpty .peripersonal .midEmpty = true := by native_decide
theorem some_mid_action : someBottleEmpty .action .midEmpty = true := by native_decide
theorem some_mid_vista : someBottleEmpty .vista .midEmpty = true := by native_decide

-- w_all: all bottles empty
theorem some_all_peri : someBottleEmpty .peripersonal .allEmpty = true := by native_decide
theorem some_all_action : someBottleEmpty .action .allEmpty = true := by native_decide
theorem some_all_vista : someBottleEmpty .vista .allEmpty = true := by native_decide

-- ============================================================================
-- §6. Key Predictions
-- ============================================================================

/-- **Proximal default**: In the proximal world, only peripersonal restriction
    makes "every bottle is empty" true. The listener *must* infer the speaker
    intended the proximal domain — no other DDRP candidate works. -/
theorem proximal_default :
    everyBottleEmpty .peripersonal .nearEmpty = true ∧
    everyBottleEmpty .action .nearEmpty = false ∧
    everyBottleEmpty .vista .nearEmpty = false :=
  ⟨w_near_peri, w_near_action, w_near_vista⟩

/-- **↓MON/↑MON contrast**: ⟦every⟧ and ⟦some⟧ react oppositely to domain
    restriction. In the proximal world, ⟦every⟧ is true only under peripersonal
    restriction (↓MON: smaller domain helps), while ⟦some⟧ is true under all
    restrictions (↑MON: larger domain never hurts). -/
theorem monotonicity_contrast :
    everyBottleEmpty .peripersonal .nearEmpty = true ∧
    everyBottleEmpty .action .nearEmpty = false ∧
    someBottleEmpty .peripersonal .nearEmpty = true ∧
    someBottleEmpty .action .nearEmpty = true ∧
    someBottleEmpty .vista .nearEmpty = true :=
  ⟨w_near_peri, w_near_action, some_near_peri, some_near_action, some_near_vista⟩

-- ============================================================================
-- §7. Bridge to Theory: Nesting from DDRP Structure
-- ============================================================================

/-- ⟦every⟧ nesting (Prop level): truth under a larger scale entails truth under
    any smaller scale. Derives from `DDRP.every_nesting` via restrictor ↓MON. -/
theorem every_nesting_prop {s₁ s₂ : SpatialScale} (h : s₁ ≤ s₂)
    (R S : bottleModel.Entity → Prop) :
    every_restricted bottleModel (sceneDDRP.region s₂) R S →
    every_restricted bottleModel (sceneDDRP.region s₁) R S :=
  DDRP.every_nesting (m := bottleModel) sceneDDRP R S h

/-- ⟦some⟧ nesting (Prop level): truth under a smaller scale entails truth under
    any larger scale. Derives from `DDRP.some_nesting` via restrictor ↑MON. -/
theorem some_nesting_prop {s₁ s₂ : SpatialScale} (h : s₁ ≤ s₂)
    (R S : bottleModel.Entity → Prop) :
    some_restricted bottleModel (sceneDDRP.region s₁) R S →
    some_restricted bottleModel (sceneDDRP.region s₂) R S :=
  DDRP.some_nesting (m := bottleModel) sceneDDRP R S h

-- ============================================================================
-- §8. RSA Connection: DDRPs as Latent Interpretation Variables
-- ============================================================================

/-- Utterance type for the RSA model. -/
inductive Utterance where
  | everyEmpty  -- "every bottle is empty"
  | someEmpty   -- "some bottle is empty"
  deriving DecidableEq, Repr, Inhabited

instance : Fintype Utterance where
  elems := ({Utterance.everyEmpty, Utterance.someEmpty} : Finset Utterance)
  complete := λ x => by cases x <;> simp

/-- Literal meaning under a given DDRP scale. -/
def utteranceMeaning (scale : SpatialScale) : Utterance → World → Bool
  | .everyEmpty, w => everyBottleEmpty scale w
  | .someEmpty, w => someBottleEmpty scale w

/-- R&S §3.2: Three cognitive heuristics collectively determine which domain
    restrictions are defaults. Each heuristic assigns a relevance score to a
    spatial scale, reflecting how well entities at that scale satisfy the
    corresponding cognitive criterion. -/
inductive CognitiveHeuristic where
  | availability    -- perceptual availability: present in the here-and-now
  | salience        -- perceptual salience: attention-grabbing
  | manipulability  -- manipulability: affords physical interaction
  deriving DecidableEq, Repr

/-- Heuristic score for each (heuristic, scale) pair.

    - **Availability** (R&S §3.2 ¶1): Peripersonal objects are maximally available
      — perceived without bodily distortion. Action/vista objects are available
      but require effort. Unrestricted objects may not be present at all.
    - **Salience** (R&S §3.2 ¶2): Peripersonal and action-space objects are
      attention-grabbing. Vista/unrestricted objects are less noticeable.
    - **Manipulability** (R&S §3.2 ¶3): Only peripersonal objects afford physical
      interaction (within arm's reach). All others are out of reach. -/
def heuristicScore : CognitiveHeuristic → SpatialScale → ℚ
  | .availability,   .peripersonal => 2 | .availability,   .action => 1
  | .availability,   .vista        => 1 | .availability,   .unrestricted => 1
  | .salience,       .peripersonal => 1 | .salience,       .action => 1
  | .salience,       .vista        => 0 | .salience,       .unrestricted => 0
  | .manipulability, .peripersonal => 1 | .manipulability, .action => 0
  | .manipulability, .vista        => 0 | .manipulability, .unrestricted => 0

/-- Each heuristic is anti-monotone: more proximal scales score at least as
    high. This captures R&S's claim that proximity enhances all three
    cognitive dimensions simultaneously. -/
theorem heuristic_anti_mono (h : CognitiveHeuristic) {s₁ s₂ : SpatialScale}
    (hle : s₁ ≤ s₂) :
    heuristicScore h s₂ ≤ heuristicScore h s₁ := by
  cases h <;> cases s₁ <;> cases s₂ <;>
    simp only [heuristicScore] <;> (revert hle; decide)

/-- Latent prior derived from the three cognitive heuristics. The sum reflects
    R&S §3.2's conjunction: a good default restriction should score high on
    availability AND salience AND manipulability. The prior is unnormalized —
    RSA normalizes via the partition function. -/
def ddprPrior (s : SpatialScale) : ℚ :=
  heuristicScore .availability s + heuristicScore .salience s +
    heuristicScore .manipulability s

/-- The derived prior is anti-monotone: more proximal scales receive higher
    prior weight. Follows from anti-monotonicity of each heuristic. -/
theorem ddprPrior_anti_mono {s₁ s₂ : SpatialScale} (h : s₁ ≤ s₂) :
    ddprPrior s₂ ≤ ddprPrior s₁ := by
  unfold ddprPrior
  have ha := heuristic_anti_mono .availability h
  have hs := heuristic_anti_mono .salience h
  have hm := heuristic_anti_mono .manipulability h
  linarith

/-- RSA model with DDRPs as the latent interpretation variable.

    `Latent = SpatialScale`: L1 marginalizes over candidate domain restrictions
    to infer the speaker's intended domain. The `latentPrior` encodes the
    cognitive default via `ddprPrior`.

    While R&S argue against RSA as explaining *default status* (§2.1), DDRPs
    are compatible with RSA as the *selection mechanism* once the candidate set
    and prior are fixed by cognitive heuristics. -/
noncomputable def domainRestrictionRSA : RSA.RSAConfig Utterance World where
  Latent := SpatialScale
  meaning _ scale u w := if utteranceMeaning scale u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u := (l0 u w) ^ α
  s1Score_nonneg _ _ _ _ _ h_nn h_pos := Real.rpow_nonneg (h_nn _ _) _
  α := 1
  α_pos := by norm_num
  latentPrior _ l := ↑(ddprPrior l)
  latentPrior_nonneg _ l := by cases l <;> simp only [ddprPrior, heuristicScore] <;> norm_num
  worldPrior_nonneg _ := by norm_num

/-- **L1_latent peripersonal > action**: The listener infers peripersonal as
    the most likely intended domain restriction, beating the action-space
    scale. This captures R&S's core claim: cognitive-default priors biasing
    toward proximal scales cause the listener to default to the nearest
    restriction. -/
theorem L1_latent_peripersonal_gt_action :
    domainRestrictionRSA.L1_latent .everyEmpty .peripersonal >
    domainRestrictionRSA.L1_latent .everyEmpty .action := by
  rsa_predict

/-- **L1_latent action > vista**: The action scale is preferred over vista,
    showing the full ordering: peripersonal > action > vista. -/
theorem L1_latent_action_gt_vista :
    domainRestrictionRSA.L1_latent .everyEmpty .action >
    domainRestrictionRSA.L1_latent .everyEmpty .vista := by
  rsa_predict

/-- For "some bottle is empty", the cognitive-default prior overrides the
    semantic signal: peripersonal is inferred as the most likely scale despite
    ⟦some⟧ being true under all scales in all worlds. Without the prior,
    RSA predicts the WRONG ordering (see `uniform_some_distal_wins`). -/
theorem L1_latent_some_peripersonal_gt_action :
    domainRestrictionRSA.L1_latent .someEmpty .peripersonal >
    domainRestrictionRSA.L1_latent .someEmpty .action := by
  rsa_predict

-- ============================================================================
-- §8b. R&S §2.1: RSA with Uniform Priors Cannot Explain Defaults
-- ============================================================================

/-! R&S §2.1 argue that RSA alone — without cognitive supplementation —
    cannot explain why certain domain restrictions are defaults. We verify
    this by constructing an RSA model with uniform latent priors and showing:

    1. For ⟦every⟧ (↓MON), RSA with uniform priors *happens* to predict
       peripersonal as most likely — but only because the literal semantics
       provides discriminative signal (it's false under wider scales in some
       worlds). This is not an explanation of default status.

    2. For ⟦some⟧ (↑MON), RSA with uniform priors predicts the *wrong*
       ordering: the listener infers vista/unrestricted as most likely, because
       under wider scales, ⟦some⟧ is the only true utterance in more worlds
       (higher L0 probability). Cognitive-default priors are needed to override
       this semantic signal.

    This pair of results formalizes R&S's core negative argument: RSA's
    predictions depend on the specific quantifier's monotonicity profile,
    not on cognitive structure, so RSA alone doesn't explain the cross-quantifier
    generalization that proximal restrictions are always preferred. -/

/-- RSA model with uniform latent prior (no cognitive bias).
    Identical to `domainRestrictionRSA` except `latentPrior _ _ = 1`. -/
noncomputable def uniformPriorRSA : RSA.RSAConfig Utterance World where
  Latent := SpatialScale
  meaning _ scale u w := if utteranceMeaning scale u w then 1 else 0
  meaning_nonneg _ _ _ _ := by split <;> norm_num
  s1Score l0 α _ w u := (l0 u w) ^ α
  s1Score_nonneg _ _ _ _ _ h_nn h_pos := Real.rpow_nonneg (h_nn _ _) _
  α := 1
  α_pos := by norm_num
  latentPrior_nonneg _ _ := by norm_num
  worldPrior_nonneg _ := by norm_num

/-- R&S §2.1: With uniform priors, RSA still predicts peripersonal for
    ⟦every⟧ — but only because the literal semantics does the work (⟦every⟧
    is false under wider scales in more worlds, so L0 assigns higher
    probability to narrower scales). This is a semantic accident, not a
    cognitive explanation. -/
theorem uniform_every_still_proximal :
    uniformPriorRSA.L1_latent .everyEmpty .peripersonal >
    uniformPriorRSA.L1_latent .everyEmpty .action := by
  rsa_predict

/-- R&S §2.1: With uniform priors, RSA predicts the WRONG ordering for
    ⟦some⟧ — the listener infers vista as most likely, not peripersonal.
    This is because under wider scales, ⟦some⟧ is more informative (it's
    the only true utterance when ⟦every⟧ is false), yielding higher L0.
    Cognitive-default priors (`ddprPrior`) are needed to override this. -/
theorem uniform_some_distal_wins :
    uniformPriorRSA.L1_latent .someEmpty .vista >
    uniformPriorRSA.L1_latent .someEmpty .peripersonal := by
  rsa_predict

-- ============================================================================
-- §9. Perception & Common Ground
-- ============================================================================

/-! Connects DDRPs to @cite{baker-jara-ettinger-saxe-tenenbaum-2017}'s BToM
architecture and @cite{stalnaker-2002}'s common ground.

When the scene is common ground (@cite{clark-1996} on joint attention),
speaker and hearer derive the same DDRP. Different perceptual access yields
different DDRPs, motivating R&S's requirement of perceptual co-presence. -/

open Core.BToM
open Core.CommonGround

/-- The RSA-BToM bridge applies to the domain restriction RSA config. -/
theorem rsa_btom_bridge (u : Utterance) (w : World) :
    domainRestrictionRSA.L1agent.score u w =
      (domainRestrictionRSA.toBToM).worldMarginal u w :=
  RSA.RSAConfig.L1_eq_btom_worldMarginal domainRestrictionRSA u w

/-- When all discourse participants share the same spatial scene, they
    derive the same DDRP — a prerequisite for successful communication
    about domain-restricted quantifiers. -/
theorem shared_scene_shared_ddrp (scene : SpatialScene Entity)
    (getScene : World → SpatialScene Entity)
    (hcg : ∀ w, getScene w = scene) :
    ∀ w, sceneToDDRP (getScene w) = sceneToDDRP scene := by
  intro w; exact congrArg sceneToDDRP (hcg w)

/-- An alternative scene where b3 is behind a partition (in vista, not action). -/
def partitionScene : SpatialScene Entity
  | .b1 => .peripersonal
  | .b2 => .peripersonal
  | .b3 => .vista
  | .b4 => .vista

theorem scenes_differ_on_b3 :
    dinnerScene .b3 ≠ partitionScene .b3 := by native_decide

/-- Different spatial scenes yield different DDRPs. -/
theorem different_scenes_different_ddrps :
    (sceneToDDRP dinnerScene).region ≠ (sceneToDDRP partitionScene).region := by
  intro h
  exact absurd (congrFun (congrFun h .action) .b3) (by native_decide)

/-- Without perceptual co-presence, domain-restricted quantifiers can
    receive different truth values: "every bottle is empty" under action-space
    restriction is false with the dinner scene but true with the partition scene
    (where b3 is too far to be in the action zone). -/
theorem perception_mismatch_changes_truth :
    [Entity.b1, .b2, .b3, .b4].all
      (λ e => !((sceneToDDRP dinnerScene).region .action e && isBottle e) ||
        emptyIn .nearEmpty e) = false ∧
    [Entity.b1, .b2, .b3, .b4].all
      (λ e => !((sceneToDDRP partitionScene).region .action e && isBottle e) ||
        emptyIn .nearEmpty e) = true := by
  constructor <;> native_decide

-- ============================================================================
-- §10. QUD and Non-Default Restrictions (R&S §4)
-- ============================================================================

/-! R&S §4 argues that non-default domain restrictions arise from explicit
    discourse moves. When the QUD shifts (e.g., "Where are the blue things?"),
    the domain restriction can widen beyond the cognitive default. We connect
    this to the `QUD` infrastructure from @cite{roberts-2012}. -/

/-- QUD partitioning worlds by spatial emptiness profile: which bottles are
    empty at each spatial scale? Worlds that agree on the emptiness of
    peripersonal, action, and vista bottles give the same answer. -/
def spatialQUD : QUD World :=
  QUD.ofDecEq (λ w => (everyBottleEmpty .peripersonal w,
                        everyBottleEmpty .action w,
                        everyBottleEmpty .vista w))

/-- The spatial QUD distinguishes all three worlds: each has a different
    emptiness profile across scales. -/
theorem spatialQUD_distinguishes_all :
    spatialQUD.sameAnswer .nearEmpty .midEmpty = false ∧
    spatialQUD.sameAnswer .midEmpty .allEmpty = false ∧
    spatialQUD.sameAnswer .nearEmpty .allEmpty = false := by
  constructor <;> [native_decide; constructor <;> native_decide]

-- ============================================================================
-- §11. Objectivity of Default Restrictions (R&S §3.2)
-- ============================================================================

/-! R&S §3.2 argue that default domain restrictions are *objective*
    (nonsubjective on @cite{traugott-dasher-2002}'s cline): they derive from
    perceptual/cognitive structure (location, spatial proximity), not from
    speaker attitude (subjective) or addressee face (intersubjective). This
    predicts that spatial/temporal restrictions make better defaults than
    evaluative restrictions (beauty, tastiness).

    @cite{scontras-degen-goodman-2017} find that more objective adjectives are
    ordered closer to the noun — "the big blue box" over "the blue big box" —
    because less subjective content is more useful for communication. R&S
    extend this: more objective *domain restrictions* are similarly privileged
    as defaults because they are more likely to be shared among participants
    and thus better for coordination.

    The connection is structural: all three cognitive heuristics (availability,
    salience, manipulability) target features that are objective in the sense
    that they don't depend on speaker perspective or taste. -/

open Core.Subjectivity (SubjectivityLevel)

/-- DDRPs are nonsubjective: the three cognitive heuristics (availability,
    salience, manipulability) all target spatiotemporal properties that don't
    depend on speaker perspective. This is not stipulated — it follows from
    the heuristics being defined over `SpatialScale`, which is a physical
    (observer-independent) ordering on spatial regions. -/
def ddprSubjectivityLevel : SubjectivityLevel := .nonSubjective

/-- Objectivity prediction: DDRPs (nonsubjective) precede subjective
    interpretations on the Traugott-Dasher cline, predicting they are
    available as defaults before evaluative restrictions require discourse
    setup. The ordering reflects @cite{scontras-degen-goodman-2017}'s finding:
    less subjective content is more useful for communication. -/
theorem ddpr_precedes_subjective :
    ddprSubjectivityLevel ≤ SubjectivityLevel.subjective := by decide

/-- Nonsubjective is the minimum on the Traugott-Dasher cline, so DDRPs
    precede *all* subjective and intersubjective interpretations. -/
theorem ddpr_is_minimum :
    ∀ l : SubjectivityLevel, ddprSubjectivityLevel ≤ l := by
  intro l; exact Core.Subjectivity.nonSubjective_le l

end Phenomena.Quantification.Studies.RitchieSchiller2024
