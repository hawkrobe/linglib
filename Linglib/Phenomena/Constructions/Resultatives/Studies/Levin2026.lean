import Linglib.Core.Lexical.DiathesisAlternation
import Linglib.Theories.Semantics.Causation.Resultatives
import Linglib.Theories.Syntax.ConstructionGrammar.ArgumentStructure
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Fragments.Mandarin.Resultatives
-- Data dissolved into GoldbergJackendoff2004 (imported transitively via Causation.Resultatives)
import Linglib.Phenomena.ArgumentStructure.DiathesisAlternations.Data

/-!
# Levin (2026): The door pushed open
@cite{levin-2026}

*The door pushed open*: an English intransitive resultative construction
with transitive-only verbs. *Journal of East Asian Linguistics* 35:3.

## Core contribution

Identifies a neglected class of English intransitive resultatives —
*The door pushed open*, *The cork pulled free*, *The door slammed shut* —
where the base verb is **transitive-only** outside the construction.
These verbs (*push*, *slam*, *pull*) cannot occur intransitively without
the result phrase: *\*The door pushed.*

Proposes that these "intr-*push open*" resultatives are the **anticausative
variant** of the causative alternation, with their transitive counterparts
(*Pat pushed the door open*) as the causative variant. The resultative
construction itself licenses the alternation that the verb lacks in
isolation.

## Key empirical findings

1. **Verb restriction**: only verbs of exerting force (Levin §12) and
   verbs of surface contact (§18 hitting, §10.4 wiping subtypes)
2. **Adjective restriction**: only *open*, *closed*, *shut*, *free*,
   *loose*, *flat* — all describing spatially instantiated states
3. **Verb–adjective combination is critical**: neither alone suffices
4. **Discourse licensing**: anticausative conditions — cause recoverable
   in context or identity unknown to speaker
5. **Semantic licensing**: subject DP must be capable of autonomous motion
   ("projectile" — entity imbued with force that can act without
   continuous external involvement)
6. **Proper Containment Condition** (@cite{rappaport-hovav-levin-2012}):
   when the cause is continuously involved, the causative variant is
   required — blocking the intr-*push open* pattern

## Architecture

This study connects four existing layers:
- `Core.Lexical.LevinClass`: verb classes lack causative alternation (§12, §18)
- `Theories.Semantics.Causation.Resultatives`: construction adds CAUSE;
  PCC maps onto the independent-source/tightness infrastructure
- `Fragments.English.Predicates`: verb and adjective entries
- `Phenomena.ArgumentStructure.DiathesisAlternations`: existing alternation data

The central theoretical insight — that *constructions* can license
alternation behavior that *verbs* lack in isolation — is a construction
grammar point that the current verb-level `participatesIn` infrastructure
does not directly accommodate. This file formalizes the specific case.
-/

namespace Levin2026

open Core (Situation)

open Core.Verbs
open LevinClass (pushPull hit wipe)
open Fragments.English.Predicates.Verbal (push pull kick)
open Fragments.English.Predicates.Adjectival (open_ closed_ shut free_ loose flat
  AdjectivalPredicateEntry)
open Core.StructuralEquationModel
open Semantics.Causation.Sufficiency (causallySufficient)
open Semantics.Causation.Necessity (causallyNecessary)
open Semantics.Causation.Resultatives (completesForEffect resultativeCausativeBuilder
  freezeSolidModel)
open Semantics.Verb.ChangeOfState (CoSType)
open ConstructionGrammar (resultative composedMeaning predictedAlternationInConstruction
  ArgStructureConstruction)
open ConstructionGrammar.Studies.GoldbergJackendoff2004 (ResultativeType)

-- ════════════════════════════════════════════════════
-- § 1. Verb classes in the construction
-- ════════════════════════════════════════════════════

/-! ## Verb inventory

The verbs attested in intr-*push open* resultatives describe the
application of force to an entity. They are drawn from two subclasses
of manner verbs: verbs of exerting force (§12) and verbs of surface
contact (§18 hitting, §10.4 wiping).

Note: *scrape* and *sweep* are Levin §10.4 (wipe) verbs, but in
intr-*push open* they participate through their **surface contact**
sense, not their removing sense. Wipe verbs as a class DO show the
causative alternation (they lexicalize CoS). These verbs enter the
construction because only their force-application component is
relevant, not the removal result. -/

/-- The core Levin classes for intr-*push open* verbs.
    Verbs of exerting force (§12 = pushPull) and verbs of surface
    contact, hitting subtype (§18.1 = hit). Wipe verbs (§10.4) also
    participate but are handled separately (see `all_verbs_from_predicted_classes`). -/
def intrPushOpenClasses : List LevinClass := [.pushPull, .hit]

/-- All core intr-*push open* verb classes lack the causative alternation
    in isolation. This is the key precondition: the verb alone does not
    alternate, so the construction must license the alternation. -/
theorem all_classes_no_causative_alternation :
    intrPushOpenClasses.all
      (! ·.participatesIn .causativeInchoative) = true := by
  native_decide

/-- Cross-reference: the existing alternation data in
    `DiathesisAlternations.Data` already records that *hit* (§18.1) is
    blocked for causative/inchoative. Our theorem agrees. -/
theorem agrees_with_diathesis_data :
    Phenomena.ArgumentStructure.DiathesisAlternations.Data.ci_hit.result
      == .blocked := by
  native_decide

/-- All core classes are pure manner roots
    (@cite{beavers-koontz-garboden-2020}): they encode no state, no result,
    no causation. The result and causation come from the construction. -/
theorem all_classes_pure_manner :
    intrPushOpenClasses.all
      (·.rootEntailments == .pureManner) = true := by
  native_decide

/-- All core classes encode contact and motion but NOT change of state
    and NOT causation. This is why they don't show the causative alternation
    (@cite{fillmore-1970}): no scalar change is lexicalized. -/
theorem all_classes_no_cos_no_causation :
    intrPushOpenClasses.all (λ c =>
      let mc := c.meaningComponents
      mc.contact && mc.motion && !mc.changeOfState && !mc.causation
    ) = true := by
  native_decide

/-- Fragment verb entries confirm the classification. -/
theorem push_is_pushPull : push.levinClass = some .pushPull := rfl
theorem pull_is_pushPull : pull.levinClass = some .pushPull := rfl
theorem kick_is_hit : kick.levinClass = some .hit := rfl

/-! ### Construction-dependent alternation (@cite{goldberg-1995})

The key derivation: these verbs cannot alternate *alone* (shown above),
but they CAN alternate *inside the resultative construction*. The
resultative adds CoS + causation via `semanticContribution`; the
composed meaning has all four components needed for the causative
alternation. No new alternation logic is needed — `predictedAlternation`
on the fused result fires automatically.

This formalizes the paper's central insight (§3): "when such verbs are
found in a resultative, the construction as a whole describes a change
of state ... properties of the resultative construction itself are
implicated in the 'loosening' of transitivity that characterizes
intr-*push open* resultatives." -/

/-- PushPull alone: no causative alternation. -/
theorem pushPull_alone_no_alternation :
    LevinClass.pushPull.meaningComponents.predictedAlternation
      .causativeInchoative = false := by native_decide

/-- PushPull in the resultative: causative alternation predicted.
    The construction adds CoS + causation → the composed meaning
    has `changeOfState && causation`, which is the precondition. -/
theorem pushPull_alternates_in_resultative :
    predictedAlternationInConstruction
      LevinClass.pushPull.meaningComponents
      resultative .causativeInchoative = true := by native_decide

/-- Hit alone: no causative alternation. -/
theorem hit_alone_no_alternation :
    LevinClass.hit.meaningComponents.predictedAlternation
      .causativeInchoative = false := by native_decide

/-- Hit in the resultative: causative alternation predicted. -/
theorem hit_alternates_in_resultative :
    predictedAlternationInConstruction
      LevinClass.hit.meaningComponents
      resultative .causativeInchoative = true := by native_decide

/-- All core intr-push-open classes alternate in the resultative. -/
theorem all_classes_alternate_in_resultative :
    intrPushOpenClasses.all (λ c =>
      predictedAlternationInConstruction
        c.meaningComponents resultative .causativeInchoative
    ) = true := by native_decide

/-! ### Event structure shift (bridge to `EventStructure`)

The same fusion operation that predicts new alternations also predicts
template shift: manner verbs (activity template) become accomplishments
inside the resultative. This connects to telicity, result state
diagnostics (*again*/*re-* ambiguity), and CAUSE structure. -/

open Semantics.Verb.EventStructure

/-- PushPull alone is an activity (no CoS, no CAUSE). -/
theorem pushPull_is_activity :
    LevinClass.pushPull.eventTemplate = .activity := rfl

/-- PushPull in the resultative shifts to accomplishment (the construction
    adds [CAUSE [BECOME [STATE]]]). -/
theorem pushPull_accomplishment_in_resultative :
    (LevinClass.pushPull.meaningComponents.fuse
      resultative.semanticContribution).predictedTemplate = .accomplishment := by
  exact fuse_cos_caus_yields_accomplishment _ _ rfl rfl

/-- Hit alone is an activity. -/
theorem hit_is_activity' :
    LevinClass.hit.eventTemplate = .activity := rfl

/-- Hit in the resultative shifts to accomplishment. -/
theorem hit_accomplishment_in_resultative :
    (LevinClass.hit.meaningComponents.fuse
      resultative.semanticContribution).predictedTemplate = .accomplishment := by
  exact fuse_cos_caus_yields_accomplishment _ _ rfl rfl

/-- Full dual prediction for pushPull in the resultative: template shift
    AND alternation AND intransitive variant, all from one fusion. -/
theorem pushPull_dual_in_resultative :
    (LevinClass.pushPull.meaningComponents.fuse
      resultative.semanticContribution).predictedTemplate = .accomplishment ∧
    (LevinClass.pushPull.meaningComponents.fuse
      resultative.semanticContribution).predictedAlternation
        .causativeInchoative = true ∧
    (LevinClass.pushPull.meaningComponents.fuse
      resultative.semanticContribution).predictedTemplate.intransitiveVariant
        = some .achievement := by
  exact fuse_dual_prediction _ _ rfl rfl rfl rfl

/-- Vendler class shift: pushPull goes from atelic activity to telic
    accomplishment inside the resultative. -/
theorem pushPull_vendler_shift :
    LevinClass.pushPull.eventTemplate.vendlerClass = .activity ∧
    (LevinClass.pushPull.meaningComponents.fuse
      resultative.semanticContribution).predictedTemplate.vendlerClass
        = .accomplishment :=
  ⟨rfl, fuse_vendler_class_shift _ _ rfl rfl⟩

/-! ### Middle construction parallel (§2, examples 17–18)

The paper shows *pound* enters the middle construction only with a
result phrase: "*This kind of metal pounds easily" vs "This kind of
metal pounds flat easily." The existing `predictedAlternationInConstruction`
infrastructure derives this — the middle alternation requires CoS,
which comes from the resultative construction, not the verb. -/

/-- Hit-class verbs (including *pound*) cannot enter the middle alone. -/
theorem hit_no_middle_alone :
    LevinClass.hit.meaningComponents.predictedAlternation .middle = false := by
  native_decide

/-- Hit-class verbs CAN enter the middle inside the resultative.
    This derives the paper's observation (18b) from the same mechanism. -/
theorem hit_middle_in_resultative :
    predictedAlternationInConstruction
      LevinClass.hit.meaningComponents resultative .middle = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 2. Adjective set: spatially instantiated states
-- ════════════════════════════════════════════════════

/-! ## Adjective inventory

Only a small set of adjectives heads the result phrase in intr-*push open*
resultatives. Each describes a spatially instantiated state — a state
whose attainment requires the entity to be in a specific spatial
configuration with respect to a reference entity.

Three semantic subtypes:
1. **Barrier configuration**: *open*, *closed*, *shut* — spatial
   configuration of a barrier (door, gate, window) relative to its frame
2. **Unattachment**: *free*, *loose* — freedom from spatial contiguity
   with a reference entity (frame, bottle, ground)
3. **Surface orientation**: *flat* — orientation relative to a reference
   surface -/

/-- Reuse the theory-level `SpatialConfigType` from `Adjective.Theory`. -/
abbrev SpatialAdjType := Semantics.Gradability.SpatialConfigType

/-- All six attested adjectives have a spatial classification in their
    Fragment entries (structural, not string-based). -/
theorem all_attested_adjs_spatial :
    [open_, closed_, shut, free_, loose, flat].all
      (·.spatialConfigType |>.isSome) = true := by
  native_decide

/-- All attested adjectives are closed-scale (absolute) in
    @cite{kennedy-2007}'s terms. Spatially instantiated states have
    crisp endpoints (fully open vs. fully closed). -/
theorem all_attested_adjs_closed_scale :
    [open_, closed_, shut, free_, loose, flat].all
      (·.scaleType == .closed) = true := by
  native_decide

/-! Adjectives in senses that are NOT spatially instantiated do not
appear in intr-*push open* resultatives, even when they occur in
transitive resultatives. The non-spatial senses of *free* ("free
of charge", "free of debris") and *loose* ("loose shoelaces") are
not attested. Adjectives like *bald*, *firm*, *senseless*, *red* have no
`spatialConfigType` in the Fragment and are never attested in
intr-*push open* resultatives (examples 57b–60b). -/

-- ════════════════════════════════════════════════════
-- § 3. Causative alternation pairs
-- ════════════════════════════════════════════════════

/-! ## Transitive–intransitive pairing

The paper's central argument (§3): tr-*push open* and intr-*push open*
form a **causative alternation pair**. The transitive is the causative
variant; the intransitive is the anticausative variant. Both share the
same verb–adjective combination and the same constructional meaning:

- Causative: `[Agent_effector V NP] CAUSE [NP BECOME Adj]`
- Anticausative: `[NP BECOME Adj]` (cause suppressed) -/

/-- An alternation pair: transitive and intransitive resultative
    with the same verb–adjective combination. -/
structure AlternationPair where
  verb : String
  adjective : String
  transitive : String
  intransitive : String
  bareIntransitive : String   -- without RP: ungrammatical
  verbClass : LevinClass
  adjType : SpatialAdjType
  deriving Repr, BEq

/-- Push–open (examples 19, 20; 10a,b). -/
def push_open : AlternationPair :=
  { verb := "push", adjective := "open"
  , transitive := "He pushed the silent wooden door open."
  , intransitive := "The back door pushed open."
  , bareIntransitive := "*The door pushed."
  , verbClass := .pushPull, adjType := .barrierConfig }

/-- Pull–free (examples 21, 22; 13a,b). -/
def pull_free : AlternationPair :=
  { verb := "pull", adjective := "free"
  , transitive := "Nuttall finally pulled the cork free."
  , intransitive := "The cork pulled free with a satisfying pop."
  , bareIntransitive := "*The cork pulled."
  , verbClass := .pushPull, adjType := .unattachment }

/-- Slam–shut (fn. 11; intransitive from example 23).
    Note: *slam* is polysemous — in *Pat slammed the door / The door slammed*
    it has a closing-with-impact sense that independently shows the causative
    alternation. The `.hit` classification here applies to the surface-contact
    sense, not the closing sense. The transitive resultative is not explicitly
    given in the paper but is implied by the alternation pair analysis. -/
def slam_shut : AlternationPair :=
  { verb := "slam", adjective := "shut"
  , transitive := "She slammed the valve shut."
  , intransitive := "The valve slammed shut."
  , bareIntransitive := "*The valve slammed."
  , verbClass := .hit, adjType := .barrierConfig }

/-- Punch–open (intransitive from example 11a; transitive implied). -/
def punch_open : AlternationPair :=
  { verb := "punch", adjective := "open"
  , transitive := "The two men punched the door open."
  , intransitive := "The door punched open and two more men leaped into the room."
  , bareIntransitive := "*The door punched."
  , verbClass := .hit, adjType := .barrierConfig }

/-- Fling–open (intransitive from example 33; transitive implied). -/
def fling_open : AlternationPair :=
  { verb := "fling", adjective := "open"
  , transitive := "She flung the front door open."
  , intransitive := "The door flung open immediately."
  , bareIntransitive := "*The door flung."
  , verbClass := .pushPull, adjType := .barrierConfig }

/-- Scrape–free (intransitive from example 39; transitive implied). -/
def scrape_free : AlternationPair :=
  { verb := "scrape", adjective := "free"
  , transitive := "She scraped the plane's door free."
  , intransitive := "The door scraped free of its frame."
  , bareIntransitive := "*The door scraped."
  , verbClass := .wipe, adjType := .unattachment }

/-- Smack–flat (intransitive from example 48; transitive implied). -/
def smack_flat : AlternationPair :=
  { verb := "smack", adjective := "flat"
  , transitive := "She smacked the poster board flat against the windshield."
  , intransitive := "The poster board smacked flat against my windshield."
  , bareIntransitive := "*The poster board smacked."
  , verbClass := .hit, adjType := .surfaceOrient }

/-- Thump–closed (intransitive from example 12a; transitive from 12b). -/
def thump_closed : AlternationPair :=
  { verb := "thump", adjective := "closed"
  , transitive := "She thumped the door closed."
  , intransitive := "The front door thumped closed."
  , bareIntransitive := "*The door thumped."
  , verbClass := .hit, adjType := .barrierConfig }

def alternationPairs : List AlternationPair :=
  [ push_open, pull_free, slam_shut, punch_open
  , fling_open, scrape_free, smack_flat, thump_closed ]

/-- All pairs use verbs from the predicted classes
    (pushPull, hit — or wipe for scrape/sweep). -/
theorem all_verbs_from_predicted_classes :
    alternationPairs.all (λ d =>
      intrPushOpenClasses.contains d.verbClass ||
      d.verbClass == .wipe) = true := by
  native_decide

/-- Each core-class pair (pushPull, hit) is blocked alone but gains the
    causative alternation inside the resultative construction.
    Wipe verbs (scrape/sweep) are excluded: they independently alternate
    because they lexicalize CoS; they enter the construction through
    their surface-contact sense, not their removing sense. -/
theorem per_pair_alternation_core :
    (alternationPairs.filter (intrPushOpenClasses.contains ·.verbClass)).all (λ p =>
      !p.verbClass.participatesIn .causativeInchoative &&
      predictedAlternationInConstruction
        p.verbClass.meaningComponents resultative .causativeInchoative
    ) = true := by native_decide

/-- Each pair's `adjType` agrees with the Fragment entry's `spatialConfigType`. -/
theorem push_open_adj_agrees : open_.spatialConfigType = some push_open.adjType := rfl
theorem pull_free_adj_agrees : free_.spatialConfigType = some pull_free.adjType := rfl
theorem slam_shut_adj_agrees : shut.spatialConfigType = some slam_shut.adjType := rfl
theorem punch_open_adj_agrees : open_.spatialConfigType = some punch_open.adjType := rfl
theorem fling_open_adj_agrees : open_.spatialConfigType = some fling_open.adjType := rfl
theorem scrape_free_adj_agrees : free_.spatialConfigType = some scrape_free.adjType := rfl
theorem smack_flat_adj_agrees : flat.spatialConfigType = some smack_flat.adjType := rfl
theorem thump_closed_adj_agrees : closed_.spatialConfigType = some thump_closed.adjType := rfl

/-! ### Negative evidence: verb alone doesn't suffice

Verbs outside the predicted classes do not license intr-*push open*
even with an appropriate adjective (examples 51–56). -/

/-- Verbs that occur in transitive resultatives with the relevant
    adjectives but lack intr-*push open* counterparts. -/
def blockedVerbs : List (String × String × String) :=
  [ ("paint", "shut",  "*The window painted shut.")    -- (51b)
  , ("wire",  "shut",  "*The windows wired shut.")     -- (52b)
  , ("shovel","free",  "*Her car shoveled free.")      -- (53b)
  , ("lever", "free",  "*One of the clasps levered free.")  -- (54b)
  , ("nudge", "loose", "*The tooth nudged loose.")      -- (55b)
  , ("oil",   "flat",  "*His hair oiled flat.")        -- (56b)
  , ("nail",  "shut",  "*The root cellar door nailed shut.") ]  -- (74→75)

/-! ### Negative evidence: adjective alone doesn't suffice

Even in their spatially instantiated senses, the adjectives can appear
in transitive resultatives with verbs of the right type, yet the
transitive resultative lacks an intr-*push open* counterpart when the
COMBINATION is wrong (examples 57–60). -/

def blockedCombinations : List (String × String × String) :=
  [ ("yank", "bald",      "*I yanked bald./*My scalp yanked bald.")           -- (57b)
  , ("pull", "firm",      "*The skin of her temples and cheeks pulled firm.") -- (58b)
  , ("scrape","smooth",   "*The ground scraped smooth and clean.")            -- (59b)
  , ("punch","senseless", "*Frank punched senseless.") ]                      -- (60b)

-- ════════════════════════════════════════════════════
-- § 4. The construction adds CAUSE
-- ════════════════════════════════════════════════════

/-! ## Causal dynamics and event decomposition

The constructional meaning of resultatives (§3, example 25):
  `[Action denoted by verb] causes [change into state denoted by RP]`

For tr-*push open* (§3, example 30):
  `[Sam_effector push the door] CAUSE [the door BECOME open]`

The constructional CAUSE comes from the resultative, not from the verb.
The constructional BECOME maps to `CoSType.inception` (¬open → open). -/

/-- The constructional BECOME in resultatives = inception (¬P → P).
    This connects to the existing `ChangeOfState` infrastructure. -/
def resultativeBECOME : CoSType := .inception

private def pushingVar : Variable := mkVar "pushing"
private def openVar : Variable := mkVar "open"

/-- "Pat pushed the door open": pushing → open. -/
def pushDoorOpenModel : CausalDynamics :=
  ⟨[CausalLaw.simple pushingVar openVar]⟩

/-- The verbal subevent is causally sufficient for the result. -/
theorem push_sufficient_for_open :
    causallySufficient pushDoorOpenModel Situation.empty
      pushingVar openVar = true := by
  native_decide

/-- The verbal subevent is the completion event (sufficient + necessary),
    matching the CC-selection analysis in `Resultatives.lean`. -/
theorem push_completes_for_open :
    completesForEffect pushDoorOpenModel Situation.empty
      pushingVar openVar = true := by
  native_decide

/-- The resultative uses the `.make` builder (sufficiency). -/
theorem push_open_uses_make :
    resultativeCausativeBuilder = .make := rfl

/-! ### Bridge: ConstructionGrammar ↔ CausalDynamics

Two independent systems model the "construction adds causation" insight:
- `ArgStructureConstruction.semanticContribution.causation` (Boolean flag)
- `CausalDynamics.laws` (structural equations)

The Boolean layer predicts alternation behavior; the structural layer
models how the causation works (sufficiency, necessity, tightness).
They must agree: `causation = true ↔ dynamics non-empty`. -/

/-- Consistency between the Boolean and structural causation layers. -/
def causationConsistent (cxn : ArgStructureConstruction)
    (dyn : CausalDynamics) : Bool :=
  cxn.semanticContribution.causation == (dyn.laws.length > 0)

/-- The resultative construction + push-open dynamics are consistent:
    both say "there is causation." -/
theorem resultative_push_open_consistent :
    causationConsistent resultative pushDoorOpenModel = true := by native_decide

/-- The resultative construction + freeze-solid dynamics are INconsistent:
    the construction says causation but the dynamics are empty.
    This formally captures why freeze-solid is a noncausative resultative —
    it uses a DIFFERENT construction (noncausative) with no causation flag. -/
theorem resultative_freeze_solid_inconsistent :
    causationConsistent resultative freezeSolidModel = false := by native_decide

/-! ### Key contrast: intr-push-open ≠ freeze-solid

"The river froze solid" is a noncausative resultative where *freeze*
independently shows the causative alternation and the causal dynamics
are empty (no constructional CAUSE).

"The door pushed open" is fundamentally different: *push* does NOT
independently alternate, and the causal dynamics are non-empty. The
cause exists but is suppressed — this is an **anticausative**, not a
lexically noncausative. -/

/-- Intr-*push open* has non-empty dynamics; *freeze solid* has empty.
    This is the formal reflex of the paper's central claim. -/
theorem push_open_not_like_freeze_solid :
    pushDoorOpenModel.laws.length > 0 ∧
    freezeSolidModel.laws.length = 0 := by
  constructor <;> decide

/-- *Freeze* independently shows the causative alternation;
    *push* does not. This confirms the classification: *freeze solid*
    is a standard noncausative resultative with an alternating verb,
    while *push open* must be an anticausative licensed by the
    construction. -/
theorem freeze_alternates_push_does_not :
    LevinClass.otherCoS.participatesIn .causativeInchoative = true ∧
    LevinClass.pushPull.participatesIn .causativeInchoative = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Proper Containment Condition ↔ tightness
-- ════════════════════════════════════════════════════

/-! ## PCC and the independent-source analysis

The Proper Containment Condition (@cite{rappaport-hovav-levin-2012}):
"When a change of state is properly contained within a causing act,
the argument representing that act must be expressed in the same clause
as the verb describing the change of state."

This maps onto the **independent-source/tightness** analysis already
formalized in `Causation/Resultatives.lean`:

- **Projectile** (door after a push): the door has kinetic energy —
  an **independent source**. Once pushed, the door continues to swing
  without the agent. The agent's involvement is NOT continuously
  required. → The theme has an independent source → the cause is
  not necessary → anticausative OK.

- **Continuous involvement** (nailing a door shut): the agent must
  sustain force throughout. The door has NO independent source of
  motion. → No independent source → the cause IS necessary → the
  anticausative is blocked (PCC requires expressing the cause). -/

private def agentForceVar : Variable := mkVar "agent_force"
private def themeMomentumVar : Variable := mkVar "theme_momentum"
private def resultStateVar : Variable := mkVar "result_state"

/-- Projectile model: agent applies force → theme gains momentum →
    theme reaches result state. The theme's momentum is an independent
    source (kinetic energy persists after the push). -/
def projectileModel : CausalDynamics :=
  ⟨[ CausalLaw.simple agentForceVar themeMomentumVar
   , CausalLaw.simple themeMomentumVar resultStateVar ]⟩

/-- Continuous-involvement model: agent applies force → result state
    directly. No intermediate with independent energy. -/
def continuousModel : CausalDynamics :=
  ⟨[CausalLaw.simple agentForceVar resultStateVar]⟩

/-- In the projectile model, the theme's momentum is NOT an independent
    source (no separate law feeds it — the agent's push IS the source).
    But the crucial point is architectural: the intermediate stage
    (momentum) means the agent can withdraw after the initial force
    application. -/
theorem projectile_tight_from_empty_bg :
    completesForEffect projectileModel Situation.empty
      agentForceVar resultStateVar = true := by
  native_decide

/-- In the continuous model, the agent IS the completion event. -/
theorem continuous_tight :
    completesForEffect continuousModel Situation.empty
      agentForceVar resultStateVar = true := by
  native_decide

/-- When the theme has its OWN independent energy source (separate from
    the agent's push), the agent's force is no longer necessary — the
    theme can reach the result state on its own. This is what licenses
    the anticausative: the cause can be suppressed because the theme
    doesn't need it continuously.

    This connects to `independent_source_disrupts_tightness` in
    `Causation/Resultatives.lean`: an independent source for the
    intermediate breaks necessity. -/
private def themeEnergyVar : Variable := mkVar "theme_energy"

def projectileWithEnergyModel : CausalDynamics :=
  ⟨[ CausalLaw.simple agentForceVar themeMomentumVar
   , CausalLaw.simple themeMomentumVar resultStateVar
   , CausalLaw.simple themeEnergyVar themeMomentumVar ]⟩

def themeHasEnergyBg : Situation :=
  Situation.empty.extend themeEnergyVar true

/-- When the theme has independent energy, the agent's force is no
    longer necessary — the theme can reach the result state on its own.
    `completesForEffect` = false because necessity fails. -/
theorem projectile_energy_breaks_necessity :
    completesForEffect projectileWithEnergyModel themeHasEnergyBg
      agentForceVar resultStateVar = false := by
  native_decide

/-- The theme's momentum HAS an independent source in this model. -/
theorem theme_has_independent_source :
    hasIndependentSource projectileWithEnergyModel
      agentForceVar themeMomentumVar = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 6. Discourse licensing conditions
-- ════════════════════════════════════════════════════

/-! ## Anticausative discourse conditions

@cite{rappaport-hovav-2014} identifies two discourse situations where
the anticausative variant is preferred over the causative:

1. The cause is **recoverable** from the discourse context — it has been
   established earlier or follows from the natural course of events
   (§5, examples 62–68).
2. The speaker **does not know** the identity of the cause — the
   existence of a cause can be inferred but its identity is unknown
   (§5, examples 69–71; McCawley 1978).

Intr-*push open* resultatives are found in precisely these two contexts. -/

/-- How the cause relates to the discourse context. -/
inductive CauseStatus where
  /-- Cause established in prior discourse or natural course of events.
      "The dry soil thawed ... the roots pulled free." (§5, ex. 64) -/
  | recoverableInContext
  /-- Cause inferable but identity unknown to speaker.
      "The door pushed open and a man walked in." (§5, ex. 70) -/
  | identityUnknown
  /-- Cause novel and not recoverable; causative variant required. -/
  | notRecoverable
  deriving DecidableEq, Repr

/-- The anticausative variant is licensed when the cause is
    recoverable or unknown. -/
def anticausativeLicensed : CauseStatus → Bool
  | .recoverableInContext => true
  | .identityUnknown      => true
  | .notRecoverable       => false

theorem recoverable_licenses : anticausativeLicensed .recoverableInContext = true := rfl
theorem unknown_licenses : anticausativeLicensed .identityUnknown = true := rfl
theorem not_recoverable_blocks : anticausativeLicensed .notRecoverable = false := rfl

-- ════════════════════════════════════════════════════
-- § 7. Semantic licensing: autonomous motion
-- ════════════════════════════════════════════════════

/-! ## The projectile property

The subject DP must be capable of **autonomous motion**: it must be
able to move along the trajectory defined by the result state without
requiring an external agent's sustained participation (§6).

The attested subjects qualify as "projectiles" (@cite{kearns-2000}):
entities that move due to their own kinetic energy and can impart
this energy to another entity through contact. This includes entities
that are not machines but are construed as force-imbued (doors after
a push, corks in bottles, roots in thawing soil).

The same types of entities pass the "What X did" diagnostic for
effectors (fn. 17): agents, natural forces, machines, and projectiles. -/

/-- Classification of the theme (subject DP). -/
inductive ThemeMotionCapacity where
  /-- Self-energetic entity (agent, animal). -/
  | animate
  /-- Machine with independent power source (tractor, vehicle). -/
  | machine
  /-- Entity imbued with force via the verbal action: after a push,
      the door continues to swing without the agent's involvement.
      Includes entities construed as moving under transferred kinetic
      energy (doors, corks, roots, prongs). -/
  | projectile
  /-- Entity requiring continuous external manipulation to move:
      nails being hammered, instruments being wielded. -/
  | requiresContinuousForce
  deriving DecidableEq, Repr

/-- Whether a theme can serve as subject of intr-*push open*. -/
def canBeIntrPushOpenSubject : ThemeMotionCapacity → Bool
  | .animate                 => true
  | .machine                 => true
  | .projectile              => true
  | .requiresContinuousForce => false

theorem projectile_licenses : canBeIntrPushOpenSubject .projectile = true := rfl
theorem animate_licenses : canBeIntrPushOpenSubject .animate = true := rfl
theorem machine_licenses : canBeIntrPushOpenSubject .machine = true := rfl

/-- Entities requiring continuous external manipulation are blocked.
    "My father nailed the door shut" (§6, ex. 74) is OK, but
    "*The root cellar door nailed shut" (§6, ex. 75) is unacceptable. -/
theorem continuous_force_blocks :
    canBeIntrPushOpenSubject .requiresContinuousForce = false := rfl

-- ════════════════════════════════════════════════════
-- § 8. Directed motion event descriptions
-- ════════════════════════════════════════════════════

/-! ## Connection to directed motion

The same verbs appear intransitively in directed motion event
descriptions (§7, examples 84–85):
- "The tennis ball slammed into the net." (84a)
- "The chair scraped across the floor." (84b)

These share the same licensing condition: the theme must be capable
of autonomous motion. This provides independent support.

Note: natural forces (*storm*, *wind*) are attested as subjects of
directed motion (85b) but NOT of intr-*push open* resultatives,
because the relevant adjectives cannot be predicated of them
(*\*an open storm/wind*). -/

/-- A directed motion event description with a surface-contact verb. -/
structure DirectedMotionDatum where
  verb : String
  sentence : String
  themeType : ThemeMotionCapacity
  deriving Repr, BEq

def ball_slammed : DirectedMotionDatum :=
  { verb := "slam", sentence := "The tennis ball slammed into the net."
  , themeType := .projectile }

def chair_scraped : DirectedMotionDatum :=
  { verb := "scrape", sentence := "The chair scraped across the floor."
  , themeType := .projectile }

def horse_banged : DirectedMotionDatum :=
  { verb := "bang", sentence := "The run-away horse banged into the fence."
  , themeType := .animate }

def truck_smacked : DirectedMotionDatum :=
  { verb := "smack", sentence := "The truck smacked into the retaining wall."
  , themeType := .machine }

def directedMotionData : List DirectedMotionDatum :=
  [ball_slammed, chair_scraped, horse_banged, truck_smacked]

/-- All directed motion themes satisfy the autonomous motion condition,
    paralleling intr-*push open*. -/
theorem directed_motion_themes_autonomous :
    directedMotionData.all (canBeIntrPushOpenSubject ·.themeType) = true := by
  native_decide

/-! Natural forces (*storm*, *wind*) are attested as directed motion
subjects — (85b) "The storm swept through the valley" — but NOT in
intr-*push open* resultatives. The blocking mechanism is the adjective
restriction: the relevant adjectives cannot be predicated of natural
forces (*\*an open storm*), so no licensed verb–adjective combination
exists. The theme passes the autonomous motion test but the adjective
filter blocks it independently. -/

-- ════════════════════════════════════════════════════
-- § 9. Full licensing condition
-- ════════════════════════════════════════════════════

/-! ## The licensing conjunction

An intr-*push open* resultative is licensed iff ALL of:
1. The verb is from a force-application class (§12, §18)
2. The adjective describes a spatially instantiated state
3. The discourse context licenses cause suppression
4. The theme is capable of autonomous motion -/

/-- Full licensing check for an intr-*push open* resultative. -/
def isLicensed (verbClass : LevinClass) (adj : AdjectivalPredicateEntry)
    (causeStatus : CauseStatus) (theme : ThemeMotionCapacity) : Bool :=
  intrPushOpenClasses.contains verbClass &&
  adj.spatialConfigType.isSome &&
  anticausativeLicensed causeStatus &&
  canBeIntrPushOpenSubject theme

/-- "The door pushed open" in a recoverable-cause context is licensed. -/
theorem door_pushed_open_licensed :
    isLicensed .pushPull open_ .recoverableInContext .projectile = true := by
  native_decide

/-- "The door pushed open" in a cause-unknown context is licensed. -/
theorem door_pushed_open_licensed_unknown :
    isLicensed .pushPull open_ .identityUnknown .projectile = true := by
  native_decide

/-- Blocked: cause not recoverable. -/
theorem blocked_no_context :
    isLicensed .pushPull open_ .notRecoverable .projectile = false := by
  native_decide

/-- Blocked: theme requires continuous force (PCC). -/
theorem blocked_continuous_force :
    isLicensed .pushPull open_ .recoverableInContext
      .requiresContinuousForce = false := by
  native_decide

/-- Blocked: verb class wrong (break is a CoS verb, not force). -/
theorem blocked_wrong_verb_class :
    isLicensed .break_ open_ .recoverableInContext .projectile = false := by
  native_decide

/-- Blocked: adjective not spatially instantiated (*red* has no spatial config). -/
private def red_ : AdjectivalPredicateEntry where
  form := "red"; scaleType := .closed; dimension := .color

theorem blocked_wrong_adjective :
    isLicensed .pushPull red_ .recoverableInContext .projectile = false := by
  native_decide

/-! ### End-to-end: the full argument chain

1. *push* is pushPull (§12) → pure manner, no CoS, no causation
2. No causative alternation for pushPull alone (meaning-component prediction)
3. **Fusion**: resultative construction adds CoS + causation → composed
   meaning now predicts the causative alternation
4. Resultative construction adds CAUSE (non-empty CausalDynamics)
5. Constructional BECOME = inception (CoSType.inception)
6. Constructional CAUSE = `.make` (sufficiency, completion event)
7. Anticausative: cause suppressed under discourse licensing
8. PCC: projectile has independent energy → cause not continuously needed
9. Theme passes autonomous-motion check → anticausative OK -/

theorem end_to_end_push_open :
    -- Step 1-2: verb class blocks alternation alone
    LevinClass.pushPull.participatesIn .causativeInchoative = false ∧
    LevinClass.rootEntailments .pushPull == .pureManner ∧
    -- Step 3: fusion — construction adds CoS + causation → alternation predicted
    predictedAlternationInConstruction
      LevinClass.pushPull.meaningComponents
      resultative .causativeInchoative = true ∧
    -- Step 4: construction adds CAUSE (non-empty dynamics)
    pushDoorOpenModel.laws.length > 0 ∧
    -- Step 5: BECOME = inception
    resultativeBECOME == .inception ∧
    -- Step 6: CAUSE = .make (sufficiency)
    resultativeCausativeBuilder == .make ∧
    -- Step 7: discourse licenses anticausative
    anticausativeLicensed .recoverableInContext = true ∧
    -- Step 8-9: theme is projectile → autonomous motion OK
    canBeIntrPushOpenSubject .projectile = true := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> decide

-- ════════════════════════════════════════════════════
-- § 10. Filled resultative: construction–verb–adjective bundle
-- ════════════════════════════════════════════════════

/-! ## FilledResultative: unifying the Boolean and structural layers

The construction grammar layer (MeaningComponents, fusion, alternation prediction)
and the causation layer (CausalDynamics, sufficiency, necessity, tightness) run
in parallel. `FilledResultative` bundles them into a single type where their
agreement is a proof obligation — not an informal invariant.

This is the formal reflex of @cite{levin-2026}'s analysis: a resultative
is a **construction filled with specific lexical material** (verb class,
adjective), and the filling must satisfy both the Boolean-level alternation
prediction and the structural-level causal dynamics. -/

/-- A resultative construction instantiated with its lexical fillers.

Bundles the three components of @cite{levin-2026}'s analysis:
1. **Verb class** — contributes manner semantics (force application)
2. **Adjective** — contributes result state (spatially instantiated)
3. **Construction** — contributes CAUSE + CoS (event structure)

Plus the causal dynamics that model HOW the causation works.
The proof fields enforce consistency across the Boolean and structural layers. -/
structure FilledResultative where
  /-- The verb's Levin class (manner root) -/
  verbClass : LevinClass
  /-- The result-state adjective (from Fragment) -/
  adjective : AdjectivalPredicateEntry
  /-- The argument structure construction (typically `resultative`) -/
  construction : ArgStructureConstruction
  /-- The structural causal model for this verb–result combination -/
  dynamics : CausalDynamics
  /-- The construction adds what the verb lacks: fusion predicts the
      causative alternation for the composed meaning. -/
  alternationPredicted :
    predictedAlternationInConstruction
      verbClass.meaningComponents construction .causativeInchoative = true
  /-- The adjective describes a spatially instantiated state. -/
  adjSpatial : adjective.spatialConfigType.isSome = true
  /-- The Boolean and structural causation layers agree. -/
  causalConsistency : causationConsistent construction dynamics = true

/-- Whether this filled resultative can surface as an anticausative
    (intr-*push open*), given discourse and theme conditions.
    Checks the verb class restriction in addition to discourse/theme. -/
def FilledResultative.canAnticausativize (fr : FilledResultative)
    (cause : CauseStatus) (theme : ThemeMotionCapacity) : Bool :=
  intrPushOpenClasses.contains fr.verbClass &&
  anticausativeLicensed cause &&
  canBeIntrPushOpenSubject theme

/-! ### Concrete instances -/

/-- *push open*: pushPull + open + resultative + push-door-open dynamics. -/
def pushOpen_filled : FilledResultative :=
  { verbClass := .pushPull
  , adjective := open_
  , construction := resultative
  , dynamics := pushDoorOpenModel
  , alternationPredicted := by native_decide
  , adjSpatial := by native_decide
  , causalConsistency := by native_decide }

/-- *pull free*: pushPull + free + resultative. -/
def pullFree_filled : FilledResultative :=
  { verbClass := .pushPull
  , adjective := free_
  , construction := resultative
  , dynamics := pushDoorOpenModel  -- same causal shape: force → result
  , alternationPredicted := by native_decide
  , adjSpatial := by native_decide
  , causalConsistency := by native_decide }

/-- *slam shut*: hit + shut + resultative. -/
def slamShut_filled : FilledResultative :=
  { verbClass := .hit
  , adjective := shut
  , construction := resultative
  , dynamics := pushDoorOpenModel
  , alternationPredicted := by native_decide
  , adjSpatial := by native_decide
  , causalConsistency := by native_decide }

/-! ### FilledResultative → licensing

The `isLicensed` function and the `FilledResultative` type encode the same
conditions from different angles. `isLicensed` is a flat Boolean check;
`FilledResultative` bundles the conditions as proof obligations. The bridge
theorem shows they agree: any `FilledResultative` with appropriate discourse
and theme conditions passes `isLicensed`. -/

/-- A `FilledResultative` whose verb class is in `intrPushOpenClasses`
    passes `isLicensed` for any licensed cause status and theme. -/
theorem filled_implies_licensed (fr : FilledResultative)
    (cause : CauseStatus) (theme : ThemeMotionCapacity)
    (hClass : intrPushOpenClasses.contains fr.verbClass = true)
    (hCause : anticausativeLicensed cause = true)
    (hTheme : canBeIntrPushOpenSubject theme = true) :
    isLicensed fr.verbClass fr.adjective cause theme = true := by
  unfold isLicensed
  rw [hClass, hCause, hTheme]
  simp [fr.adjSpatial]

/-- Concrete: `pushOpen_filled` passes `isLicensed` in a recoverable-cause,
    projectile context. -/
theorem pushOpen_filled_licensed :
    isLicensed pushOpen_filled.verbClass pushOpen_filled.adjective
      .recoverableInContext .projectile = true := by
  native_decide

/-- The anticausative of `pushOpen_filled` is licensed in the right
    discourse context. -/
theorem pushOpen_anticausative_licensed :
    pushOpen_filled.canAnticausativize .recoverableInContext .projectile = true := by
  native_decide

/-- The anticausative is blocked when the cause is not recoverable. -/
theorem pushOpen_anticausative_blocked_no_context :
    pushOpen_filled.canAnticausativize .notRecoverable .projectile = false := by
  native_decide

/-- The anticausative is blocked when the theme requires continuous force. -/
theorem pushOpen_anticausative_blocked_continuous :
    pushOpen_filled.canAnticausativize .recoverableInContext
      .requiresContinuousForce = false := by
  native_decide

/-! ### FilledResultative ↔ end-to-end chain

The `end_to_end_push_open` theorem proved 9 conjuncts individually.
`pushOpen_filled` encodes three of those (alternation prediction,
spatial adjective, causal consistency) as proof obligations on the type.
The remaining conditions (discourse, theme) are runtime parameters. -/

/-- `pushOpen_filled` subsumes the core of `end_to_end_push_open`:
    the type's proof obligations cover steps 1-6. -/
theorem pushOpen_filled_covers_core :
    -- From alternationPredicted: steps 1-3 (verb blocked alone → construction enables)
    predictedAlternationInConstruction
      pushOpen_filled.verbClass.meaningComponents
      pushOpen_filled.construction .causativeInchoative = true ∧
    -- From causalConsistency: step 4 (non-empty dynamics)
    causationConsistent pushOpen_filled.construction pushOpen_filled.dynamics = true ∧
    -- From adjSpatial: step 2 (adjective spatial)
    pushOpen_filled.adjective.spatialConfigType.isSome = true := by
  exact ⟨pushOpen_filled.alternationPredicted,
         pushOpen_filled.causalConsistency,
         pushOpen_filled.adjSpatial⟩

/-! ### Connection to ResultativeType

Intr-*push open* resultatives are `anticausativeProperty` in the
Goldberg & Jackendoff typology (added to `ResultativeType` for
@cite{levin-2026}). This closes the loop between the `FilledResultative`
type and the broader resultative classification. -/

/-- Map a `FilledResultative` to its `ResultativeType`.
    All intr-*push open* resultatives are anticausative property resultatives:
    the verb is transitive-only, the adjective heads a property result phrase,
    and the cause is suppressed. The transitive counterpart (tr-*push open*)
    would be `causativeProperty`, but is modeled separately. -/
def filledToResultativeType (_ : FilledResultative) :
    ResultativeType :=
  .anticausativeProperty

/-- Anticausative property is distinct from noncausative property
    (freeze solid): the former has a suppressed cause, the latter
    has no constructional cause at all. -/
theorem anticausative_not_noncausative :
    filledToResultativeType pushOpen_filled ≠
    ResultativeType.noncausativeProperty := by
  decide

-- ════════════════════════════════════════════════════
-- § 11. Cross-linguistic: Mandarin tuī-kāi 推开
-- ════════════════════════════════════════════════════

/-! ## Mandarin cognate

The paper (§1) motivates the English analysis by drawing parallels to
Mandarin, where the verb *tuī* "push" similarly cannot occur intransitively
outside resultative constructions (example 4: *tuī fān* "push-upend";
examples 5–6 show *tuī* alone cannot appear intransitively).
The Mandarin cognate compound *tuī-kāi* "push-open" exists
as a V-V compound in the Fragment — this bridge connects it to the English
analysis. -/

/-- The Mandarin push-open compound is the cross-linguistic cognate:
    same verb meaning (push), same result meaning (open), object-oriented. -/
theorem mandarin_tui_kai_is_cognate :
    Fragments.Mandarin.Resultatives.tui_kai.gloss = "push-open" ∧
    Fragments.Mandarin.Resultatives.tui_kai.orientation = .objectOriented := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § Fragment–Theory Bridge
-- ════════════════════════════════════════════════════

open Fragments.English.Predicates.Verbal (make cause)
open Semantics.Causation.Resultatives (resultativeCausativeBuilder)

/-- Resultative CAUSE matches the Fragment entry for "make". -/
theorem resultative_cause_matches_make_verb :
    make.causative = some resultativeCausativeBuilder := rfl

/-- Resultative CAUSE ≠ "cause" verb (`.make` ≠ `.cause`). -/
theorem resultative_cause_differs_from_cause_verb :
    cause.causative ≠ some resultativeCausativeBuilder := by
  decide

end Levin2026
