import Linglib.Theories.Semantics.Modality.Narrog
import Linglib.Phenomena.Modality.ComparePosition

/-!
# Narrog (2012): Modality, Subjectivity, and Semantic Change
@cite{narrog-2012}

Study file formalizing the core contributions of @cite{narrog-2012} beyond
what is already captured in `Semantics.Modality.Narrog` (the 2D/3D semantic
map) and `Diachronic.ModalChange` (Bybee et al. data + directionality).

## New contributions formalized here

1. **Category hierarchy** (Tables 3.5–3.9): an empirically-derived scope
   hierarchy from Japanese data, finer-grained than @cite{cinque-1999}'s
   stipulated universal hierarchy. Categories at the bottom (voice, aspect)
   are event-oriented; categories at the top (mood, illocutionary
   modification) are speech-act-oriented.

2. **Source and target categories** (Table 3.10): which grammatical
   categories serve as diachronic sources, targets, or both for modality.

3. **Category-climbing hypothesis** (§3.3.1): semantic change involving
   grammatical categories proceeds from narrow-scope to wide-scope — i.e.,
   from lower to higher in the hierarchy.

4. **Bridge: Narrog → Hacquard** (our construction): the event-oriented /
   speech-act-oriented cut in Narrog's hierarchy aligns with
   @cite{hacquard-2006}'s AspP boundary. Categories below the boundary lack
   propositional content; categories above it have content. This unifies the
   diachronic (Narrog) and synchronic (Hacquard) perspectives. Narrog does
   not explicitly make this connection; we construct it here.

5. **Subjectification stages for English modals** (Table 3.3): Langacker's
   three stages of modal development, mapped to `SpeakerOrientationLevel`.
-/

namespace Narrog2012

open Semantics.Modality.Narrog
open Semantics.Modality.EventRelativity (ModalPosition EventBinder)


-- ============================================================================
-- §1. Category Hierarchy (Tables 3.5–3.9)
-- ============================================================================

/-- Grammatical categories relevant to the verbal clause, drawn from
    @cite{narrog-2012} Tables 3.5–3.9 and @cite{narrog-2009a}.

    The categories are ordered by empirical scope from Japanese data:
    lower scope (event-oriented) to wider scope (speech-act-oriented).
    Categories at the same scope level are grouped into a shared
    `scopeLevel`. -/
inductive GramCategory where
  | voice              -- passive, causative (lowest scope)
  | benefactive        -- benefactive applicatives
  | phasalAspect       -- begin, continue, finish
  | dynamicModality    -- ability, volition (boulomaic)
  | perfImperfAspect   -- perfective/imperfective
  | deontic1           -- necessity: must, have to
  | evidentiality1     -- predictive appearance
  | negation           -- internal negation
  | epistemic1         -- necessity/expectation
  | evidentiality2     -- inferential evidentiality
  | tense              -- past, present, future
  | deontic2           -- valuative obligation, recommendation
  | epistemic2         -- possibility
  | evidentiality3     -- reportive
  | epistemic3         -- speculative, epistemic mood
  | volitiveMood       -- imperative, hortative
  | illocutionaryMod   -- sentence-final particles, tag questions (widest scope)
  deriving DecidableEq, Repr

/-- Empirical scope level from Japanese data (@cite{narrog-2009a},
    @cite{narrog-2012} Tables 3.5–3.7, 3.9). Lower number = narrower scope.

    Multiple categories can share a level; the ordering between
    categories at the same level is not empirically established.

    Level assignments follow the groupings established in the text (p. 97):
    "Evidentiality 3 and Epistemic modality 2... are located on the same
    level as Tense"; "Epistemic modality 1 and Evidentiality 2... are
    located at the same level as (Internal) negation." Non-modal anchors
    (Tense, Negation, Perf/Imperf, Phasal aspect) and the modal categories
    listed alongside them share the same level. -/
def GramCategory.scopeLevel : GramCategory → Nat
  | .voice | .benefactive                                     => 0
  | .phasalAspect | .dynamicModality                          => 1
  | .perfImperfAspect | .deontic1 | .evidentiality1           => 2
  | .negation | .epistemic1 | .evidentiality2                 => 3
  | .tense | .deontic2 | .epistemic2 | .evidentiality3        => 4
  | .epistemic3 | .volitiveMood                               => 5
  | .illocutionaryMod                                         => 6

instance : LE GramCategory where le a b := a.scopeLevel ≤ b.scopeLevel
instance : LT GramCategory where lt a b := a.scopeLevel < b.scopeLevel

instance (a b : GramCategory) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.scopeLevel ≤ b.scopeLevel))

instance (a b : GramCategory) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.scopeLevel < b.scopeLevel))

/-- Epistemic modality outscopes deontic modality — the basic observation
    that all three frameworks (Cinque, Hacquard, Narrog) agree on. -/
theorem epistemic_outscopes_deontic : GramCategory.deontic1 < GramCategory.epistemic1 := by
  decide

/-- Dynamic modality (ability) has narrower scope than deontic. -/
theorem dynamic_below_deontic : GramCategory.dynamicModality < GramCategory.deontic1 := by
  decide

/-- Mood outscopes all levels of modality proper. -/
theorem mood_outscopes_modality :
    GramCategory.epistemic3 ≤ GramCategory.volitiveMood ∧
    GramCategory.deontic2 < GramCategory.volitiveMood := by
  exact ⟨by decide, by decide⟩

/-- Illocutionary modification is the widest-scope category. -/
theorem im_is_widest (c : GramCategory) : c ≤ GramCategory.illocutionaryMod := by
  cases c <;> decide

-- ============================================================================
-- §2. Speaker-Orientation by Scope Level
-- ============================================================================

/-- Map a category to its speaker-orientation level in Narrog's 2D map.

    Categories below the aspect boundary are event-oriented; categories
    at the modal level are speaker-oriented; mood and IM are mood-level.

    At scope level 2, event-oriented (perfective aspect) and speaker-oriented
    (deontic 1, evidentiality 1) categories coexist, reflecting Narrog's
    observation (p. 97, point 4) that volitive modalities rank low due to
    descriptive use. The mapping is therefore approximate at the
    event/speaker boundary; see `scope_implies_orientation` for the
    precise (strict `<`) relationship. -/
def GramCategory.toOrientation : GramCategory → SpeakerOrientationLevel
  | .voice | .benefactive | .phasalAspect | .dynamicModality
  | .perfImperfAspect => .eventOriented
  | .deontic1 | .deontic2 | .epistemic1 | .epistemic2
  | .evidentiality1 | .evidentiality2 | .evidentiality3
  | .negation | .tense => .speakerOriented
  | .epistemic3 | .volitiveMood | .illocutionaryMod => .mood

/-- Strict scope increase implies non-decreasing orientation.

    If category `a` is strictly narrower in scope than `b`, then `a`'s
    orientation is no higher than `b`'s. This is the formal link between
    Narrog's Hypothesis I (category climbing: narrow → wide scope) and
    Hypothesis II (event-oriented → speech-act-oriented).

    The theorem requires strict `<` rather than `≤` because at the
    boundary between event-oriented and speaker-oriented categories
    (scope level 2), perfective/imperfective aspect (event-oriented) and
    deontic modality 1 (speaker-oriented) share the same scope level.
    Narrog (p. 97, point 4) notes this: volitive categories rank low in
    the scope hierarchy due to their descriptive use, even though their
    performative use is high. -/
theorem scope_implies_orientation (a b : GramCategory) (h : a < b) :
    a.toOrientation ≤ b.toOrientation := by
  revert h; cases a <;> cases b <;> decide

-- ============================================================================
-- §3. Source and Target Categories (Table 3.10)
-- ============================================================================

/-- Role of a grammatical category relative to modality in diachronic change.

    Based on @cite{narrog-2012} Table 3.10 (p. 113), which lists *non-modal*
    source, target, and bidirectional categories. Table 3.10 also includes
    categories not in our scope hierarchy: possession and directionals
    (sources), referent honorification (both), and politeness/addressee
    honorification (targets). Our `changeRole` function extends Table 3.10
    to the full `GramCategory` type by classifying modal categories (deontic,
    epistemic, evidentiality) as `.both`. -/
inductive ChangeRole where
  | source  -- lower scope: voice, benefactives (+ possession, directionals in Table 3.10)
  | target  -- higher scope: mood, IM (+ politeness/honorification in Table 3.10)
  | both    -- same level: aspect, tense, negation (+ referent honorification in Table 3.10)
  deriving DecidableEq, Repr

/-- Classification of categories by their diachronic role relative to
    modality. Extends @cite{narrog-2012} Table 3.10 to cover all
    `GramCategory` constructors (see `ChangeRole` docstring). -/
def GramCategory.changeRole : GramCategory → ChangeRole
  | .voice | .benefactive          => .source
  | .phasalAspect | .perfImperfAspect | .tense | .negation => .both
  | .dynamicModality | .deontic1 | .deontic2
  | .epistemic1 | .epistemic2 | .epistemic3
  | .evidentiality1 | .evidentiality2 | .evidentiality3 => .both
  | .volitiveMood | .illocutionaryMod => .target

/-- Every source category has strictly narrower scope than every target
    category. This is the structural precondition for category-climbing:
    semantic change from source to target always increases scope. -/
theorem source_below_target (c d : GramCategory)
    (hc : c.changeRole = .source) (hd : d.changeRole = .target) :
    c < d := by
  revert hc hd; cases c <;> cases d <;> decide

/-- All source categories are event-oriented; all target categories are
    at the mood level. The diachronic role aligns with the synchronic
    orientation: categories that *give rise to* modality sit at the event
    level, while categories that modality *develops into* sit at the
    speech-act level. -/
theorem source_is_event_oriented (c : GramCategory) (h : c.changeRole = .source) :
    c.toOrientation = .eventOriented := by
  revert h; cases c <;> decide

theorem target_is_mood (c : GramCategory) (h : c.changeRole = .target) :
    c.toOrientation = .mood := by
  revert h; cases c <;> decide

-- ============================================================================
-- §4. Bridge: Narrog Hierarchy → Hacquard Content Licensing (Our Construction)
-- ============================================================================

/-- Map Narrog's scope-based orientation to Hacquard's modal position.

    Event-oriented categories (scope levels 0–2, up to perfective aspect) map
    to Hacquard's `belowAsp`; speaker-oriented and mood categories map to
    `aboveAsp`. The AspP boundary is the empirical cut-point that both
    frameworks independently identify.

    **NB**: This bridge is our own construction. @cite{narrog-2012} compares
    his scope hierarchy to @cite{cinque-1999}'s in §3.2 but does not
    explicitly connect it to @cite{hacquard-2006}'s content licensing. The
    alignment is natural — both identify a boundary between event-level and
    propositional-level categories — but the formal mapping is ours. -/
def GramCategory.toHacquardPosition : GramCategory → ModalPosition
  | c => if c.toOrientation == .eventOriented then .belowAsp else .aboveAsp

/-- Event-oriented categories map to belowAsp (VP events, no content). -/
theorem event_oriented_below_asp :
    GramCategory.toHacquardPosition .voice = .belowAsp ∧
    GramCategory.toHacquardPosition .dynamicModality = .belowAsp ∧
    GramCategory.toHacquardPosition .perfImperfAspect = .belowAsp := by
  exact ⟨rfl, rfl, rfl⟩

/-- Speaker-oriented categories map to aboveAsp (contentful events). -/
theorem speaker_oriented_above_asp :
    GramCategory.toHacquardPosition .epistemic1 = .aboveAsp ∧
    GramCategory.toHacquardPosition .deontic1 = .aboveAsp ∧
    GramCategory.toHacquardPosition .evidentiality2 = .aboveAsp := by
  exact ⟨rfl, rfl, rfl⟩

/-- The Hacquard bridge preserves the epistemic/root prediction:
    epistemic categories map to aboveAsp (where Hacquard licenses epistemic),
    and dynamic/ability categories map to belowAsp (where Hacquard blocks
    epistemic). This is the key unification of the diachronic and synchronic
    perspectives. -/
theorem hacquard_narrog_agree_on_epistemic :
    -- Narrog: epistemic is speaker-oriented
    GramCategory.epistemic1.toOrientation = .speakerOriented ∧
    -- Hacquard: speaker-oriented → aboveAsp → epistemic available
    GramCategory.toHacquardPosition .epistemic1 = .aboveAsp ∧
    EventBinder.speechAct.canProjectEpistemic = true ∧
    -- Narrog: dynamic is event-oriented
    GramCategory.dynamicModality.toOrientation = .eventOriented ∧
    -- Hacquard: event-oriented → belowAsp → no epistemic
    GramCategory.toHacquardPosition .dynamicModality = .belowAsp ∧
    EventBinder.vpEvent.canProjectEpistemic = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §5. Category-Climbing Hypothesis (§3.3.1)
-- ============================================================================

/-! The category-climbing hypothesis — that cross-linguistic modal change
    always proceeds from narrow-scope (event-oriented) to wide-scope
    (speech-act-oriented) — is proved as `Diachronic.ModalChange.directionality`
    over the Bybee et al. (1994) dataset. The `source_below_target` theorem
    above establishes the structural precondition for this in our hierarchy:
    every source category is strictly below every target category. -/

-- ============================================================================
-- §6. Subjectification of English Modals (Table 3.3)
-- ============================================================================

/-- A stage in the diachronic development of English modals.
    @cite{narrog-2012} Table 3.3, following Langacker (1990; 1998; 1999). -/
structure ModalDevelopmentStage where
  stageLabel : String
  semanticChange : String
  historicalCorrelate : String
  orientation : SpeakerOrientationLevel
  deriving Repr

/-- Langacker's stages for English modal verbs (@cite{narrog-2012} Table 3.3).

    Stage I>II: Physical → social force (main verb → modal verb).
    Stage I>II: Potency source/target diffuse (main verb → modal verb).
    Stage II: Maximal diffusion = deontic → epistemic meaning.
    Stage II,III: Potency → speaker's knowledge (present-oriented epistemic).
    Stage II>III: Directed potency lost → grounding predications. -/
def langackerStages : List ModalDevelopmentStage :=
  [ ⟨"I>II", "domain of force shifts from physical to social",
    "main verb to modal verb", .eventOriented⟩
  , ⟨"I>II", "diffusion of source and target of potency",
    "main verb to modal verb", .eventOriented⟩
  , ⟨"II", "maximal diffusion of source and target of potency",
    "deontic to epistemic meaning", .speakerOriented⟩
  , ⟨"II,III", "potency pertains to evolution of speaker's knowledge of reality",
    "present-oriented epistemic meanings", .speakerOriented⟩
  , ⟨"II>III", "directed potency loses profiled status",
    "modals become grounding predications", .mood⟩
  ]

/-- The stages are monotonically non-decreasing in orientation —
    consistent with Narrog's directionality hypothesis. -/
theorem langacker_stages_monotone :
    langackerStages.Pairwise (λ a b => a.orientation ≤ b.orientation) := by
  simp [langackerStages]
  decide

-- ============================================================================
-- §7. Three Perspectives on Position-Flavor (Cinque, Hacquard, Narrog)
-- ============================================================================

/-- All three frameworks agree that epistemic is "higher" than root/dynamic,
    but for different reasons:

    - @cite{cinque-1999}: stipulated functional heads place epistemic above TP.
    - @cite{hacquard-2006}: content licensing blocks epistemic below AspP.
    - @cite{narrog-2012}: empirical scope data from Japanese places epistemic
      at scope levels 3–5 vs. dynamic at level 1.

    This theorem states the common prediction, which each framework derives
    differently. -/
theorem three_way_agreement_epistemic_above_root :
    -- Cinque: epistemic heads are high
    Phenomena.Modality.ComparePosition.CinqueModHead.modEpistemic.isHigh = true ∧
    -- Hacquard: high position licenses epistemic
    ModalPosition.aboveAsp.defaultBinder.canProjectEpistemic = true ∧
    -- Narrog: epistemic has higher scope level than dynamic
    GramCategory.dynamicModality < GramCategory.epistemic1 := by
  exact ⟨rfl, rfl, by decide⟩

-- ============================================================================
-- §8. Deriving Orientation from Flavor (ModalItem Bridge)
-- ============================================================================

/-- Derive a default speaker-orientation from a `ModalFlavor`.

    Epistemic modality is speaker-oriented (the speaker assesses likelihood).
    Deontic modality is speaker-oriented (the speaker imposes norms).
    Circumstantial modality is event-oriented (describes abilities/facts).

    This bridges the existing `ModalItem.meaning` (List ForceFlavor) data
    that fragment entries already carry to Narrog's orientation axis,
    without requiring changes to the `ModalItem` structure. -/
def orientationOfFlavor : Core.Modality.ModalFlavor → SpeakerOrientationLevel
  | .epistemic => .speakerOriented
  | .deontic => .speakerOriented
  | .bouletic => .speakerOriented
  | .circumstantial => .eventOriented

/-- Circumstantial-only modals are event-oriented. -/
theorem circumstantial_is_event_oriented :
    orientationOfFlavor .circumstantial = .eventOriented := rfl

/-- Epistemic modals are speaker-oriented. -/
theorem epistemic_is_speaker_oriented :
    orientationOfFlavor .epistemic = .speakerOriented := rfl

/-- The consistency claim holds for flavors in Narrog's image.
    Bouletic collapses with deontic in Narrog's 2D space (both volitive,
    speaker-oriented), so the round-trip from `.bouletic` yields `.deontic`. -/
theorem orientationOfFlavor_consistent :
    ∀ f : Core.Modality.ModalFlavor, f ≠ .bouletic →
      ∃ r : NarrogRegion, r.toModalFlavor = some f ∧
        r.orientation = orientationOfFlavor f := by
  intro f hf; cases f with
  | epistemic => exact ⟨⟨.nonVolitive, .speakerOriented⟩, rfl, rfl⟩
  | deontic => exact ⟨⟨.volitive, .speakerOriented⟩, rfl, rfl⟩
  | bouletic => exact absurd rfl hf
  | circumstantial => exact ⟨⟨.nonVolitive, .eventOriented⟩, rfl, rfl⟩

/-- `toHacquardPosition` factors through `toOrientation` and
    `ComparePosition.narrogOrientationToPosition`. This links the category-level
    bridge (§4) to the orientation-level bridge in `ComparePosition`. -/
theorem toHacquardPosition_factors (c : GramCategory) :
    c.toHacquardPosition =
      Phenomena.Modality.ComparePosition.narrogOrientationToPosition c.toOrientation := by
  cases c <;> rfl

end Narrog2012
