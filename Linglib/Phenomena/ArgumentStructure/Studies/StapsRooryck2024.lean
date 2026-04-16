import Linglib.Core.Semantics.Presupposition
import Linglib.Fragments.French.Predicates
import Linglib.Theories.Semantics.Lexical.Verb.Affectedness
import Linglib.Theories.Semantics.Tense.Aspect.LexicalAspect
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Staps & Rooryck (2024): Formalizing Spatial-Causal Polysemy of Agent Prepositions
@cite{staps-rooryck-2024}

Semantics and Pragmatics 17, Article 4, pp. 1–47.

## Core Claims

1. Agent prepositions (*by*, French *par*/*de*) are **not** semantically vacuous
   case markers. They have non-trivial semantic content derived from their
   spatial meanings via principled polysemy (@cite{tyler-evans-2003}).

2. The general denotation is **polymorphically typed**: ⟨η, ⟨θ, t⟩⟩, where
   η (Figure) and θ (Ground) are instantiated by the syntactic/semantic
   context. Spatial: ⟨e, ⟨e, t⟩⟩. Agentive: ⟨e, ⟨s, t⟩⟩.

3. French **par** ('through, via') presupposes **high** proto-agentivity;
   **de** ('from, of') presupposes **low** proto-agentivity. The relevant
   factors are: bringing about a change (§3.1), contextually inferred
   change (§3.2), volitionality (§3.3), and telicity (§3.4).

4. The same polymorphic mechanism extends to **causal adjuncts** (§2.3):
   *de* marks causes-as-situations (type ⟨s, ⟨s, t⟩⟩), *par* marks
   causes-as-forces (type ⟨f, ⟨s, t⟩⟩), following @cite{copley-harley-2022}.

## Formalization Strategy

Proto-agentivity is formalized via `EntailmentProfile.pAgentScore` and
the specific entailments {volition, causation, movement}. The prediction
is: *par* requires the subject to have at least one of these "active"
entailments; *de* is the default for low-agentivity subjects.

We derive the par/de preference from the verb's stored `EntailmentProfile`
and `VendlerClass`, connecting to the affectedness hierarchy
(@cite{beavers-2010}) and aspectual classification (@cite{vendler-1957}).

## Integration with linglib

- Subject profiles reuse canonical @cite{dowty-1991} profiles
  (`kickSubjectProfile`, `seeSubjectProfile`, `runSubjectProfile`)
  rather than duplicating them, making the connection structural.
- Passive voice connects to @cite{collins-2005}'s `voicePassive` —
  Case-checking by Voice is the syntactic correlate of the preposition's
  semantic contribution.
- Object affectedness derives from @cite{beavers-2010}'s `profileToDegree`.
-/

namespace StapsRooryck2024

open Core.Presupposition
open Fragments.French.Predicates
open Semantics.Lexical.Verb.EntailmentProfile
open Semantics.Lexical.Verb.Affectedness
open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Minimalism

-- ============================================================================
-- § 1. Polymorphic Preposition Types
-- ============================================================================

/-- Semantic domain types for preposition Figure/Ground arguments.
    The paper's ⟨η, ⟨θ, t⟩⟩ polymorphism: η and θ range over these
    domain types, constrained by the syntactic/semantic context. -/
inductive SemDomain where
  | e  -- Entity: concrete individuals
  | s  -- Eventuality: situations or events
  | f  -- Force: causal forces (@cite{copley-harley-2022})
  deriving DecidableEq, Repr

/-- A polymorphic preposition type: ⟨η, ⟨θ, t⟩⟩.
    The Figure (η) is the first argument; the Ground (θ) is the second. -/
structure PrepType where
  figure : SemDomain  -- η
  ground : SemDomain  -- θ
  deriving DecidableEq, Repr

/-- Spatial instantiation: ⟨e, ⟨e, t⟩⟩.
    "The house by the lake" — two entities in close proximity. -/
def spatialType : PrepType := ⟨.e, .e⟩

/-- Agentive instantiation: ⟨e, ⟨s, t⟩⟩.
    "Written by John" — entity in close proximity to event.
    Interpretation: Initiator(x, e). -/
def agentiveType : PrepType := ⟨.e, .s⟩

/-- Causal adjunct (force-based): ⟨f, ⟨s, t⟩⟩.
    French *par un tremblement de terre* — force in close proximity to
    situation. Used by *par* in causal adjuncts. -/
def causalForceType : PrepType := ⟨.f, .s⟩

/-- Causal adjunct (situation-based): ⟨s, ⟨s, t⟩⟩.
    French *de faim* — situation in close proximity to situation.
    Used by *de* in causal adjuncts. -/
def causalSituationType : PrepType := ⟨.s, .s⟩

theorem agentive_not_spatial : agentiveType ≠ spatialType := by decide
theorem causal_force_not_situation : causalForceType ≠ causalSituationType := by decide

-- ============================================================================
-- § 2. Proto-Agentivity Threshold
-- ============================================================================

/-- The "active" P-Agent entailments that drive *par* selection.
    §3.5 (34): change/causation, volitionality, and kinesis/movement are
    the three entailments that distinguish par-requiring from de-allowing
    contexts. These are a strict subset of @cite{dowty-1991}'s five
    P-Agent entailments — sentience and independent existence do NOT
    contribute to par selection (experiencers allow *de*).

    Note: the paper's (34) establishes a hierarchy among these factors:
    (34a) change is primary — if change is possible, par presupposes it;
    (34b) volitionality and telicity are secondary — relevant only when
    change is excluded. Our disjunction correctly predicts the binary
    par-required/de-available outcome for all attested verbs. -/
def hasActiveAgentEntailment (p : EntailmentProfile) : Bool :=
  p.volition || p.causation || p.movement

/-- *par* is required when the subject has active agent entailments.
    This is a necessary condition: *de* is RULED OUT for high-agentivity
    contexts, while *par* as the modern French default can appear even
    with low-agentivity Agents. -/
def predictsParRequired (p : EntailmentProfile) : Bool :=
  hasActiveAgentEntailment p

/-- *de* is available when active agent entailments are absent. -/
def predictsDeAvailable (p : EntailmentProfile) : Bool :=
  !hasActiveAgentEntailment p

/-- §3.5 (34): par and de are in complementary distribution w.r.t.
    proto-agentivity. Par implies change; de presupposes its absence.
    This is the paper's primary empirical generalization. -/
theorem par_de_complementary (p : EntailmentProfile) :
    predictsParRequired p = !predictsDeAvailable p := by
  simp [predictsParRequired, predictsDeAvailable, Bool.not_not]

-- ============================================================================
-- § 3. Per-Profile Predictions
-- ============================================================================

-- One theorem per unique profile, not per verb. The French verbs using
-- each profile are listed in the docstring.

/-- Canonical agents (laver, écrire, construire, tuer, abandonner,
    délaisser) have V+S+C+M+IE → par required. This is `kickSubjectProfile`
    from @cite{dowty-1991}. -/
theorem canonical_agent_requires_par :
    predictsParRequired protoTransSubjectProfile = true := by native_decide

/-- Experiencer subjects (aimer, adorer, respecter) have S+IE only →
    de available. This is `seeSubjectProfile` from @cite{dowty-1991}. -/
theorem experiencer_allows_de :
    predictsDeAvailable experiencerSubjectProfile = true := by native_decide

/-- Stative positional subjects (précéder, stative suivre) have IE
    only → de available. -/
theorem stative_positional_allows_de :
    predictsDeAvailable stativePositionalSubjectProfile = true := by native_decide

/-- Dynamic motion subjects (dynamic suivre) have V+S+M+IE → par
    required. This is `runSubjectProfile` from @cite{dowty-1991}. -/
theorem dynamic_motion_requires_par :
    predictsParRequired dynamicFollowSubjectProfile = true := by native_decide

/-- Accompany subjects have S+M+IE → par required (movement suffices). -/
theorem accompany_requires_par :
    predictsParRequired accompanySubjectProfile = true := by native_decide

-- ============================================================================
-- § 4. Aspectual Dimension: Telicity and Object Change
-- ============================================================================

/-- §3.4: Telicity influences par/de selection. Telic events imply
    a bounded change, which increases proto-agentivity. -/
def telicityFavorsPar (vc : VendlerClass) : Bool :=
  vc.telicity == .telic

theorem accomplishment_favors_par : telicityFavorsPar .accomplishment = true := rfl
theorem achievement_favors_par : telicityFavorsPar .achievement = true := rfl
theorem activity_no_telic_par : telicityFavorsPar .activity = false := rfl
theorem state_no_telic_par : telicityFavorsPar .state = false := rfl

/-- §3.1: Object affectedness also matters. Verbs with quantized or
    nonquantized affectedness entail a Patient change → forces *par*.
    Connects to @cite{beavers-2010}'s affectedness hierarchy. -/
def objectChangeFavorsPar (objProfile : EntailmentProfile) : Bool :=
  match profileToDegree objProfile with
  | .quantized | .nonquantized => true
  | .potential | .unspecified => false

-- laver object: CoS+CA → nonquantized → favors par.
theorem laver_object_favors_par :
    objectChangeFavorsPar protoTransObjectProfile = true := by native_decide

-- écrire object: CoS+IT+DE → quantized → favors par.
theorem ecrire_object_favors_par :
    objectChangeFavorsPar
      { protoTransObjectProfile with
        incrementalTheme := true, dependentExistence := true } = true := by
  native_decide

-- Stimulus object (psych verbs): IE only, no change → no par pressure.
theorem stimulus_no_object_par :
    objectChangeFavorsPar minimalParticipantProfile = false := by native_decide

-- ============================================================================
-- § 5. Combined Prediction
-- ============================================================================

/-- Full prediction combining subject proto-agentivity, object
    affectedness, and telicity. Any one factor suffices for *par*. -/
def predictsPar (v : FrenchVerbEntry) : Bool :=
  (v.subjectEntailments.map predictsParRequired |>.getD false) ||
  (v.objectEntailments.map objectChangeFavorsPar |>.getD false) ||
  (v.vendlerClass.map telicityFavorsPar |>.getD false)

-- Comprehensive classification: Table 1 verb classes.

/-- Par-required verbs: all have active agent entailments, affected
    objects, and/or telic aspect. -/
theorem par_verbs :
    predictsPar laver = true ∧ predictsPar ecrire = true ∧
    predictsPar construire = true ∧ predictsPar tuer = true ∧
    predictsPar abandonner = true ∧ predictsPar delaisser = true ∧
    predictsPar suivreDyn = true ∧ predictsPar accompagner = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Par/de verbs: experiencer and stative subjects lack active agent
    entailments, unaffected objects, and atelic aspect. -/
theorem de_available_verbs :
    predictsPar aimer = false ∧ predictsPar adorer = false ∧
    predictsPar respecter = false ∧ predictsPar preceder = false ∧
    predictsPar suivreStat = false :=
  ⟨by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide⟩

-- ============================================================================
-- § 6. Survey Data (Table 2)
-- ============================================================================

/-- Survey judgment: verb form, context agentivity level, and
    mean acceptability for *de* and *par* on [-1, 1] scale. -/
structure SurveyJudgment where
  verb : String
  context : String        -- "high" or "low" proto-agentivity context
  deMean : Int            -- scaled ×100 to avoid rationals for data
  parMean : Int           -- scaled ×100
  deriving Repr

/-- Survey data from @cite{staps-rooryck-2024} Table 2.
    Means are ×100 (e.g., 0.87 → 87, -0.96 → -96). -/
def surveyData : List SurveyJudgment := [
  -- § Causal adjuncts (§2.3)
  ⟨"mort", "de_causal", 100, -87⟩,         -- (13a): de=1.00, par=-0.87
  ⟨"cassée", "par_causal", -90, 37⟩,       -- (13b): de=-0.90, par=0.37
  -- § Change (§3.1): prototypically transitive, par only
  ⟨"lavé", "high", -96, 100⟩,              -- (1a): de=-0.96, par=1.00
  ⟨"maintenu", "high", -81, 100⟩,          -- (17): de=-0.81, par=1.00
  ⟨"suivie", "high", -45, 100⟩,            -- (19a): de=-0.45, par=1.00
  ⟨"traversé", "high", -77, 96⟩,           -- (19b): de=-0.77, par=0.96
  -- § Contextually implied change (§3.2): psych verbs
  ⟨"adorée", "low", 60, 77⟩,               -- (20a): de=0.60, par=0.77
  ⟨"adorée", "high", 50, 92⟩,              -- (20b): de=0.50, par=0.92
  ⟨"aimé", "low", 92, 70⟩,                 -- (21a): de=0.92, par=0.70
  ⟨"aimé", "high", 83, 77⟩,                -- (21b): de=0.83, par=0.77
  ⟨"respecté", "low", 77, 89⟩,             -- (22a): de=0.77, par=0.89
  ⟨"respecté", "high", 64, 81⟩,            -- (22b): de=0.64, par=0.81
  ⟨"accompagnés", "neutral", 87, 94⟩,      -- (2): de=0.87, par=0.94
  ⟨"accompagné", "high", 79, 96⟩,          -- (23a): de=0.79, par=0.96
  ⟨"accompagné", "low", 79, 89⟩,           -- (23b): de=0.79, par=0.89
  -- § Contextually implied change (§3.2): entourer (inanimate agent)
  ⟨"entouré", "low", 87, 73⟩,              -- (24a): de=0.87, par=0.73
  ⟨"entouré", "high", 79, 77⟩,             -- (24b): de=0.79, par=0.77
  -- § Volitionality (§3.3): suivre/précéder
  ⟨"précédé", "low", 83, 50⟩,              -- (25a): de=0.83, par=0.50
  ⟨"suivi", "high", 35, 98⟩,               -- (25b): de=0.35, par=0.98
  ⟨"suivi", "low", 98, 31⟩,                -- (26a): de=0.98, par=0.31
  ⟨"suivi", "high_2", 77, 64⟩,             -- (26b): de=0.77, par=0.64
  -- § Volitionality (§3.3): suivre with additional contexts
  ⟨"suivis", "low", 89, 50⟩,               -- (27a): de=0.89, par=0.50
  ⟨"suivis", "high", 77, 68⟩,              -- (27b): de=0.77, par=0.68
  ⟨"suivie", "low_2", 81, 71⟩,             -- (28a): de=0.81, par=0.71
  ⟨"suivie", "high_2", 73, 77⟩,            -- (28b): de=0.73, par=0.77
  ⟨"suivi", "high_3", 66, 98⟩,             -- (29): de=0.66, par=0.98
  -- § Telicity (§3.4): abandonner/délaisser
  ⟨"abandonnés", "high", -12, 100⟩,        -- (31a): de=-0.12, par=1.00
  ⟨"abandonnés", "low", -7, 92⟩,           -- (31b): de=-0.07, par=0.92
  ⟨"délaissée", "high", 10, 83⟩,           -- (32a): de=0.10, par=0.83
  ⟨"délaissé", "low", 28, 85⟩              -- (32b): de=0.28, par=0.85
]

/-- §3.1 Change-entailing verbs reject *de* (all deMean < 0).
    Filter restricts to the §3.1 items (high proto-agentivity context)
    to exclude §3.3 volitionality items with the same verb form. -/
theorem change_verbs_reject_de :
    (surveyData.filter (λ j =>
      (j.verb == "lavé" || j.verb == "maintenu" || j.verb == "traversé" ||
       (j.verb == "suivie" && j.context == "high")))
    ).all (λ j => j.deMean < 0) = true := by native_decide

/-- High-agentivity *suivi* prefers *par* (parMean > deMean). -/
theorem suivi_high_prefers_par :
    (surveyData.filter (λ j => j.verb == "suivi" && j.context == "high")
    ).all (λ j => j.parMean > j.deMean) = true := by native_decide

/-- Low-agentivity *suivi* prefers *de* (deMean > parMean). -/
theorem suivi_low_prefers_de :
    (surveyData.filter (λ j => j.verb == "suivi" && j.context == "low")
    ).all (λ j => j.deMean > j.parMean) = true := by native_decide

-- ============================================================================
-- § 7. Passive Voice Connection
-- ============================================================================

/-- The by-phrase is an argument of v, not an adjunct. In the passive,
    Voice checks Case but does not assign θ — the θ-role comes from v.
    The par/de preposition is the morphological spell-out of this
    Case-checking relationship, with the semantic contribution being
    Initiator(x,e) plus the proto-agentivity presupposition.

    This connects @cite{staps-rooryck-2024}'s §2.2 to
    @cite{collins-2005}'s passive structure: Voice_PASS checks Case
    while v assigns the external θ-role. -/
inductive FrenchAgentPrep where
  | par  -- 'through, via': high proto-agentivity presupposition
  | de   -- 'from, of': low proto-agentivity presupposition (default)
  deriving DecidableEq, Repr

/-- Both par and de in passives have agentive type ⟨e, ⟨s, t⟩⟩.
    They differ only in presupposition, not at-issue type. -/
def FrenchAgentPrep.passiveType : FrenchAgentPrep → PrepType
  | .par => agentiveType
  | .de  => agentiveType

/-- In causal adjuncts, par and de diverge in type:
    par: ⟨f, ⟨s, t⟩⟩ (forces), de: ⟨s, ⟨s, t⟩⟩ (situations). -/
def FrenchAgentPrep.causalType : FrenchAgentPrep → PrepType
  | .par => causalForceType
  | .de  => causalSituationType

theorem par_de_same_passive_type :
    FrenchAgentPrep.par.passiveType = FrenchAgentPrep.de.passiveType := rfl

theorem par_de_different_causal_type :
    FrenchAgentPrep.par.causalType ≠ FrenchAgentPrep.de.causalType := by decide

/-- The syntactic precondition for par/de: passive Voice checks Case
    (feature dissociation per @cite{collins-2005}), providing the
    structural position for the preposition. The par/de choice is
    then determined by proto-agentivity. -/
theorem passive_provides_case_position :
    voicePassive.checksCase = true ∧ voicePassive.assignsTheta = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 8. Causal Chain Distances (§3.5)
-- ============================================================================

/-- Position in the causal chain relative to the Patient.
    @cite{croft-2012}: *par* 'through' = perlative (path position),
    *de* 'from' = ablative (source position). Closer to Patient →
    more proto-agentive. -/
inductive CausalChainPosition where
  | source  -- Origin: ablative *de* 'from'
  | path    -- Intermediate: perlative *par* 'through'
  | goal    -- Endpoint: allative *à* 'to'
  deriving DecidableEq, Repr

/-- Distance from Patient: source > path > goal. -/
def CausalChainPosition.distance : CausalChainPosition → Nat
  | .source => 2
  | .path   => 1
  | .goal   => 0

def FrenchAgentPrep.causalPosition : FrenchAgentPrep → CausalChainPosition
  | .par => .path
  | .de  => .source

/-- Par has smaller causal distance → higher proto-agentivity. -/
theorem par_closer_than_de :
    FrenchAgentPrep.par.causalPosition.distance <
    FrenchAgentPrep.de.causalPosition.distance := by decide

-- ============================================================================
-- § 9. Cross-Theory Connections
-- ============================================================================

/-- Verbs with quantized object affectedness always require *par*.
    Quantized affectedness implies the subject causes a definite change
    (@cite{beavers-2010}). -/
theorem quantized_object_implies_par (obj : EntailmentProfile)
    (h : profileToDegree obj = .quantized) :
    objectChangeFavorsPar obj = true := by
  simp only [objectChangeFavorsPar, h]

/-- Dynamic VendlerClasses (activity, achievement, accomplishment)
    correlate with higher proto-agentivity than states — the
    stative/dynamic contrast driving *suivre*'s polysemy (§3.3). -/
theorem dynamic_vendler_implies_dynamicity (vc : VendlerClass)
    (h : vc.dynamicity = .dynamic) :
    vc = .activity ∨ vc = .achievement ∨ vc = .accomplishment ∨ vc = .semelfactive := by
  cases vc <;> simp [VendlerClass.dynamicity] at h ⊢

/-- §3.2 contextual enrichment gap: *adorer*'s lexical profile predicts
    de-availability, but high-agentivity contexts license *par* (survey
    data shows parMean > 0 in high context). `EntailmentProfile` alone
    cannot capture this — it requires pragmatic enrichment. -/
theorem adorer_lexical_not_par : predictsPar adorer = false := by native_decide

theorem adorer_contextual_par_ok :
    (surveyData.filter (λ j => j.verb == "adorée" && j.context == "high")
    ).all (λ j => j.parMean > 0) = true := by native_decide

/-- `stativePositionalSubjectProfile` is definitionally equal to
    `minimalParticipantProfile` — this is structural (via `abbrev`),
    not a coincidence. Both roles represent participants with only
    independent existence. -/
theorem stativePositional_is_minimal :
    stativePositionalSubjectProfile = minimalParticipantProfile := rfl

-- ============================================================================
-- § 10. Cross-Study: @cite{dowty-1991} P-Agent Score
-- ============================================================================

/-- The "active" agent entailments (V, C, M) are a strict subset of
    @cite{dowty-1991}'s full P-Agent set (V, S, C, M, IE). Profiles with
    active entailments always have pAgentScore ≥ 1, but the converse fails:
    experiencer profiles have pAgentScore = 2 (S+IE) yet no active
    entailments — which is exactly why they allow *de*. -/
theorem active_implies_pAgent_ge_1 (p : EntailmentProfile)
    (h : hasActiveAgentEntailment p = true) :
    p.pAgentScore ≥ 1 := by
  obtain ⟨v, s, c, m, ie, cos, it, ca, st, de⟩ := p
  simp only [hasActiveAgentEntailment] at h
  simp only [EntailmentProfile.pAgentScore]
  cases v <;> cases c <;> cases m <;> simp_all (config := { decide := false }) <;> omega

/-- Converse fails: experiencer profiles have pAgentScore ≥ 1 but no
    active agent entailments. This is the theoretical crux —
    @cite{staps-rooryck-2024}'s par/de distinction is sensitive to a
    narrower notion of agentivity than @cite{dowty-1991}'s full count. -/
theorem experiencer_high_pAgent_but_no_active :
    experiencerSubjectProfile.pAgentScore ≥ 1 ∧
    hasActiveAgentEntailment experiencerSubjectProfile = false :=
  ⟨by native_decide, by native_decide⟩

/-- Canonical agents have all three active entailments and the
    maximum pAgentScore of 5. This is the canonical case where
    @cite{staps-rooryck-2024}'s active-agent test and
    @cite{dowty-1991}'s full P-Agent count agree. -/
theorem canonical_agent_full_agreement :
    hasActiveAgentEntailment protoTransSubjectProfile = true ∧
    protoTransSubjectProfile.pAgentScore = 5 :=
  ⟨by native_decide, by native_decide⟩

-- ============================================================================
-- § 11. Formal Denotations (14)-(15), (35)
-- ============================================================================

/-! ### Proto-agentivity level

Binary classification grounding the par/de presupposition contrast.
Derived from `hasActiveAgentEntailment` — not independently stipulated. -/

/-- Binary proto-agentivity level for par/de presuppositions.
    HIGH = at least one of {V, C, M}; LOW = none. -/
inductive ProtoAgentivityLevel where
  | high  -- par: V ∨ C ∨ M
  | low   -- de: ¬(V ∨ C ∨ M)
  deriving DecidableEq, Repr

/-- Bridge from `EntailmentProfile` to binary agentivity level.
    Derived from `hasActiveAgentEntailment` (§2). -/
def profileToAgentivityLevel (p : EntailmentProfile) : ProtoAgentivityLevel :=
  if hasActiveAgentEntailment p then .high else .low

theorem canonical_agent_high :
    profileToAgentivityLevel protoTransSubjectProfile = .high := by native_decide
theorem experiencer_low :
    profileToAgentivityLevel experiencerSubjectProfile = .low := by native_decide
theorem stative_positional_low :
    profileToAgentivityLevel stativePositionalSubjectProfile = .low := by native_decide
theorem dynamic_follow_high :
    profileToAgentivityLevel dynamicFollowSubjectProfile = .high := by native_decide

/-! ### Agentive denotations (35a/35b)

The paper's key semantic contribution: par and de share at-issue content
(Initiator(x,e)) but carry complementary presuppositions about
proto-agentivity. Formalized using `PrProp W` from
`Core.Semantics.Presupposition`. -/

/-- Parameters for agentive preposition denotations (35a/35b).
    Bundled so the denotation is parametric over the event/entity model. -/
structure AgentivePrepParams (Entity Event : Type) (W : Type) where
  /-- The at-issue relation: Initiator(x, e). -/
  initiator : Entity → Event → W → Bool
  /-- Proto-agentivity predicate over entities (in context). -/
  highProtoAgentivity : Entity → W → Bool

variable {Entity Event W : Type}

/-- ⟦par⟧_agentive (35a): λx.λe. Initiator(x,e);
    presup: HIGH proto-agentivity(x). -/
def parAgentiveDenot (params : AgentivePrepParams Entity Event W)
    (x : Entity) (e : Event) : PrProp W :=
  .ofBool (params.highProtoAgentivity x) (params.initiator x e)

/-- ⟦de⟧_agentive (35b): λx.λe. Initiator(x,e);
    presup: LOW proto-agentivity(x). -/
def deAgentiveDenot (params : AgentivePrepParams Entity Event W)
    (x : Entity) (e : Event) : PrProp W :=
  .ofBool (λ w => !params.highProtoAgentivity x w) (params.initiator x e)

/-- Par and de share at-issue content — same assertion (Initiator(x,e)).
    This is structural: both constructors pass `params.initiator x e`
    to `PrProp.ofBool`'s second argument. -/
theorem par_de_same_assertion (params : AgentivePrepParams Entity Event W)
    (x : Entity) (e : Event) :
    (parAgentiveDenot params x e).assertion =
    (deAgentiveDenot params x e).assertion := rfl

/-- Par and de presuppositions are complementary: exactly one is
    satisfied at every world. -/
theorem par_de_presup_complementary (params : AgentivePrepParams Entity Event W)
    (x : Entity) (w : W) :
    params.highProtoAgentivity x w = true ↔
    ¬((!params.highProtoAgentivity x w) = true) := by
  cases params.highProtoAgentivity x w <;> simp

/-! ### Grounding: presuppositions derive from `hasActiveAgentEntailment`

The presupposition infrastructure connects back to the per-profile
prediction machinery from §2. The proto-agentivity predicate in
`AgentivePrepParams` grounds out in `hasActiveAgentEntailment` — by
construction, not by bridge theorem. -/

/-- Construct `AgentivePrepParams` from `EntailmentProfile`-based
    predictions. The proto-agentivity predicate grounds out in
    `hasActiveAgentEntailment`, connecting the formal denotation to
    the existing per-profile predictions. -/
def lexicalAgentivityParams (subjectProfile : Entity → EntailmentProfile)
    (initiator : Entity → Event → W → Bool) : AgentivePrepParams Entity Event W where
  initiator := initiator
  highProtoAgentivity := λ x _ => hasActiveAgentEntailment (subjectProfile x)

/-- The presupposition of ⟦par⟧_agentive agrees with `predictsParRequired`.
    This closes the loop: the formal denotation's presupposition IS the
    existing prediction, not a separate claim that happens to match. -/
theorem presup_agrees_with_prediction
    (subjectProfile : Entity → EntailmentProfile)
    (initiator : Entity → Event → W → Bool)
    (x : Entity) (e : Event) (w : W) :
    (parAgentiveDenot (lexicalAgentivityParams subjectProfile initiator) x e).presup w ↔
    predictsParRequired (subjectProfile x) = true := by
  simp [parAgentiveDenot, PrProp.ofBool, lexicalAgentivityParams, predictsParRequired]

/-! ### Causal denotations (14b/15b)

The causal uses of par and de differ in type — forces vs situations —
already captured by `causalForceType`/`causalSituationType` (§1).
The denotations are thin wrappers over the causal relations. -/

/-- ⟦par⟧_causal (14b): λf.λe. f FORCES e.
    Force-based causation — par marks the cause as a force
    (@cite{copley-harley-2022}). -/
def parCausalDenot (Force Event W : Type)
    (forces : Force → Event → W → Bool)
    (f : Force) (e : Event) (w : W) : Bool :=
  forces f e w

/-- ⟦de⟧_causal (15b): λs'.λe. s' CAUSE e.
    Situation-based causation — de marks the cause as a situation
    (@cite{copley-harley-2022}). -/
def deCausalDenot (Situation Event W : Type)
    (cause : Situation → Event → W → Bool)
    (s' : Situation) (e : Event) (w : W) : Bool :=
  cause s' e w

/-! ### Unified dispatch -/

/-- Full denotation dispatch for agentive uses. Wraps the par/de choice
    into a single function matching on `FrenchAgentPrep`. -/
def FrenchAgentPrep.agentiveDenot (prep : FrenchAgentPrep)
    (params : AgentivePrepParams Entity Event W)
    (x : Entity) (e : Event) : PrProp W :=
  match prep with
  | .par => parAgentiveDenot params x e
  | .de  => deAgentiveDenot params x e

end StapsRooryck2024
