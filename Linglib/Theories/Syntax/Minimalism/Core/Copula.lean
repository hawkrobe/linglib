import Linglib.Theories.Syntax.Minimalism.Core.Voice
import Linglib.Theories.Morphology.DM.Allosemy
import Linglib.Theories.Morphology.DM.VocabularyInsertion
import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalism.VoiceTheta

/-!
# Copula Theory: HAVE, BE, and Delayed Gratification
@cite{myler-2016} @cite{freeze-1992} @cite{kayne-1993} @cite{wood-2015}

@cite{myler-2016} proposes that the copula verb (v) is a **semantically
vacuous light verb**: ⟦v⟧ = λx.x. The PF realization of v is determined
by Vocabulary Insertion sensitive to the syntactic environment:

- v ⇔ HAVE / ___Voice_{D},φ  (transitive Voice with a DP specifier)
- v ⇔ BE   / elsewhere

This captures HAVE = BE + transitivity: *have* is the spell-out of v in
the environment of transitive, external-argument-introducing Voice.

## Delayed Gratification

A DP can satisfy a θ-role introduced by a head X without being merged
in Spec,XP. Instead, the DP merges higher in the structure and the
θ-role percolates up via λ-abstraction until it finds its argument.
This is **delayed gratification** — distinct from both raising (which
involves a syntactic copy/trace in the lower position) and control
(which involves PRO). In delayed gratification, there is no syntactic
representation of the argument in the lower position at all.

This mechanism is the key to the "too-many-structures" puzzle: since
possession relations originate inside DP and the possessor role can
be gratified at any position in the clausal spine, the cross-linguistic
variation in possession constructions reduces to where in the structure
the possessor is first-merged.

## FreeP (@cite{myler-2016} §4.1.1.3)

The Free head introduces an experiencer θ-role in eventive *have*
constructions. Like Voice, Free varies cross-linguistically in whether
it requires a specifier:

- Free_{} (English): cannot project a specifier → experiencer role
  must be gratified higher (delayed gratification → experiencer HAVE)
- Free_{D} (Spanish): must project a specifier → free datives exist,
  but eventive experiencer HAVE is blocked (specifier consumes the role)
-/

namespace Minimalism

-- ════════════════════════════════════════════════════
-- § 1. Copula as Semantically Vacuous Light Verb
-- ════════════════════════════════════════════════════

/-- The surface realization of the copula, determined by Vocabulary Insertion. -/
inductive CopulaForm where
  | have  -- transitive environment: Voice_{D},φ above v
  | be    -- elsewhere (intransitive, unaccusative, expletive Voice)
  deriving DecidableEq, Repr

/-- Vocabulary Insertion rule for the copula.

    @cite{myler-2016} (89):
    - v ⇔ HAVE / ___Voice_{D},φ
    - v ⇔ BE   / elsewhere

    The conditioning environment is **transitive Voice**: Voice that
    introduces an external argument (has a DP specifier with φ-features).
    This is exactly the `hasD` property of `VoiceHead`. -/
def copulaVI (voice : VoiceHead) : CopulaForm :=
  if voice.hasD && voice.flavor != .nonThematic && voice.flavor != .passive
  then .have
  else .be

-- ─── VocabItem formulation ───

open Morphology.DM.VI in

/-- The copula VI rule as a proper `VocabItem` from the DM VI framework.

    Two items compete via the Elsewhere Condition:
    - HAVE: specificity 2 (checks hasD = true AND flavor ∉ {nonThematic, passive})
    - BE: specificity 0 (elsewhere — matches any context)

    `vocabularyInsertSimple copulaVIRules voice` agrees with `copulaVI voice`. -/
def copulaVIRules : List (VocabItem VoiceHead Unit) :=
  [ { exponent := "have"
    , contextMatch := λ v => v.hasD && v.flavor != .nonThematic && v.flavor != .passive
    , specificity := 2 }
  , { exponent := "be"
    , contextMatch := λ _ => true
    , specificity := 0 } ]

open Morphology.DM.VI in

/-- The `VocabItem` formulation agrees with the direct `copulaVI` function:
    "have" is inserted iff `copulaVI` returns `.have`. -/
theorem copulaVI_agrees_vocabItem (v : VoiceHead) :
    vocabularyInsertSimple copulaVIRules v =
    some (if copulaVI v = .have then "have" else "be") := by
  cases v with | mk flavor hasD phaseHead checksCase features =>
  cases flavor <;> cases hasD <;> cases phaseHead <;> cases checksCase <;>
  simp [copulaVI, copulaVIRules, vocabularyInsertSimple, vocabularyInsert,
    VocabItem.matches, List.mergeSort, List.findSome?]

/-- HAVE in the environment of agentive Voice. -/
theorem vi_agent_have : copulaVI voiceAgent = .have := rfl

/-- HAVE in the environment of causer Voice. -/
theorem vi_causer_have : copulaVI voiceCauser = .have := rfl

/-- HAVE in the environment of experiencer Voice. -/
theorem vi_experiencer_have : copulaVI voiceExperiencer = .have := rfl

/-- BE in the environment of middle/expletive Voice. -/
theorem vi_middle_be : copulaVI voiceMiddle = .be := rfl

/-- BE in the environment of non-thematic Voice (anticausative). -/
theorem vi_anticausative_be : copulaVI voiceAnticausative = .be := rfl

/-- BE in the environment of passive Voice. -/
theorem vi_passive_be : copulaVI voicePassive = .be := rfl

/-- The VI rule is equivalent to: HAVE ↔ Voice is transitive (has external argument
    that is not a PF-only marker and not a passive). -/
theorem vi_characterization (v : VoiceHead) :
    copulaVI v = .have ↔
    (v.hasD = true ∧ v.flavor ≠ .nonThematic ∧ v.flavor ≠ .passive) := by
  cases v with | mk flavor hasD phaseHead checksCase features =>
  cases flavor <;> cases hasD <;> simp [copulaVI]

-- ════════════════════════════════════════════════════
-- § 2. Gratification: When θ-Roles Meet Their Arguments
-- ════════════════════════════════════════════════════

/-- How a θ-role introduced by a head X is satisfied.

    @cite{myler-2016} §1.3 (69–73) distinguishes three mechanisms:

    - **Instant**: the DP merges in Spec,XP — the standard case.
      The DP is both the syntactic and semantic argument of X.
    - **Delayed**: the DP merges higher in the structure (e.g., Spec,YP
      where Y ≠ X). The θ-role of X percolates up via λ-abstraction
      and is eventually saturated. There is NO syntactic representation
      of the argument in the lower Spec,XP position.
    - **Raising**: the DP is base-generated in Spec,XP (or a copy/trace
      is left there) and moves to a higher position. Unlike delayed
      gratification, there IS a syntactic reflex in the lower position.

    Delayed gratification is the key to Myler's account: possession
    relations originate DP-internally (in Spec,nP for inalienable, in
    Spec,PossP for alienable), but the possessor can be gratified at
    any point in the clausal spine — Spec,PredP, Spec,ApplP, Spec,VoiceP.
    The variation in WHERE gratification occurs generates the cross-linguistic
    typology of possession constructions. -/
inductive GratificationType where
  | instant   -- DP in Spec,XP: syntactic + semantic argument of X
  | delayed   -- DP higher: only semantic argument of X, no syntactic reflex in Spec,XP
  | raising   -- DP moves from Spec,XP: syntactic copy/trace below
  deriving DecidableEq, Repr

/-- Does this gratification type leave a syntactic reflex in the
    lower (base) position? This is the key difference between
    delayed gratification and raising/control. -/
def GratificationType.hasSyntacticReflexBelow : GratificationType → Bool
  | .instant => true   -- DP is in the base position
  | .delayed => false  -- no syntactic presence below
  | .raising => true   -- copy/trace in base position

/-- Does the argument end up higher than the θ-assigning head? -/
def GratificationType.argumentMovesUp : GratificationType → Bool
  | .instant => false
  | .delayed => true
  | .raising => true

/-- Delayed gratification is unique: the argument moves up but leaves
    no syntactic reflex. This has consequences for agreement, scope, and
    intervention — none of the effects triggered by a DP in the lower
    position arise. -/
theorem delayed_unique :
    GratificationType.delayed.argumentMovesUp = true ∧
    GratificationType.delayed.hasSyntacticReflexBelow = false := ⟨rfl, rfl⟩

/-- Raising has BOTH syntactic reflex and upward movement.
    This is what distinguishes it from delayed gratification. -/
theorem raising_has_both :
    GratificationType.raising.argumentMovesUp = true ∧
    GratificationType.raising.hasSyntacticReflexBelow = true := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. FreeP: Experiencer-Introducing Head
-- ════════════════════════════════════════════════════

/-- The Free head introduces an experiencer θ-role above an embedded VoiceP.

    @cite{myler-2016} §4.1.1.3: Free is a functional head that merges
    above the embedded VoiceP inside *have*'s complement. It is related
    to but distinct from Appl:
    - Like high Appl, Free relates an individual to an event
    - Unlike Appl, Free introduces specifically an **experiencer** role
    - Free's specifier behavior varies cross-linguistically (±D)

    The ±D parameter on Free generates the English/Spanish asymmetry:
    - Free_{} (English): no specifier → delayed gratification →
      experiencer HAVE exists, free datives do not
    - Free_{D} (Spanish): specifier required → instant gratification →
      free datives exist, eventive experiencer HAVE does not

    @cite{myler-2016} table (35):
    | Free heads  | Phenomena                           | Languages    |
    |-------------|-------------------------------------|--------------|
    | Free_{}     | Eventive Exp HAVE, No free datives  | English      |
    | Free_{D}    | No Eventive Exp HAVE, Free datives  | Spanish      |
    | Both        | Both                                | None known   |
    | None        | Neither                             | None known   | -/
structure FreeHead where
  /-- Does Free require a specifier (DP)? -/
  hasD : Bool
  deriving DecidableEq, Repr

/-- English-type Free: cannot take a specifier.
    The experiencer role introduced by Free must be gratified higher,
    via delayed gratification to Spec,VoiceP → yields experiencer HAVE. -/
def freeNoSpec : FreeHead := { hasD := false }

/-- Spanish-type Free: must take a specifier.
    The experiencer role is gratified instantly in Spec,FreeP →
    yields free datives. But delayed gratification to Spec,VoiceP
    is blocked (the role is already consumed) → no eventive
    experiencer HAVE. -/
def freeWithSpec : FreeHead := { hasD := true }

/-- Does this Free head allow delayed gratification of its
    experiencer role to a higher position?

    If Free has a specifier ({D}), the role is gratified instantly
    and cannot percolate further. If Free lacks a specifier ({}),
    the role remains unsaturated and percolates up. -/
def FreeHead.allowsDelayedGratification (f : FreeHead) : Bool :=
  !f.hasD

/-- Does this Free head yield free datives?
    Free datives arise when the experiencer merges in Spec,FreeP. -/
def FreeHead.yieldsFreeOrDative (f : FreeHead) : Bool :=
  f.hasD

/-- Does this Free head yield eventive experiencer HAVE?
    Eventive experiencer HAVE arises when the experiencer role
    percolates to Spec,VoiceP via delayed gratification.

    Derived from `allowsDelayedGratification`: experiencer HAVE
    exists iff Free's θ-role can percolate (not consumed locally). -/
def FreeHead.yieldsEventiveExpHave (f : FreeHead) : Bool :=
  f.allowsDelayedGratification

/-- English: eventive experiencer HAVE, no free datives. -/
theorem english_free_pattern :
    freeNoSpec.yieldsEventiveExpHave = true ∧
    freeNoSpec.yieldsFreeOrDative = false := ⟨rfl, rfl⟩

/-- Spanish: free datives, no eventive experiencer HAVE. -/
theorem spanish_free_pattern :
    freeWithSpec.yieldsEventiveExpHave = false ∧
    freeWithSpec.yieldsFreeOrDative = true := ⟨rfl, rfl⟩

/-- The complementarity: for any Free head, exactly one of
    eventive experiencer HAVE and free datives is available. -/
theorem free_complementarity (f : FreeHead) :
    f.yieldsEventiveExpHave = !f.yieldsFreeOrDative := by
  cases f with | mk d => cases d <;> rfl

-- ════════════════════════════════════════════════════
-- § 4. Complement Types of HAVE
-- ════════════════════════════════════════════════════

/-- The complement of *have* (= the complement of v_BE).

    @cite{myler-2016} table (100): the interpretation of a HAVE
    sentence depends on the interaction between the complement type
    and the Voice alloseme selected. The complement types are:

    - **possessedDP**: a DP containing a possession relation
      (relational noun or Poss head). Voice is expletive → relational HAVE.
    - **eventDP**: a DP denoting an event (light-verb HAVE: "had a bath").
      Voice assigns agent/holder.
    - **saturatedEventiveVoiceP**: a full VoiceP with an agent and event
      (engineer HAVE: "had John bathe the dog"). Voice selects engineer alloseme.
    - **stativeSC**: a stative small clause — PredP, AP, PP
      (causer HAVE: "had me angry"; locative HAVE: "has nests in it").
      Voice selects holder/causer.
    - **freeP**: a FreeP embedding a VoiceP (experiencer HAVE:
      "had Johnny run off on us"). Voice is expletive; Free introduces
      the experiencer role.
    - **modalBase**: a DP/set of worlds (modal HAVE: "has to leave").
      Semantics is world-containment, not individual-event. -/
inductive HaveComplement where
  | possessedDP               -- DP with possession relation (relational HAVE)
  | eventDP                   -- DP denoting event (light-verb HAVE)
  | saturatedEventiveVoiceP   -- Full VoiceP (engineer HAVE)
  | stativeSC                 -- Stative small clause (causer/locative HAVE)
  | freeP                     -- FreeP + embedded VoiceP (experiencer HAVE)
  | modalBase                 -- Set of worlds (modal HAVE)
  deriving DecidableEq, Repr

/-- Is the complement eventive? This conditions Voice alloseme selection. -/
def HaveComplement.isEventive : HaveComplement → Bool
  | .saturatedEventiveVoiceP => true
  | .eventDP                 => true
  | .freeP                   => true   -- embedded VoiceP is eventive
  | .possessedDP             => false
  | .stativeSC               => false
  | .modalBase               => false

/-- Is the complement a stative predication (small clause)?
    This is the condition for the holder/causer Voice alloseme:
    Voice assigns a holder role when it combines with a stative
    predicate (AP, PP, PredP).

    Crucially, possessedDP and modalBase are NOT stative predicates
    from Voice's perspective — the possession relation originates
    DP-internally and Voice is vacuous (expletive). -/
def HaveComplement.isStativePredicate : HaveComplement → Bool
  | .stativeSC => true
  | _          => false

/-- Is the complement a saturated eventive VoiceP?
    This is the most specific environment: a full clause with its own
    agent and event, triggering the engineer alloseme. -/
def HaveComplement.isSaturatedEventiveVoiceP : HaveComplement → Bool
  | .saturatedEventiveVoiceP => true
  | _                        => false

/-- Is the complement an eventive DP (not a full VoiceP)?
    Event-denoting DPs (light-verb HAVE: "had a bath") trigger agentive
    Voice, unlike FreeP (which triggers expletive Voice). -/
def HaveComplement.isEventDP : HaveComplement → Bool
  | .eventDP => true
  | _        => false

-- ════════════════════════════════════════════════════
-- § 5. The HAVE Interpretation Table
-- ════════════════════════════════════════════════════

/-- The reading (interpretation) of a HAVE sentence. -/
inductive HaveReading where
  | relational           -- "I have a sister" (kinship/body-part/ownership)
  | lightVerb            -- "We had a conversation" (event denoting DP)
  | engineer             -- "I had John bathe the dog" (ECM, sentient orchestrator)
  | causer               -- "The article had me angry" (causer of state)
  | experiencerEventive  -- "We had Johnny run off on us" (adversely affected, eventive)
  | experiencerStative   -- "Juan has bees stinging him" (adversely affected, stative)
  | locative             -- "This tree has nests in it" (locative SC + pronoun)
  | temporaryPossession  -- "I have your money" (hidden SC, causer)
  | modal                -- "John has to leave" (modal base containment)
  deriving DecidableEq, Repr

/-- @cite{myler-2016} table (100): Which Voice alloseme is selected
    given a particular complement type.

    **Derived** from complement properties via
    `VoiceAlloseme.fromComplement` (Allosemy.lean), with one extension:
    event-denoting DPs (light-verb HAVE) trigger the agent alloseme,
    which `fromComplement` does not cover (it only distinguishes
    saturated VoiceP from stative from elsewhere).

    The cascade:
    1. Saturated eventive VoiceP → engineer (most specific)
    2. Event-denoting DP → agent (eventive but not a VoiceP)
    3. Stative SC → holder (stative predicate)
    4. Elsewhere (possessedDP, FreeP, modalBase) → expletive (Voice is vacuous) -/
def voiceAllosemeForComplement (c : HaveComplement) :
    Morphology.DM.Allosemy.VoiceAlloseme :=
  if c.isSaturatedEventiveVoiceP then .engineer
  else if c.isEventDP then .agent
  else if c.isStativePredicate then .holder
  else .expletive

/-- The non-eventDP cases agree with `VoiceAlloseme.fromComplement`:
    when the complement is not an event-denoting DP, the alloseme can
    be derived purely from the `isSaturatedEventiveVoiceP` and `isStative`
    properties — which is exactly what `fromComplement` does. -/
theorem voiceAlloseme_agrees_fromComplement (c : HaveComplement)
    (hNotEventDP : c.isEventDP = false) :
    voiceAllosemeForComplement c =
    Morphology.DM.Allosemy.VoiceAlloseme.fromComplement
      c.isSaturatedEventiveVoiceP c.isStativePredicate := by
  cases c <;> simp_all [voiceAllosemeForComplement,
    HaveComplement.isSaturatedEventiveVoiceP, HaveComplement.isEventDP,
    HaveComplement.isStativePredicate,
    Morphology.DM.Allosemy.VoiceAlloseme.fromComplement]

/-- The predicted reading for each complement type. -/
def haveReading : HaveComplement → HaveReading
  | .possessedDP             => .relational
  | .eventDP                 => .lightVerb
  | .saturatedEventiveVoiceP => .engineer
  | .stativeSC               => .causer              -- or locative, depending on SC content
  | .freeP                   => .experiencerEventive
  | .modalBase               => .modal

-- ════════════════════════════════════════════════════
-- § 6. Verification: Per-Cell Theorems for Table (100)
-- ════════════════════════════════════════════════════

/-- Relational HAVE: Voice is expletive; meaning = complement's meaning. -/
theorem relational_have_expletive :
    voiceAllosemeForComplement .possessedDP = .expletive := rfl

/-- Light-verb HAVE: Voice is agentive; meaning = complement + agent. -/
theorem lightVerb_have_agentive :
    voiceAllosemeForComplement .eventDP = .agent := rfl

/-- Engineer HAVE: saturated eventive VoiceP triggers engineer alloseme. -/
theorem engineer_have_from_voiceP :
    voiceAllosemeForComplement .saturatedEventiveVoiceP = .engineer := rfl

/-- Causer HAVE: stative SC triggers holder alloseme. -/
theorem causer_have_from_stativeSC :
    voiceAllosemeForComplement .stativeSC = .holder := rfl

/-- Experiencer HAVE: FreeP triggers expletive Voice (Free does the θ-work). -/
theorem experiencer_have_from_freeP :
    voiceAllosemeForComplement .freeP = .expletive := rfl

/-- Modal HAVE: modal base triggers expletive Voice. -/
theorem modal_have_expletive :
    voiceAllosemeForComplement .modalBase = .expletive := rfl

-- § 6a. Starred cells: ruled-out combinations

open Morphology.DM.Allosemy in

/-- Agent + stative SC = * : agentive Voice requires a dynamic event,
    but a stative SC does not provide one. -/
theorem agent_blocked_by_stativeSC :
    voiceAllosemeForComplement .stativeSC ≠ .agent := by decide

/-- Engineer is ONLY available with saturated eventive VoiceP.
    All other complement types yield a different alloseme. -/
theorem engineer_only_from_voiceP (c : HaveComplement) :
    voiceAllosemeForComplement c = .engineer → c = .saturatedEventiveVoiceP := by
  cases c <;> simp [voiceAllosemeForComplement, HaveComplement.isSaturatedEventiveVoiceP,
    HaveComplement.isEventDP, HaveComplement.isStativePredicate]

/-- When Voice is expletive (relational, experiencer, modal HAVE),
    the meaning comes entirely from the complement — Voice contributes
    nothing. This is the "meaning = complement's meaning" generalization. -/
theorem expletive_voice_complement_determines_meaning (c : HaveComplement) :
    voiceAllosemeForComplement c = .expletive →
    c = .possessedDP ∨ c = .freeP ∨ c = .modalBase := by
  cases c <;> simp [voiceAllosemeForComplement, HaveComplement.isSaturatedEventiveVoiceP,
    HaveComplement.isEventDP, HaveComplement.isStativePredicate]

-- ════════════════════════════════════════════════════
-- § 6b. Voice Alloseme → Theta Role (via VoiceTheta)
-- ════════════════════════════════════════════════════

open Morphology.DM.Allosemy (VoiceAlloseme) in
open Interfaces.SyntaxSemantics.VoiceTheta in

/-- The complete theta-role prediction chain for HAVE sentences:

        HaveComplement → VoiceAlloseme → VoiceFlavor → Option ThetaRole

    This composes three independently motivated mappings:
    1. Complement type determines Voice alloseme (§5, table (100))
    2. Alloseme maps to syntactic VoiceFlavor (Allosemy.lean)
    3. VoiceFlavor determines theta role (VoiceTheta.lean)

    The result: each HAVE reading predicts a specific external θ-role
    (or none, for expletive Voice). -/
def haveThetaPrediction (c : HaveComplement) : Option ThetaRole :=
  (voiceAllosemeForComplement c).toFlavor.thetaRole

/-- Light-verb HAVE assigns agent. -/
theorem lightVerb_assigns_agent :
    haveThetaPrediction .eventDP = some .agent := by decide

/-- Engineer HAVE assigns agent (to the "engineer" orchestrator). -/
theorem engineer_assigns_agent :
    haveThetaPrediction .saturatedEventiveVoiceP = some .agent := by decide

/-- Causer HAVE assigns experiencer (holder alloseme → experiencer flavor). -/
theorem causer_assigns_experiencer :
    haveThetaPrediction .stativeSC = some .experiencer := by decide

/-- Relational HAVE assigns no theta role (expletive Voice). -/
theorem relational_no_theta :
    haveThetaPrediction .possessedDP = none := by decide

/-- Experiencer HAVE (FreeP) assigns no theta role from Voice
    (the experiencer role comes from Free, not Voice). -/
theorem experiencer_theta_from_free_not_voice :
    haveThetaPrediction .freeP = none := by decide

/-- Modal HAVE assigns no theta role. -/
theorem modal_no_theta :
    haveThetaPrediction .modalBase = none := by decide

-- ════════════════════════════════════════════════════
-- § 7. Complex Event Nominals and Delayed Gratification
-- ════════════════════════════════════════════════════

/-- Whether a nominal (DP complement of HAVE) can undergo delayed
    gratification — i.e., can its possessor role percolate up to
    be gratified at Spec,VoiceP?

    @cite{myler-2016} §4.1.2.1 observes that complex event nominals
    (CENs) resist delayed gratification and thus cannot appear in
    relational *have* constructions:

    - * John had a/the destruction of the city.
    - * The city had a/the destruction.

    The reason: CENs contain a v head (verbal substructure), and v
    forces instant gratification — the possessor must be realized
    DP-internally. In contrast, simplex event nominals (SENs) and
    relational nouns lack v, so their possessor role can percolate.

    **Derived from v allosemy** (Allosemy.lean): `VAlloseme.introducesEvent`
    is the independently motivated property that determines whether v
    contributes an event variable. When v is eventive, the DP has verbal
    substructure that blocks delayed gratification. When v is zero
    (identity), delayed gratification is available. -/
def nominalAllowsDelayedGratification
    (v : Morphology.DM.Allosemy.VAlloseme) : Bool :=
  !v.introducesEvent

open Morphology.DM.Allosemy in

/-- Relational nouns (v = zero, no event variable) allow delayed gratification. -/
theorem relational_allows_delayed :
    nominalAllowsDelayedGratification .zero = true := rfl

open Morphology.DM.Allosemy in

/-- CENs (v = eventive, introduces event variable) block delayed gratification. -/
theorem cen_blocks_delayed :
    nominalAllowsDelayedGratification .eventive = false := rfl

open Morphology.DM.Allosemy in

/-- The bridge: delayed gratification is blocked iff v introduces an event.
    This derives the CEN restriction from the allosemy framework rather
    than stipulating it as a separate parameter. -/
theorem delayed_gratification_iff_no_event
    (v : Morphology.DM.Allosemy.VAlloseme) :
    nominalAllowsDelayedGratification v = !v.introducesEvent := rfl

end Minimalism
