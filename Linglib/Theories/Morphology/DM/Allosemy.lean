import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Morphology.DM.CategorizerSemantics
import Linglib.Theories.Morphology.RootTypology
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Allosemy: Contextual Meaning Variation of Functional Heads
@cite{benz-2025} @cite{wood-2023} @cite{kratzer-1996}

@cite{benz-2025} "Structure and Interpretation Across Categories" examines allosemy — the
meaning-side analog of allomorphy in Distributed Morphology. Where
allomorphy concerns contextually conditioned variation in *form* (PF),
allosemy concerns contextually conditioned variation in *meaning* (LF).

The key claim: several functional heads (v, n, Voice, α) systematically
receive different interpretations depending on their syntactic context,
and these meaning alternations are **not tracked by morphosyntactic
features**. The syntax does not distinguish Voice_Agent from Voice_Holder
featurally; the distinction is resolved at LF by the semantics of the
VP complement.

## Existing infrastructure as allosemy instances

linglib already formalizes several cases of allosemy without naming them:

- `CategorizerSemantics.NSemanticType`: n has three allosemes
  (relational/sortal/alienator), selected by `selectsD` and context
- `Minimalism.VoiceFlavor`: Voice has six flavors (agentive/causer/
  nonThematic/expletive/impersonal/passive), each with different semantics
- `RootType` / `Root.changeType`: roots vary in whether
  they entail change, conditioning the semantics of the v that embeds them

This module provides the general abstraction: `AllosemicEntry` and
`AllosemicHead` capture the pattern that a single morpheme has
multiple context-dependent meanings. The module then instantiates
this for v (critical for @cite{benz-2025} Ch. 3 on nominalizations)
and retroactively classifies existing n and Voice types as allosemy.

-/

namespace Theories.Morphology.DM.Allosemy

open Theories.Morphology.DM (Categorizer CatHead)
open Theories.Morphology.DM.CategorizerSemantics (NSemanticType)
open Minimalism (VoiceFlavor VoiceHead)

-- ════════════════════════════════════════════════════
-- § 1. General Allosemy Framework
-- ════════════════════════════════════════════════════

/-- A syntactic context that conditions alloseme selection.

    §2.4: allosemy is conditioned by the semantics of a
    previously interpreted domain (below) or the syntactic features of the
    next higher head (above). Both cyclic locality and linear adjacency
    play a role, but the exact locality conditions are an open question.

    We represent context minimally as what is structurally below and
    above the allosemic head. -/
structure SyntacticContext where
  /-- Category of the complement (below). `none` = no complement. -/
  belowCat : Option Categorizer := none
  /-- Category of the embedding head (above). `none` = root context. -/
  aboveCat : Option Categorizer := none
  /-- Does the complement denote an event? -/
  complementIsEventive : Bool := false
  deriving DecidableEq, Repr

/-- A single alloseme: a labeled meaning available in a particular context. -/
structure AllosemicEntry (Sem : Type) where
  /-- Human-readable label for this alloseme. -/
  label : String
  /-- The semantic contribution. -/
  denotation : Sem
  /-- The conditioning context. -/
  context : SyntacticContext
  deriving BEq, Repr

/-- An allosemic head: a functional morpheme with multiple
    context-dependent meanings.

    §2.6: "This dissertation is about examining the
    principal promise of allosemy as a tool in syntactic theory." -/
structure AllosemicHead (Sem : Type) where
  /-- Which functional head (n, v, a). -/
  morpheme : Categorizer
  /-- The available allosemes in their contexts. -/
  entries : List (AllosemicEntry Sem)
  deriving Repr

/-- Number of distinct meanings available for this head. -/
def AllosemicHead.allosemeCount {Sem : Type} (h : AllosemicHead Sem) : Nat :=
  h.entries.length

-- ════════════════════════════════════════════════════
-- § 2. v Allosemy (Ch. 3)
-- ════════════════════════════════════════════════════

/-- Allosemes of the verbal categorizer v.

    @cite{benz-2025} §2.2 / @cite{wood-2023} Ch. 5: v can be semantically
    null (identity function) or contribute eventive semantics, depending
    on its syntactic context. This distinction drives the nominalization
    reading typology:

    - `eventive`: v introduces an event variable and contributes the
      normal verbal interpretation. Yields CEN reading in nominalizations
      ("the frequent observation of the sky").
    - `zero`: v is semantically Ø (identity function). The root combines
      directly with n, yielding SEN or RN readings depending on n's
      alloseme. @cite{wood-2023} Ch. 5: "When n is semantically zero and
      v gets its ordinary verbal interpretation" (CEN); "when the v head
      is Ø" the root interacts directly with n (SEN/RN).

    In nominalization contexts, both allosemes are available for the
    same root — the ambiguity between CEN and RN/SEN readings arises
    from v's alloseme varying, not from the root changing. -/
inductive VAlloseme where
  | eventive   -- introduces an event variable (CEN contexts)
  | zero       -- semantically Ø / identity function (SEN/RN contexts)
  deriving DecidableEq, Repr

/-- Does this v alloseme introduce an event variable? -/
def VAlloseme.introducesEvent : VAlloseme → Bool
  | .eventive => true
  | .zero     => false

/-- v allosemy as an `AllosemicHead`. -/
def vAllosemic : AllosemicHead VAlloseme where
  morpheme := .v
  entries := [
    { label := "v_eventive"
    , denotation := .eventive
    , context := { complementIsEventive := true } },
    { label := "v_zero"
    , denotation := .zero
    , context := { complementIsEventive := false } }
  ]

/-- v has exactly two allosemes. -/
theorem v_has_two_allosemes : vAllosemic.allosemeCount = 2 := rfl

/-- Root change-type conditions v alloseme selection.

    Result roots (entailing prior change) yield eventive v — the change
    entailed by the root requires an event variable in v.
    Property concept roots yield stative v — no inherent change event.

    This connects @cite{beavers-etal-2021}'s root typology to
    v allosemy: the root's lexical semantics
    determines which v alloseme is selected. -/
def VAlloseme.fromRootType : _root_.RootType → VAlloseme
  | .result          => .eventive
  | .propertyConcept => .zero

/-- Result roots yield eventive v. -/
theorem result_root_eventive :
    VAlloseme.fromRootType .result = .eventive := rfl

/-- PC roots yield zero v. -/
theorem pc_root_zero :
    VAlloseme.fromRootType .propertyConcept = .zero := rfl

/-- The bridge preserves the change entailment information:
    eventive v iff the root entails change. -/
theorem fromRootType_iff_entailsChange (rt : _root_.RootType) :
    (VAlloseme.fromRootType rt).introducesEvent = rt.entailsChange := by
  cases rt <;> rfl

-- ════════════════════════════════════════════════════
-- § 3. n Allosemy (retroactive classification)
-- ════════════════════════════════════════════════════

/-- n allosemy: the three semantic types from `CategorizerSemantics`
    are allosemes of n conditioned by morphosyntactic features.

    @cite{benz-2025} Ch. 3 adds a `content` possibility for content
    nominalizations. @cite{wood-2023} Ch. 5 adds `zero` (identity
    function, yielding CEN reading) and `simpleEvent` (yielding SEN).

    The full inventory:
    - `relational`: introduces a relation (body-part-of); type ⟨e,⟨e,t⟩⟩
    - `sortal`: bare categorization; type ⟨e,t⟩
    - `alienator`: existentially closes possessor; type ⟨e,t⟩
    - `content`: selects CP complement (CCN reading, @cite{benz-2025})
    - `zero`: semantically Ø (identity), noun = verb meaning (CEN,
      @cite{wood-2023} Ch. 5 (5.4e))
    - `simpleEvent`: λP⟨e,t⟩λx∃e. P(x) & x = e — picks out entities
      equal to an event (SEN, @cite{wood-2023} Ch. 5 (5.4c))
    - `result`: λP⟨s,t⟩λx∃e. P(e) & result(x)(e) — picks out entity
      created as result of event (@cite{wood-2023} Ch. 6 (6.30))
    - `state`: λP⟨e,t⟩λx∃e. P(x) & x = e — picks out states
      (@cite{wood-2023} Ch. 1 (1.18), Ch. 6 §6.2)
    - `entity`: λP⟨e,t⟩λx. P(x) — picks out entities described by the
      root, no event connection (@cite{wood-2023} Ch. 5 (5.4d)) -/
inductive NAlloseme where
  | relational    -- introduces a relation (body-part-of); type ⟨e,⟨e,t⟩⟩
  | sortal        -- bare categorization; type ⟨e,t⟩
  | alienator     -- existentially closes possessor; type ⟨e,t⟩
  | content       -- selects CP complement (CCN reading); type ⟨e,t⟩
  | zero          -- Ø / identity function (CEN: noun = verb meaning)
  | simpleEvent   -- λP.λx∃e. P(x) & x = e (SEN reading)
  | result        -- λP.λx∃e. P(e) & result(x)(e) (result/product entity)
  | state         -- picks out states (simple state reading)
  | entity        -- λP.λx. P(x) (simple entity, no event connection)
  deriving DecidableEq, Repr

/-- Bridge: `NSemanticType` from CategorizerSemantics maps to `NAlloseme`. -/
def NAlloseme.ofNSemanticType : NSemanticType → NAlloseme
  | .relational => .relational
  | .sortal     => .sortal
  | .alienator  => .alienator

/-- The content alloseme is genuinely new — it has no pre-existing
    `NSemanticType` counterpart. -/
theorem content_is_new : ∀ (t : NSemanticType),
    NAlloseme.ofNSemanticType t ≠ .content := by
  intro t; cases t <;> simp [NAlloseme.ofNSemanticType]

/-- n has nine allosemes (extending the three from CategorizerSemantics
    with content from @cite{benz-2025} and zero/simpleEvent/result/state/
    entity from @cite{wood-2023}). -/
def nAllosemic : AllosemicHead NAlloseme where
  morpheme := .n
  entries := [
    { label := "n_relational"
    , denotation := .relational
    , context := { belowCat := none } },
    { label := "n_sortal"
    , denotation := .sortal
    , context := { belowCat := none } },
    { label := "n_alienator"
    , denotation := .alienator
    , context := { belowCat := none } },
    { label := "n_content"
    , denotation := .content
    , context := { belowCat := some .v, complementIsEventive := true } },
    { label := "n_zero"
    , denotation := .zero
    , context := { belowCat := some .v, complementIsEventive := true } },
    { label := "n_simpleEvent"
    , denotation := .simpleEvent
    , context := { belowCat := some .v } },
    { label := "n_result"
    , denotation := .result
    , context := { belowCat := some .v, complementIsEventive := true } },
    { label := "n_state"
    , denotation := .state
    , context := { belowCat := some .v } },
    { label := "n_entity"
    , denotation := .entity
    , context := { belowCat := some .v } }
  ]

theorem n_has_nine_allosemes : nAllosemic.allosemeCount = 9 := rfl

-- ════════════════════════════════════════════════════
-- § 4. Voice Allosemy (@cite{kratzer-1996}; §2.3)
-- ════════════════════════════════════════════════════

/-- Voice allosemy: the thematic interpretation of the external argument
    depends on the semantics of the VP it combines with.

    @cite{kratzer-1996}: "What we cannot do, however, is combine the
    holder function with the denotation of an action predicate or the
    agent function with the denotation of a stative predicate."

    §2.3: while Voice_{D} must introduce a DP argument,
    the thematic interpretation of that argument can be left to allosemy.
    The denotations in @cite{kratzer-1996} correspond not to separate
    syntactic heads, but to allosemes of a single Voice head. -/
inductive VoiceAlloseme where
  | agent   -- λx.λe. agent(x)(e) — combines with action VPs
  | holder  -- λx.λs. holder(x)(s) — combines with stative VPs
  deriving DecidableEq, Repr

/-- Voice alloseme selection from VP semantics. -/
def VoiceAlloseme.fromVPType (vpIsAction : Bool) : VoiceAlloseme :=
  if vpIsAction then .agent else .holder

/-- Bridge: both Voice allosemes map to `VoiceFlavor.agentive`.

    This is intentionally lossy: `VoiceFlavor` is a syntactic
    classification (Voice_D introduces a DP specifier), while
    `VoiceAlloseme` captures a purely semantic distinction (agent
    vs. holder thematic role). Both agent and holder are syntactically
    Voice_D; the thematic interpretation is resolved at LF by the
    semantics of the VP complement, not in the syntax. -/
def VoiceAlloseme.toFlavor : VoiceAlloseme → VoiceFlavor
  | .agent  => .agentive
  | .holder => .agentive

/-- Both Voice allosemes map to the same syntactic Voice flavor:
    the distinction is purely semantic, invisible to syntax. -/
theorem voice_allosemy_syntactically_invisible :
    VoiceAlloseme.agent.toFlavor = VoiceAlloseme.holder.toFlavor := rfl

-- ════════════════════════════════════════════════════
-- § 5. Nominalization Reading Derivation (Ch. 3)
-- ════════════════════════════════════════════════════

/-- Reading types for deverbal nominalizations.

    @cite{wood-2023} Ch. 1 (1.18) identifies five terminal reading types;
    @cite{benz-2025} Ch. 3 adds the CCN for German, yielding six:

    - **CEN** (Complex Event Nominal): v eventive + n zero. Noun inherits
      full verb meaning including event variable and argument structure.
    - **SEN** (Simple Event Nominal): v zero + n simpleEvent. Event reading
      without full argument structure; event comes from n's alloseme.
    - **Result/Product Nominal**: v eventive + n result. Entity whose
      existence is the result of an event (e.g. *prentun* 'printing' = the
      printed object). Built off verbal meaning, retains event variable.
    - **Simple State Nominal**: v zero + n state. State reading
      (e.g. *aðdáun* 'admiration' as a lasting state, *þrælkun* 'slavery').
    - **Simple Entity Nominal**: v zero + n entity. Entity reading with
      no event connection (e.g. *þvottur* 'laundry' = the clothes).
    - **CCN** (Complex Content Nominal): v eventive + n content. Takes
      CP complement (@cite{benz-2025}). -/
inductive NominalizationReading where
  | complexEvent   -- CEN: event reading (takes temporal modifiers, telicity PPs)
  | simpleEvent    -- SEN: event reading without full arg structure
  | result         -- RN: result/product entity (existence results from event)
  | simpleState    -- state reading (e.g. admiration, slavery)
  | simpleEntity   -- simple entity reading, no event connection (e.g. laundry)
  | content        -- CCN: content reading (takes CP complement)
  deriving DecidableEq, Repr

/-- Derive the nominalization reading from the allosemes of v and n.

    Integrates @cite{benz-2025} Ch. 3 and @cite{wood-2023} Ch. 5–6:

    - v_eventive + n_zero → CEN (n is identity, noun = verb meaning)
    - v_eventive + n_sortal → CEN (@cite{benz-2025} mapping)
    - v_eventive + n_result → result/product RN (entity from event)
    - v_zero + n_simpleEvent → SEN (v absent, n picks out event-entity)
    - v_zero + n_state → simple state (v absent, n picks out state)
    - v_zero + n_entity → simple entity RN (no event connection)
    - v_zero + n_sortal → simple entity RN (@cite{benz-2025} mapping)
    - v_eventive + n_content → CCN (content requires eventive v)
    - v_zero + n_content → impossible (content requires eventive v) -/
def readingFromAllosemes : VAlloseme → NAlloseme → Option NominalizationReading
  | .eventive, .zero        => some .complexEvent
  | .eventive, .sortal      => some .complexEvent
  | .eventive, .result      => some .result          -- result/product RN
  | .zero,     .simpleEvent => some .simpleEvent
  | .zero,     .state       => some .simpleState
  | .zero,     .entity      => some .simpleEntity
  | .zero,     .sortal      => some .simpleEntity
  | .eventive, .content     => some .content
  | .zero,     .content     => none   -- content requires eventive v
  | _,         .relational  => none   -- relational n yields possessive
  | _,         .alienator   => none   -- alienator yields alienated noun
  | .zero,     .zero        => none   -- both zero is vacuous
  | .zero,     .result      => none   -- result requires eventive v
  | .eventive, .simpleEvent => none   -- SEN requires v = Ø
  | .eventive, .state       => none   -- state requires v = Ø
  | .eventive, .entity      => none   -- entity-n requires v = Ø

/-- CEN from eventive v + zero n (@cite{wood-2023} Ch. 5). -/
theorem cen_from_zero_n :
    readingFromAllosemes .eventive .zero = some .complexEvent := rfl

/-- CEN from eventive v + sortal n (@cite{benz-2025}). -/
theorem cen_from_sortal_n :
    readingFromAllosemes .eventive .sortal = some .complexEvent := rfl

/-- Result/product RN from eventive v + result n (@cite{wood-2023} Ch. 6 (6.30)). -/
theorem result_from_eventive_v :
    readingFromAllosemes .eventive .result = some .result := rfl

/-- SEN from zero v + simpleEvent n (@cite{wood-2023} Ch. 5). -/
theorem sen_from_zero_v :
    readingFromAllosemes .zero .simpleEvent = some .simpleEvent := rfl

/-- Simple state from zero v + state n (@cite{wood-2023} Ch. 1 (1.18)). -/
theorem state_from_zero_v :
    readingFromAllosemes .zero .state = some .simpleState := rfl

/-- Simple entity from zero v + entity n (@cite{wood-2023} Ch. 5). -/
theorem simpleEntity_from_entity_n :
    readingFromAllosemes .zero .entity = some .simpleEntity := rfl

/-- Simple entity from zero v + sortal n (@cite{benz-2025}). -/
theorem simpleEntity_from_sortal_n :
    readingFromAllosemes .zero .sortal = some .simpleEntity := rfl

/-- CCN requires eventive v AND content n. -/
theorem ccn_requires_eventive_content :
    readingFromAllosemes .eventive .content = some .content := rfl

/-- Content reading is impossible with zero v. -/
theorem no_content_without_event :
    readingFromAllosemes .zero .content = none := rfl

/-- The six readings are pairwise distinct. -/
theorem readings_distinct :
    NominalizationReading.complexEvent ≠ .simpleEvent ∧
    NominalizationReading.complexEvent ≠ .result ∧
    NominalizationReading.complexEvent ≠ .simpleState ∧
    NominalizationReading.complexEvent ≠ .simpleEntity ∧
    NominalizationReading.complexEvent ≠ .content ∧
    NominalizationReading.simpleEvent ≠ .result ∧
    NominalizationReading.simpleEvent ≠ .simpleState ∧
    NominalizationReading.simpleEvent ≠ .simpleEntity ∧
    NominalizationReading.simpleEvent ≠ .content ∧
    NominalizationReading.result ≠ .simpleState ∧
    NominalizationReading.result ≠ .simpleEntity ∧
    NominalizationReading.result ≠ .content ∧
    NominalizationReading.simpleState ≠ .simpleEntity ∧
    NominalizationReading.simpleState ≠ .content ∧
    NominalizationReading.simpleEntity ≠ .content := by decide

-- ════════════════════════════════════════════════════
-- § 6. The Allomorphy Analogy (§2.5)
-- ════════════════════════════════════════════════════

/-- Ch. 2 evaluates three positions on the relationship
    between allosemy and allomorphy:

    1. The allomorphy analogy is deeply flawed and should be abandoned.
    2. Only phenomena that closely mirror allomorphy count as allosemy.
    3. The analogy holds in some respects but the relationship is
       fundamentally different.

    Benz favors position 3: allosemy shares locality properties with
    allomorphy (cyclic domains, adjacency effects) but Roots are far
    more flexible in meaning than in form. -/
inductive AllomorphyAnalogyPosition where
  | abandoned       -- position 1: analogy is flawed
  | strictParallel  -- position 2: only strict mirror cases
  | partialAnalogy  -- position 3: some respects hold, others don't
  deriving DecidableEq, Repr

/-- Benz's position. -/
def benzPosition : AllomorphyAnalogyPosition := .partialAnalogy

end Theories.Morphology.DM.Allosemy
