import Linglib.Theories.Morphology.DM.Categorizer
import Linglib.Theories.Morphology.DM.CategorizerSemantics
import Linglib.Theories.Morphology.RootTypology
import Linglib.Theories.Syntax.Minimalism.Core.Voice

/-!
# Allosemy: Contextual Meaning Variation of Functional Heads
@cite{benz-2025} @cite{kratzer-1996}

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

namespace Morphology.DM.Allosemy

open Morphology.DM (Categorizer CatHead)
open Morphology.DM.CategorizerSemantics (NSemanticType)
open Minimalism (VoiceFlavor VoiceHead)

-- ════════════════════════════════════════════════════
-- § 1. General Allosemy Framework
-- ════════════════════════════════════════════════════

/-- A syntactic context that conditions alloseme selection.

    @cite{benz-2025} §2.4: allosemy is conditioned by the semantics of a
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
  deriving DecidableEq, BEq, Repr

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

    @cite{benz-2025} §2.6: "This dissertation is about examining the
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
-- § 2. v Allosemy (@cite{benz-2025} Ch. 3)
-- ════════════════════════════════════════════════════

/-- Allosemes of the verbal categorizer v.

    @cite{benz-2025} §2.2: v can be semantically null or contribute
    eventive semantics, depending on its syntactic context. This
    distinction drives the nominalization reading typology (Ch. 3):

    - `eventive`: v introduces an event variable. Yields CEN reading
      in nominalizations ("the frequent observation of the sky").
    - `stative`: v is semantically null / contributes stative semantics.
      Yields RN reading in nominalizations ("the observations are lost").

    In nominalization contexts, both allosemes are available for the
    same root — the ambiguity between CEN and RN readings arises from
    v's alloseme varying, not from the root changing. -/
inductive VAlloseme where
  | eventive   -- introduces an event variable (CEN contexts)
  | stative    -- null / stative semantics (RN contexts)
  deriving DecidableEq, BEq, Repr

/-- Does this v alloseme introduce an event variable? -/
def VAlloseme.introducesEvent : VAlloseme → Bool
  | .eventive => true
  | .stative  => false

/-- v allosemy as an `AllosemicHead`. -/
def vAllosemic : AllosemicHead VAlloseme where
  morpheme := .v
  entries := [
    { label := "v_eventive"
    , denotation := .eventive
    , context := { complementIsEventive := true } },
    { label := "v_stative"
    , denotation := .stative
    , context := { complementIsEventive := false } }
  ]

/-- v has exactly two allosemes. -/
theorem v_has_two_allosemes : vAllosemic.allosemeCount = 2 := rfl

/-- Root change-type conditions v alloseme selection.

    Result roots (entailing prior change) yield eventive v — the change
    entailed by the root requires an event variable in v.
    Property concept roots yield stative v — no inherent change event.

    This connects @cite{beavers-etal-2021}'s root typology to
    @cite{benz-2025}'s v allosemy: the root's lexical semantics
    determines which v alloseme is selected. -/
def VAlloseme.fromRootType : _root_.RootType → VAlloseme
  | .result          => .eventive
  | .propertyConcept => .stative

/-- Result roots yield eventive v. -/
theorem result_root_eventive :
    VAlloseme.fromRootType .result = .eventive := rfl

/-- PC roots yield stative v. -/
theorem pc_root_stative :
    VAlloseme.fromRootType .propertyConcept = .stative := rfl

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

    @cite{benz-2025} Ch. 3 adds a fourth possibility for content
    nominalizations: n can select a CP complement when v_eventive
    is present, yielding the content (CCN) reading. -/
inductive NAlloseme where
  | relational  -- introduces a relation (body-part-of); type ⟨e,⟨e,t⟩⟩
  | sortal      -- bare categorization; type ⟨e,t⟩
  | alienator   -- existentially closes possessor; type ⟨e,t⟩
  | content     -- selects CP complement (CCN reading); type ⟨e,t⟩
  deriving DecidableEq, BEq, Repr

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

/-- n has four allosemes (extending the three from CategorizerSemantics). -/
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
    , context := { belowCat := some .v, complementIsEventive := true } }
  ]

theorem n_has_four_allosemes : nAllosemic.allosemeCount = 4 := rfl

-- ════════════════════════════════════════════════════
-- § 4. Voice Allosemy (@cite{kratzer-1996}; @cite{benz-2025} §2.3)
-- ════════════════════════════════════════════════════

/-- Voice allosemy: the thematic interpretation of the external argument
    depends on the semantics of the VP it combines with.

    @cite{kratzer-1996}: "What we cannot do, however, is combine the
    holder function with the denotation of an action predicate or the
    agent function with the denotation of a stative predicate."

    @cite{benz-2025} §2.3: while Voice_{D} must introduce a DP argument,
    the thematic interpretation of that argument can be left to allosemy.
    The denotations in @cite{kratzer-1996} correspond not to separate
    syntactic heads, but to allosemes of a single Voice head. -/
inductive VoiceAlloseme where
  | agent   -- λx.λe. agent(x)(e) — combines with action VPs
  | holder  -- λx.λs. holder(x)(s) — combines with stative VPs
  deriving DecidableEq, BEq, Repr

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
-- § 5. Nominalization Reading Derivation (@cite{benz-2025} Ch. 3)
-- ════════════════════════════════════════════════════

/-- Reading types for deverbal nominalizations.

    @cite{benz-2025} Ch. 3 argues for three readings, the third (content)
    being less studied than event and result:

    - **CEN** (Complex Event Nominalization): "Die Beobachtung des
      Nachthimmels dauerte drei Stunden" — event reading
    - **RN** (Result/Referring Nominalization): "Die Beobachtungen der
      Astronomin sind verloren" — result/object reading
    - **CCN** (Complex Content Nominalization): "Seine Beobachtung, dass
      Planeten sich bewegen, veränderte die Wissenschaft" — content reading

    The CCN is syntactically and semantically distinct from both CEN and RN:
    it takes a CP complement specifying the propositional content. -/
inductive NominalizationReading where
  | complexEvent   -- CEN: event reading (takes temporal modifiers)
  | result         -- RN: result/object reading (can be pluralized)
  | content        -- CCN: content reading (takes CP complement)
  deriving DecidableEq, BEq, Repr

/-- Derive the nominalization reading from the allosemes of v and n.

    @cite{benz-2025} Ch. 3 "Chapter claim": CCNs and their characteristic
    syntax of CP-complementation are best accommodated in a structural
    polysemy account, implemented in terms of allosemy of v and n.

    The mapping:
    - v_eventive + n_sortal → CEN (event reading)
    - v_stative  + n_sortal → RN  (result reading)
    - v_eventive + n_content → CCN (content reading)
    - v_stative  + n_content → impossible (content requires eventive v) -/
def readingFromAllosemes : VAlloseme → NAlloseme → Option NominalizationReading
  | .eventive, .sortal  => some .complexEvent
  | .stative,  .sortal  => some .result
  | .eventive, .content => some .content
  | .stative,  .content => none   -- content requires eventive v
  | _,         .relational => none -- relational n yields possessive, not nominalization
  | _,         .alienator  => none -- alienator yields alienated noun

/-- CEN requires eventive v. -/
theorem cen_requires_eventive :
    readingFromAllosemes .eventive .sortal = some .complexEvent := rfl

/-- RN requires stative v. -/
theorem rn_requires_stative :
    readingFromAllosemes .stative .sortal = some .result := rfl

/-- CCN requires eventive v AND content n. -/
theorem ccn_requires_eventive_content :
    readingFromAllosemes .eventive .content = some .content := rfl

/-- Content reading is impossible with stative v: you cannot have
    propositional content without an underlying event. -/
theorem no_content_without_event :
    readingFromAllosemes .stative .content = none := rfl

/-- The three readings are pairwise distinct. -/
theorem readings_distinct :
    NominalizationReading.complexEvent ≠ .result ∧
    NominalizationReading.complexEvent ≠ .content ∧
    NominalizationReading.result ≠ .content := by decide

-- ════════════════════════════════════════════════════
-- § 6. The Allomorphy Analogy (@cite{benz-2025} §2.5)
-- ════════════════════════════════════════════════════

/-- @cite{benz-2025} Ch. 2 evaluates three positions on the relationship
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
  deriving DecidableEq, BEq, Repr

/-- Benz's position. -/
def benzPosition : AllomorphyAnalogyPosition := .partialAnalogy

end Morphology.DM.Allosemy
