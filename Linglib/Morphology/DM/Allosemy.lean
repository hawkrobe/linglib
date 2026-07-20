import Linglib.Morphology.DM.Categorizer
import Linglib.Morphology.DM.CategorizerSemantics
import Linglib.Morphology.Exponence.Select
import Linglib.Morphology.Realization
import Linglib.Semantics.Verb.Root.Classification
import Linglib.Syntax.Minimalist.Verbal.Voice

/-!
# Allosemy: Contextual Meaning Variation of Functional Heads

[benz-2025] "Structure and Interpretation Across Categories" examines allosemy — the
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
- `Minimalist.Voice.Flavor`: Voice has six flavors (agentive/causer/
  nonThematic/expletive/impersonal/passive), each with different semantics
- `Verb.Root.ChangeType` / `Verb.Root.Classification.changeType`: roots vary in
  whether they entail change, conditioning the semantics of the v that embeds them

This module provides the general abstraction: `AllosemicEntry` and
`AllosemicHead` capture the pattern that a single morpheme has
multiple context-dependent meanings. The module then instantiates
this for v (critical for [benz-2025] Ch. 3 on nominalizations)
and retroactively classifies existing n and Voice types as allosemy.

## The List-2 / List-3 symmetry, by construction

`AllosemicEntry` is a `Morphology.Exponence.Rule` instance
(`SyntacticContext.matches` as applicability, denotation as exponent),
just as `DM.VI.VocabItem` is. So DM's List 2 (form) and List 3 (meaning)
are resolved by **one** selection engine: `Exponence.selectBy` on the
non-wildcard-field score, whose winner is the Elsewhere winner
(`selectBy_score_isElsewhereWinner`). `VoiceAlloseme.fromComplement` is a
worked List-3 competition over that engine. `readingFromAllosemes` is a
different object — the List-3 *composition* of two already-selected
allosemes (v ⊕ n), not a single-head competition — so it stays a table.

-/

namespace Morphology.DM.Allosemy

open Morphology.DM (Categorizer CatHead)
open Morphology.DM.CategorizerSemantics (NSemanticType)
open Minimalist.Voice (Flavor Head)

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
  /-- Does the complement denote a state? ([kratzer-1996] §2.3: the
      stative-vs-dynamic split conditions the Voice alloseme.) -/
  complementIsStative : Bool := false
  deriving DecidableEq, Repr

/-- A partial context specification `spec` **matches** a fully-specified
query context `c` when every non-wildcard field of `spec` agrees with
`c`. A field at its default (`none` / `false`) is a **wildcard**,
constraining nothing; a set field must agree. More specified contexts
match strictly fewer queries — the applicability-set inclusion that
orders exponence rules ([kiparsky-1973]). -/
def SyntacticContext.matches (spec c : SyntacticContext) : Bool :=
  (spec.belowCat == none || spec.belowCat == c.belowCat) &&
  (spec.aboveCat == none || spec.aboveCat == c.aboveCat) &&
  (!spec.complementIsEventive || c.complementIsEventive) &&
  (!spec.complementIsStative || c.complementIsStative)

/-- The specificity **score**: the number of non-wildcard fields. Higher
score = more specified = strictly smaller applicability set, so the score
reflects the specificity preorder contravariantly
(`SyntacticContext.specificity_le_of_matches_subset`). -/
def SyntacticContext.specificity (c : SyntacticContext) : Nat :=
  (if c.belowCat.isSome then 1 else 0) + (if c.aboveCat.isSome then 1 else 0)
    + (if c.complementIsEventive then 1 else 0) + (if c.complementIsStative then 1 else 0)

@[simp] theorem SyntacticContext.matches_self (c : SyntacticContext) : c.matches c = true := by
  simp [SyntacticContext.matches]

/-- A broader specification (matched by every query the narrower one is)
has no more non-wildcard fields: the score reflects applicability-set
inclusion contravariantly. -/
theorem SyntacticContext.specificity_le_of_matches_subset {r s : SyntacticContext}
    (h : ∀ q, s.matches q = true → r.matches q = true) :
    r.specificity ≤ s.specificity := by
  have hrs : r.matches s = true := h s (SyntacticContext.matches_self s)
  simp only [SyntacticContext.matches, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrs
  obtain ⟨⟨⟨hb, ha⟩, he⟩, hst⟩ := hrs
  simp only [SyntacticContext.specificity]
  have b : (if r.belowCat.isSome then 1 else 0) ≤ (if s.belowCat.isSome then (1 : ℕ) else 0) := by
    rcases hb with hb | hb <;> simp [hb]
  have a : (if r.aboveCat.isSome then 1 else 0) ≤ (if s.aboveCat.isSome then (1 : ℕ) else 0) := by
    rcases ha with ha | ha <;> simp [ha]
  have e : (if r.complementIsEventive then 1 else 0) ≤
      (if s.complementIsEventive then (1 : ℕ) else 0) := by
    cases hr : r.complementIsEventive <;> cases hsc : s.complementIsEventive <;> simp_all
  have t : (if r.complementIsStative then 1 else 0) ≤
      (if s.complementIsStative then (1 : ℕ) else 0) := by
    cases hr : r.complementIsStative <;> cases hsc : s.complementIsStative <;> simp_all
  omega

/-- Equal-score inclusion is equality: if every query matching `s` also
matches `r` and the two carry the same number of non-wildcard fields, the
specifications coincide. -/
theorem SyntacticContext.eq_of_matches_subset_of_specificity_eq {r s : SyntacticContext}
    (h : ∀ q, s.matches q = true → r.matches q = true)
    (hs : r.specificity = s.specificity) : r = s := by
  have hrs : r.matches s = true := h s (SyntacticContext.matches_self s)
  simp only [SyntacticContext.matches, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hrs
  obtain ⟨⟨⟨hb, ha⟩, he⟩, hst⟩ := hrs
  simp only [SyntacticContext.specificity] at hs
  have b : (if r.belowCat.isSome then 1 else 0) ≤ (if s.belowCat.isSome then (1 : ℕ) else 0) := by
    rcases hb with h | h <;> simp [h]
  have a : (if r.aboveCat.isSome then 1 else 0) ≤ (if s.aboveCat.isSome then (1 : ℕ) else 0) := by
    rcases ha with h | h <;> simp [h]
  have e : (if r.complementIsEventive then 1 else 0) ≤
      (if s.complementIsEventive then (1 : ℕ) else 0) := by
    cases hr : r.complementIsEventive <;> cases hsc : s.complementIsEventive <;> simp_all
  have t : (if r.complementIsStative then 1 else 0) ≤
      (if s.complementIsStative then (1 : ℕ) else 0) := by
    cases hr : r.complementIsStative <;> cases hsc : s.complementIsStative <;> simp_all
  obtain ⟨rb, ra, rc, rd⟩ := r
  obtain ⟨sb, sa, sc, sd⟩ := s
  have eqb : rb = sb := by cases rb <;> cases sb <;> simp_all; all_goals omega
  have eqa : ra = sa := by cases ra <;> cases sa <;> simp_all; all_goals omega
  have eqc : rc = sc := by cases rc <;> cases sc <;> simp_all; all_goals omega
  have eqd : rd = sd := by cases rd <;> cases sd <;> simp_all
  subst eqb eqa eqc eqd; rfl

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

/-! ### Allosemy on the exponence core

An `AllosemicEntry` is a rule of exponence (`Morphology/Exponence/`): its
denotation is the exponent, its context's `matches` predicate the
applicability set. So the very engine that resolves DM's List 2
(`DM/VocabularyInsertion.lean`) resolves List 3 — LF competition among
allosemes — with no new machinery. `AllosemicEntry.score` is the
non-wildcard-field count of the entry's context; `score_strictAnti` shows
it is strictly antitone in specificity, so `selectBy score` is Elsewhere
selection (`selectBy_score_isElsewhereWinner`). -/

section Exponence

open Morphology.Exponence

variable {Sem : Type}

/-- An `AllosemicEntry` exposes the shared exponence interface: contexts
are `SyntacticContext`s, applicability is `matches`, the exponent is the
denotation. -/
instance : Exponence.Rule (AllosemicEntry Sem) SyntacticContext Sem :=
  ⟨AllosemicEntry.denotation, fun e c => e.context.matches c = true⟩

instance : Preorder (AllosemicEntry Sem) := Exponence.toPreorder

instance : DecidableRel (Applies : AllosemicEntry Sem → SyntacticContext → Prop) :=
  fun e c => inferInstanceAs (Decidable (e.context.matches c = true))

/-- The specificity score of an alloseme: the non-wildcard-field count of
its conditioning context. -/
def AllosemicEntry.score (e : AllosemicEntry Sem) : Nat := e.context.specificity

/-- The score is strictly antitone in specificity: a strictly broader
alloseme scores strictly lower. -/
theorem score_strictAnti : StrictAnti (AllosemicEntry.score (Sem := Sem)) := by
  intro s r hlt
  have hsub : ∀ q, s.context.matches q = true → r.context.matches q = true := hlt.le
  refine lt_of_le_of_ne (SyntacticContext.specificity_le_of_matches_subset hsub)
    fun heq => not_le_of_gt hlt ?_
  have hctx : r.context = s.context :=
    SyntacticContext.eq_of_matches_subset_of_specificity_eq hsub heq
  show ∀ q, r.context.matches q = true → s.context.matches q = true
  rw [hctx]; exact fun _ h => h

/-- Score selection over an alloseme vocabulary is Elsewhere selection:
the winner is `≤`-minimal among the applicable allosemes. -/
theorem selectBy_score_isElsewhereWinner {v : List (AllosemicEntry Sem)}
    {c : SyntacticContext} {r : AllosemicEntry Sem}
    (h : selectBy AllosemicEntry.score v c = some r) : IsElsewhereWinner v c r :=
  selectBy_isElsewhereWinner (score_strictAnti.strictAntiOn _) h

end Exponence

-- ════════════════════════════════════════════════════
-- § 2. v Allosemy (Ch. 3)
-- ════════════════════════════════════════════════════

/-- Allosemes of the verbal categorizer v.

    [benz-2025] §2.2 / [wood-2023] Ch. 5: v can be semantically
    null (identity function) or contribute eventive semantics, depending
    on its syntactic context. This distinction drives the nominalization
    reading typology:

    - `eventive`: v introduces an event variable and contributes the
      normal verbal interpretation. Yields CEN reading in nominalizations
      ("the frequent observation of the sky").
    - `zero`: v is semantically Ø (identity function). The root combines
      directly with n, yielding SEN or RN readings depending on n's
      alloseme. [wood-2023] Ch. 5: "When n is semantically zero and
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

    This connects [beavers-etal-2021]'s root typology to
    v allosemy: the root's lexical semantics
    determines which v alloseme is selected. -/
def VAlloseme.fromRootType : Verb.Root.ChangeType → VAlloseme
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
theorem fromRootType_iff_entailsChange (rt : Verb.Root.ChangeType) :
    (VAlloseme.fromRootType rt).introducesEvent = rt.entailsChange := by
  cases rt <;> rfl

-- ════════════════════════════════════════════════════
-- § 3. n Allosemy (retroactive classification)
-- ════════════════════════════════════════════════════

/-- n allosemy: the three semantic types from `CategorizerSemantics`
    are allosemes of n conditioned by morphosyntactic features.

    [benz-2025] Ch. 3 adds a `content` possibility for content
    nominalizations. [wood-2023] Ch. 5 adds `zero` (identity
    function, yielding CEN reading) and `simpleEvent` (yielding SEN).

    The full inventory:
    - `relational`: introduces a relation (body-part-of); type ⟨e,⟨e,t⟩⟩
    - `sortal`: bare categorization; type ⟨e,t⟩
    - `alienator`: existentially closes possessor; type ⟨e,t⟩
    - `content`: selects CP complement (CCN reading, [benz-2025])
    - `zero`: semantically Ø (identity), noun = verb meaning (CEN,
      [wood-2023] Ch. 5 (5.4e))
    - `simpleEvent`: λP⟨e,t⟩λx∃e. P(x) & x = e — picks out entities
      equal to an event (SEN, [wood-2023] Ch. 5 (5.4c))
    - `result`: λP⟨s,t⟩λx∃e. P(e) & result(x)(e) — picks out entity
      created as result of event ([wood-2023] Ch. 6 (6.30))
    - `state`: λP⟨e,t⟩λx∃e. P(x) & x = e — picks out states
      ([wood-2023] Ch. 1 (1.18), Ch. 6 §6.2)
    - `entity`: λP⟨e,t⟩λx. P(x) — picks out entities described by the
      root, no event connection ([wood-2023] Ch. 5 (5.4d)) -/
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
    with content from [benz-2025] and zero/simpleEvent/result/state/
    entity from [wood-2023]). -/
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
-- § 4. Voice Allosemy ([kratzer-1996]; §2.3)
-- ════════════════════════════════════════════════════

/-- Voice allosemy: the thematic interpretation of the external argument
    depends on the semantics of the VP it combines with.

    [kratzer-1996]: "What we cannot do, however, is combine the
    holder function with the denotation of an action predicate or the
    agent function with the denotation of a stative predicate."

    §2.3: while Voice_{D} must introduce a DP argument,
    the thematic interpretation of that argument can be left to allosemy.
    The denotations in [kratzer-1996] correspond not to separate
    syntactic heads, but to allosemes of a single Voice head.

    [myler-2016] Ch. 4 extends this to four allosemes, adding
    the engineer role (for ECM *have*) and the expletive/identity
    alloseme (for relational and light-verb *have* where Voice assigns
    no θ-role). The conditioning environments (98a–d):

    - `agent`:    ⟦Voice⟧ = λx.λe. Agent(x,e)     / ___(agentive, dynamic event)
    - `holder`:   ⟦Voice⟧ = λx.λe. Holder(x,e)    / ___(stative eventuality)
    - `engineer`: ⟦Voice⟧ = λx.λe. Engineer(x,e)  / ___v_BE Eventive-VoiceP⟨s,t⟩
    - `expletive`:⟦Voice⟧ = λx.x                  / ___(elsewhere) -/
inductive VoiceAlloseme where
  | agent     -- λx.λe. Agent(x,e) — combines with action VPs
  | holder    -- λx.λe. Holder(x,e) — combines with stative VPs (includes causer, experiencer)
  | engineer  -- λx.λe. Engineer(x,e) — ECM *have*: complement is saturated eventive VoiceP
  | expletive -- λx.x — type-neutral identity; no θ-role (relational *have*, light-verb *have*)
  deriving DecidableEq, Repr

/-- Does this Voice alloseme assign a thematic role to the external argument? -/
def VoiceAlloseme.assignsTheta : VoiceAlloseme → Bool
  | .agent    => true
  | .holder   => true
  | .engineer => true
  | .expletive => false

/-- The Voice allosemes as a competing exponence vocabulary
    ([myler-2016] (98a–d)): engineer for a saturated eventive VoiceP
    complement (most specified), holder for a stative one, expletive
    elsewhere (the all-wildcard, `⊥`-specificity default). -/
def voiceVocabulary : List (AllosemicEntry VoiceAlloseme) :=
  [ { label := "Voice_engineer", denotation := .engineer
    , context := { belowCat := some .v, complementIsEventive := true } },
    { label := "Voice_holder", denotation := .holder
    , context := { complementIsStative := true } },
    { label := "Voice_expletive", denotation := .expletive
    , context := {} } ]

/-- Voice alloseme selection from complement properties.

    [myler-2016] table (100): the alloseme is determined by the nature of
    *have*'s complement and whether the VP is eventive. This is Elsewhere
    competition over `voiceVocabulary`, resolved by the shared exponence
    engine (`Exponence.selectBy` on the non-wildcard-field score): engineer
    is most specific (saturated eventive VoiceP), expletive is the elsewhere
    default. -/
def VoiceAlloseme.fromComplement
    (complementIsEventiveVoiceP : Prop) [Decidable complementIsEventiveVoiceP]
    (complementIsStative : Prop) [Decidable complementIsStative] : VoiceAlloseme :=
  let q : SyntacticContext :=
    { belowCat := if complementIsEventiveVoiceP then some .v else none
      complementIsEventive := decide complementIsEventiveVoiceP
      complementIsStative := decide complementIsStative }
  ((Exponence.selectBy AllosemicEntry.score voiceVocabulary q).map
    AllosemicEntry.denotation).getD .expletive

/-- Eventive-VoiceP complement selects engineer ([myler-2016]). -/
example : VoiceAlloseme.fromComplement True False = .engineer := by decide

/-- Stative complement (non-eventive) selects holder ([kratzer-1996]). -/
example : VoiceAlloseme.fromComplement False True = .holder := by decide

/-- Neither condition met selects the elsewhere expletive. -/
example : VoiceAlloseme.fromComplement False False = .expletive := by decide

/-- Bridge: Voice allosemes to syntactic `Flavor`.

    [myler-2016]: syntactically, all four allosemes realize
    the same Voice_{D} — transitive Voice with a DP specifier.
    The θ-role distinction is resolved at LF, not in the syntax.
    We map to the flavor that best captures the syntactic behavior:
    agent/engineer → agentive (phase head, assigns θ);
    holder → experiencer (assigns θ, stative);
    expletive → expletive (no θ, no semantics). -/
def VoiceAlloseme.toFlavor : VoiceAlloseme → Flavor
  | .agent    => .agentive
  | .holder   => .experiencer
  | .engineer => .agentive
  | .expletive => .expletive

/-- All θ-assigning Voice allosemes map to θ-assigning syntactic flavors;
    the non-θ expletive maps to a non-θ flavor. -/
theorem voice_alloseme_theta_consistent (a : VoiceAlloseme) :
    a.assignsTheta = true ↔
      Head.AssignsTheta { flavor := a.toFlavor, hasD := true } := by
  cases a <;> decide

-- ════════════════════════════════════════════════════
-- § 5. Nominalization Reading Derivation (Ch. 3)
-- ════════════════════════════════════════════════════

/-- Reading types for deverbal nominalizations.

    [wood-2023] Ch. 1 (1.18) identifies five terminal reading types;
    [benz-2025] Ch. 3 adds the CCN for German, yielding six:

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
      CP complement ([benz-2025]). -/
inductive NominalizationReading where
  | complexEvent   -- CEN: event reading (takes temporal modifiers, telicity PPs)
  | simpleEvent    -- SEN: event reading without full arg structure
  | result         -- RN: result/product entity (existence results from event)
  | simpleState    -- state reading (e.g. admiration, slavery)
  | simpleEntity   -- simple entity reading, no event connection (e.g. laundry)
  | content        -- CCN: content reading (takes CP complement)
  deriving DecidableEq, Repr

/-- Derive the nominalization reading from the allosemes of v and n.

    Integrates [benz-2025] Ch. 3 and [wood-2023] Ch. 5–6:

    - v_eventive + n_zero → CEN (n is identity, noun = verb meaning)
    - v_eventive + n_sortal → CEN ([benz-2025] mapping)
    - v_eventive + n_result → result/product RN (entity from event)
    - v_zero + n_simpleEvent → SEN (v absent, n picks out event-entity)
    - v_zero + n_state → simple state (v absent, n picks out state)
    - v_zero + n_entity → simple entity RN (no event connection)
    - v_zero + n_sortal → simple entity RN ([benz-2025] mapping)
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

/-- CEN from eventive v + zero n ([wood-2023] Ch. 5). -/
theorem cen_from_zero_n :
    readingFromAllosemes .eventive .zero = some .complexEvent := rfl

/-- CEN from eventive v + sortal n ([benz-2025]). -/
theorem cen_from_sortal_n :
    readingFromAllosemes .eventive .sortal = some .complexEvent := rfl

/-- Result/product RN from eventive v + result n ([wood-2023] Ch. 6 (6.30)). -/
theorem result_from_eventive_v :
    readingFromAllosemes .eventive .result = some .result := rfl

/-- SEN from zero v + simpleEvent n ([wood-2023] Ch. 5). -/
theorem sen_from_zero_v :
    readingFromAllosemes .zero .simpleEvent = some .simpleEvent := rfl

/-- Simple state from zero v + state n ([wood-2023] Ch. 1 (1.18)). -/
theorem state_from_zero_v :
    readingFromAllosemes .zero .state = some .simpleState := rfl

/-- Simple entity from zero v + entity n ([wood-2023] Ch. 5). -/
theorem simpleEntity_from_entity_n :
    readingFromAllosemes .zero .entity = some .simpleEntity := rfl

/-- Simple entity from zero v + sortal n ([benz-2025]). -/
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

-- ════════════════════════════════════════════════════
-- § 7. The `Realization.Interpreted` view (List 3 on the shared carrier)
-- ════════════════════════════════════════════════════

/-! An allosemic head is a List-3 object: a single morpheme whose
*interpretation* is resolved in context by the shared exponence engine.
`Realization.Interpreted` is exactly that carrier — an opaque index with a
contextual `interp` map — so the engine slots in as a view. The form side
(`realize`) is empty (`Unit`, `∅`): allosemy is meaning-only, the List-2
form having been resolved separately. Contextual meaning variation — Benz's
core claim that allosemy is allomorphy's LF analogue — is then literally
`Realization.Interpreted.IsAllosemous`. -/

open Morphology.Exponence in
/-- The allosemy engine as a `Realization.Interpreted` view: one abstract
head (`Unit`) whose contextual interpretation is the alloseme `selectBy`
picks (a singleton, `∅` at a semantic gap), with an empty List-2 form
side. -/
def AllosemicHead.toInterpreted {Sem : Type} (h : AllosemicHead Sem) :
    Realization.Interpreted Unit SyntacticContext Unit Sem where
  realize _ _ := ∅
  interp _ c :=
    match selectBy AllosemicEntry.score h.entries c with
    | some e => {e.denotation}
    | none => ∅

/-- The verbal categorizer's meaning varies with context — eventive under
an eventive complement, zero elsewhere — so v is `IsAllosemous` on the
shared carrier: contextual meaning variation as non-constancy of the
`interp` map ([benz-2025], the LF analogue of allomorphy). -/
theorem vAllosemic_isAllosemous : vAllosemic.toInterpreted.IsAllosemous () :=
  ⟨{ complementIsEventive := true }, { complementIsEventive := false },
   .eventive, by decide, .zero, by decide, by decide⟩

end Morphology.DM.Allosemy
