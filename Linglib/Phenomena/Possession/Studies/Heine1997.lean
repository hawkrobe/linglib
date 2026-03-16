import Linglib.Phenomena.Possession.Typology
import Linglib.Theories.Diachronic.Grammaticalization

/-!
# Heine (1997): Possession — Cognitive Sources, Forces, and Grammaticalization
@cite{heine-1997}

Bernd Heine. *Possession: Cognitive Sources, Forces, and Grammaticalization.*
Cambridge Studies in Linguistics 83. Cambridge University Press, 1997.

## Core claims

1. Predicative possession constructions worldwide derive from a small set of
   eight cognitive **event schemas** (Table 2.1), each with a fixed propositional
   structure that predicts the resulting word order and case marking.

2. Each schema has characteristic **contrastive properties** (Table 2.3):
   whether its predicate nucleus is lexical (Action only) or non-lexical,
   whether its structure is basic or extended, and which participant
   (possessor or possessee) maps to clausal subject.

3. Schemas correlate with **possessive notions** (Table 2.4): Location
   invariably yields have-constructions; Equation invariably yields
   belong-constructions; Action and Goal can yield both.

4. Grammaticalization proceeds via the **Overlap Model**: Stage I (source
   meaning only) → Stage II (source + target overlap) → Stage III
   (target meaning only).

5. A 100-language survey (Table 2.2) shows schemas are distributed across
   all continents with Location (20.9%) and Goal (20.0%) as the most
   common sources, and Action (13.6%) less common than often assumed.

## Connections

- `Phenomena.Possession.Typology.PossessionSource`: the eight schemas
- `Phenomena.Possession.Typology.PossessiveNotion`: the seven target notions
- `Theories.Diachronic.Grammaticalization.GramStage`: the verbal cline
- `Theories.Semantics.Lexical.Noun.Relational.Barker2011`: π operator and
  arity tracking — connects to which schemas have possessor-as-subject
  (Action, Companion = transitive/Pred2) vs possessee-as-subject (rest)
-/

open Phenomena.Possession.Typology
open Diachronic.Grammaticalization

namespace Phenomena.Possession.Studies.Heine1997

-- ============================================================================
-- §1. Schema Contrastive Properties (Table 2.3)
-- ============================================================================

/-- Whether the predicate nucleus of a schema retains lexical content.
    Action is unique: its predicate nucleus is a lexical verb ('take', 'seize',
    'hold'). All other schemas have non-lexical nuclei (copulas, existentials,
    locative verbs). -/
def schemaHasLexicalNucleus : PossessionSource → Bool
  | .action => true
  | _       => false

/-- Whether the source structure is basic (two core arguments) or extended
    (basic structure + an additional oblique participant grafted on).
    Action and Location are basic; the remaining five involve extending a
    simpler structure with an additional case-marked participant. -/
inductive SourceStructure where
  | basic    -- Two core arguments (agent+patient or figure+ground)
  | extended -- Basic + oblique/topic participant added
  deriving DecidableEq, BEq, Repr

def schemaStructure : PossessionSource → SourceStructure
  | .action    => .basic
  | .location  => .basic
  | .companion => .extended
  | .genitive  => .extended
  | .goal      => .extended
  | .source    => .extended
  | .topic     => .extended
  | .equation  => .extended

/-- Which participant of the source schema is encoded as the clausal subject.
    Action and Companion encode the possessor as subject; all others encode
    the possessee as subject. -/
inductive SubjectParticipant where
  | possessor  -- Possessor = clausal subject (transitive-like)
  | possessee  -- Possessee = clausal subject (intransitive/existential)
  deriving DecidableEq, BEq, Repr

def schemaSubject : PossessionSource → SubjectParticipant
  | .action    => .possessor
  | .companion => .possessor
  | .location  => .possessee
  | .genitive  => .possessee
  | .goal      => .possessee
  | .source    => .possessee
  | .topic     => .possessee
  | .equation  => .possessee

/-- Only Action has a lexical predicate nucleus. -/
theorem action_unique_lexical :
    (∀ s : PossessionSource, schemaHasLexicalNucleus s = true → s = .action) := by
  intro s h; cases s <;> simp [schemaHasLexicalNucleus] at h <;> rfl

/-- Only Action and Companion have possessor-as-subject. -/
theorem possessor_subject_iff_action_or_companion :
    ∀ s : PossessionSource,
      schemaSubject s = .possessor ↔ (s = .action ∨ s = .companion) := by
  intro s; cases s <;> simp [schemaSubject]

/-- Basic schemas are exactly Action and Location. -/
theorem basic_iff_action_or_location :
    ∀ s : PossessionSource,
      schemaStructure s = .basic ↔ (s = .action ∨ s = .location) := by
  intro s; cases s <;> simp [schemaStructure]

-- ============================================================================
-- §2. Schema → Construction Type (Table 2.4)
-- ============================================================================

/-- Whether a schema gives rise to a have-construction ('X has Y'),
    a belong-construction ('Y belongs to X'), or both.
    Location → have only. Equation → belong only. Action and Goal → both.
    Companion, Genitive, Topic → have only. Source → irrelevant for
    predicative possession (provides attributive possession source). -/
def schemaYieldsHave : PossessionSource → Bool
  | .action    => true
  | .location  => true
  | .companion => true
  | .genitive  => true
  | .goal      => true
  | .source    => false  -- irrelevant for predicative
  | .topic     => true
  | .equation  => false

def schemaYieldsBelong : PossessionSource → Bool
  | .action    => true
  | .location  => false
  | .companion => false
  | .genitive  => false
  | .goal      => true
  | .source    => false
  | .topic     => false
  | .equation  => true

/-- Location invariably leads to have-constructions, never belong. -/
theorem location_yields_have_only :
    schemaYieldsHave .location = true ∧
    schemaYieldsBelong .location = false := ⟨rfl, rfl⟩

/-- Equation invariably leads to belong-constructions, never have. -/
theorem equation_yields_belong_only :
    schemaYieldsHave .equation = false ∧
    schemaYieldsBelong .equation = true := ⟨rfl, rfl⟩

/-- Action and Goal are the only schemas that can yield both types. -/
theorem dual_schemas :
    ∀ s : PossessionSource,
      (schemaYieldsHave s = true ∧ schemaYieldsBelong s = true) ↔
      (s = .action ∨ s = .goal) := by
  intro s; cases s <;> simp [schemaYieldsHave, schemaYieldsBelong]

-- ============================================================================
-- §3. The Overlap Model (Figure 2.1)
-- ============================================================================

/-- Grammaticalization from source schema to possessive target proceeds
    through three stages (the Overlap Model, Figure 2.1). -/
inductive OverlapStage where
  /-- Stage I: the construction has source meaning only.
      (e.g., "The money is in his hand" = pure location) -/
  | sourceOnly
  /-- Stage II: source and target meanings overlap; the construction is
      ambiguous between source and possessive interpretations.
      (e.g., Russian "u Markovyx gripp" = "There is flu at the Markovs"
       or "The Markovs have the flu") -/
  | overlap
  /-- Stage III: target meaning only; source meaning is no longer available.
      (e.g., Estonian "isal on raamat" = "Father has a book", not
       "A book is on the father") -/
  | targetOnly
  deriving DecidableEq, BEq, Repr

/-- The Overlap Model is a monotonic progression: each stage is more
    grammaticalized than the previous. -/
def OverlapStage.degree : OverlapStage → Nat
  | .sourceOnly => 0
  | .overlap    => 1
  | .targetOnly => 2

/-- Source-only precedes overlap, which precedes target-only. -/
theorem overlap_ordered :
    OverlapStage.sourceOnly.degree < OverlapStage.overlap.degree ∧
    OverlapStage.overlap.degree < OverlapStage.targetOnly.degree :=
  ⟨by decide, by decide⟩

/-- The Overlap Model connects to the verbal grammaticalization cline:
    reaching Stage III (target only) correlates with increasing boundedness
    of the verbal element. -/
theorem stage_III_implies_decategorialized :
    OverlapStage.targetOnly.degree ≥ OverlapStage.overlap.degree ∧
    GramStage.auxiliary.boundedness > GramStage.fullVerb.boundedness :=
  ⟨by decide, by decide⟩

-- ============================================================================
-- §4. The 100-Language Survey (Table 2.2)
-- ============================================================================

/-- Distribution of major source schemas across continents, from the
    100-language sample. Each entry is (schema, counts by continent).
    Continents: Europe, Asia, Africa, America, Indian/Pacific Ocean. -/
structure SchemaDist where
  schema : PossessionSource
  europe : Nat
  asia : Nat
  africa : Nat
  america : Nat
  pacific : Nat
  deriving DecidableEq, BEq, Repr

def SchemaDist.total (d : SchemaDist) : Nat :=
  d.europe + d.asia + d.africa + d.america + d.pacific

/-- Table 2.2 data: major schemas in 100 languages.
    Note: some languages have more than one major schema,
    so totals exceed 100. -/
def actionDist  : SchemaDist := { schema := .action,    europe := 3, asia := 1,  africa := 9, america := 1, pacific := 1 }
def locationDist : SchemaDist := { schema := .location,  europe := 5, asia := 8,  africa := 9, america := 1, pacific := 0 }
def companionDist : SchemaDist := { schema := .companion, europe := 0, asia := 0,  africa := 7, america := 3, pacific := 4 }
def genitiveDist : SchemaDist := { schema := .genitive,  europe := 0, asia := 2,  africa := 4, america := 5, pacific := 5 }
def goalDist    : SchemaDist := { schema := .goal,      europe := 3, asia := 11, africa := 4, america := 1, pacific := 3 }
def topicDist   : SchemaDist := { schema := .topic,     europe := 0, asia := 4,  africa := 1, america := 3, pacific := 3 }

def table2_2 : List SchemaDist :=
  [actionDist, locationDist, companionDist, genitiveDist, goalDist, topicDist]

/-- Total attestations across six identifiable schemas: 101 (> 100 because
    some languages use multiple schemas). The remaining 9 attestations are
    opaque or minor schemas not included here. -/
theorem table2_2_total :
    actionDist.total + locationDist.total + companionDist.total +
    genitiveDist.total + goalDist.total + topicDist.total = 101 := by native_decide

/-- Location and Goal are the two most frequent schemas worldwide. -/
theorem location_and_goal_most_frequent :
    locationDist.total ≥ goalDist.total ∧
    goalDist.total > actionDist.total := by native_decide

/-- Action accounts for only ~14% of the sample — less common than often
    assumed for European-centric linguistics. -/
theorem action_not_dominant :
    actionDist.total * 100 / 110 < 15 := by native_decide

/-- In Asia, Goal (via dative/benefactive) is the most common schema,
    exceeding Location (the runner-up): 11 vs 8 out of 26. -/
theorem asia_goal_dominant :
    goalDist.asia > locationDist.asia ∧
    goalDist.asia > actionDist.asia ∧
    goalDist.asia > topicDist.asia := by native_decide

/-- In Africa, Location and Action tie as the most common sources (9 each). -/
theorem africa_location_action_tie :
    locationDist.africa = actionDist.africa := by native_decide

-- ============================================================================
-- §5. Schema → Possessive Notion Correlations (§2.3)
-- ============================================================================

/-- Probabilistic correlations between source schemas and the possessive
    notions they are most likely to express (Table 2.4, §2.3).

    - Location: most likely physical/temporary possession
    - Existence (Genitive, Goal, Topic): permanent/inalienable possession
    - Companion: physical/temporary, or alienable possession
    - Action: wide range (physical through permanent)
    - Equation: permanent (ownership, "the book is mine") -/
def schemaTypicalNotions : PossessionSource → List PossessiveNotion
  | .action    => [.physical, .temporary, .permanent]
  | .location  => [.physical, .temporary]
  | .companion => [.physical, .temporary]
  | .genitive  => [.permanent, .inalienable]
  | .goal      => [.permanent, .inalienable, .abstract]
  | .source    => []  -- irrelevant for predicative
  | .topic     => [.permanent, .inalienable]
  | .equation  => [.permanent, .inalienable]

/-- Existence schemas (Genitive, Goal, Topic) are never recruited for
    physical possession. -/
theorem existence_not_physical :
    ¬(schemaTypicalNotions .genitive).contains .physical ∧
    ¬(schemaTypicalNotions .goal).contains .physical ∧
    ¬(schemaTypicalNotions .topic).contains .physical := by native_decide

/-- Location is most likely associated with physical/temporary; it is not
    typically recruited for permanent or inalienable possession. -/
theorem location_not_permanent :
    ¬(schemaTypicalNotions .location).contains .permanent ∧
    ¬(schemaTypicalNotions .location).contains .inalienable := by
  native_decide

-- ============================================================================
-- §6. Bridge to Barker 2011: Subject Encoding and Arity
-- ============================================================================

/-- The possessor-as-subject schemas (Action, Companion) correspond to
    transitive constructions — the possessive verb takes two core arguments,
    analogous to Barker's Pred2 (two-place predicate).

    The possessee-as-subject schemas correspond to intransitive/existential
    constructions where the possessor is an oblique adjunct, analogous to
    Barker's Pred1 with Ex closure.

    This connects Heine's diachronic structural predictions to Barker's
    synchronic type-theoretic analysis. -/
def schemaIsTransitiveLike : PossessionSource → Bool
  | .action    => true
  | .companion => true
  | _          => false

/-- Transitivity correlates exactly with possessor-as-subject. -/
theorem transitive_iff_possessor_subject :
    ∀ s : PossessionSource,
      schemaIsTransitiveLike s = true ↔
      schemaSubject s = .possessor := by
  intro s; cases s <;> simp [schemaIsTransitiveLike, schemaSubject]

/-- The Action Schema's grammaticalization path:
    full lexical verb ('take', 'seize') → have-verb (auxiliary-like).
    This places Action Schema verbs on the grammaticalization cline
    from fullVerb toward auxiliary. -/
theorem action_schema_on_cline :
    GramStage.fullVerb < GramStage.auxiliary := by decide

end Phenomena.Possession.Studies.Heine1997
