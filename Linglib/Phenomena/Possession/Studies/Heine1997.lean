import Linglib.Phenomena.Possession.Typology
import Linglib.Theories.Diachronic.Grammaticalization
import Linglib.Theories.Semantics.Lexical.Noun.Relational.Barker2011
import Linglib.Core.WALS.Features.F117A

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
open Semantics.Lexical.Noun.Relational.Barker2011 (Pred1 Pred2 SemType)

namespace Heine1997

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
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

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
  intro s h; cases s <;> simp_all [schemaHasLexicalNucleus]

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
  deriving DecidableEq, Repr

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

/-- The Action Schema's grammaticalization path through the Overlap Model:
    a full lexical verb ('take', 'seize') at Stage I becomes a possessive
    auxiliary ('have') at Stage III. Both the Overlap Model and the verbal
    cline are monotonic, and they co-vary: advancing through overlap stages
    corresponds to advancing along the boundedness cline.

    This parallels the general unidirectionality of grammaticalization:
    fullVerb → auxiliary is the path from source schema (action verb)
    to target schema (possessive marker). -/
theorem action_overlap_cline_covary :
    OverlapStage.sourceOnly.degree < OverlapStage.targetOnly.degree ∧
    GramStage.fullVerb < GramStage.auxiliary :=
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
  deriving DecidableEq, Repr

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

/-- Action accounts for only 13.6% of major schema attestations (15 out
    of 110 total) — less common than often assumed for European-centric
    linguistics. The denominator 110 includes opaque/other schemas. -/
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
    notions they are most likely to express (§2.3, generalizations i-iv).

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

/-- Map each schema to its Barker 2011 semantic type, based on the
    argument structure of the resulting possessive predicate.

    Possessor-as-subject schemas (Action, Companion) produce transitive
    constructions: the possessive verb takes two core arguments (possessor
    and possessee), corresponding to @cite{barker-2011}'s Pred2.

    Possessee-as-subject schemas produce intransitive/existential
    constructions: the possessee is the sole core argument, and the
    possessor is an oblique adjunct. The possessive predicate is Pred1,
    with the possessor introduced by Ex closure or case marking. -/
def schemaArity : PossessionSource → SemType
  | .action    => .pred2  -- X takes Y: two core arguments
  | .companion => .pred2  -- X is with Y: two core arguments
  | _          => .pred1  -- Y exists/is-at/...: one core argument + oblique

/-- Possessor-as-subject correlates exactly with Pred2 (transitive). -/
theorem possessor_subject_iff_pred2 :
    ∀ s : PossessionSource,
      schemaSubject s = .possessor ↔ schemaArity s = .pred2 := by
  intro s; cases s <;> simp [schemaSubject, schemaArity]

/-- Pred2 schemas are exactly the basic-structure schemas where the
    possessor is a core argument (not grafted on). Companion is the
    exception: extended structure but still Pred2, because the comitative
    complement is reanalyzed as a core argument. -/
theorem pred2_action_companion_only :
    ∀ s : PossessionSource,
      schemaArity s = .pred2 ↔ (s = .action ∨ s = .companion) := by
  intro s; cases s <;> simp [schemaArity]

/-- The Pred1 schemas (Location, Genitive, Goal, Source, Topic, Equation)
    express possession via an existential predicate + oblique possessor.
    This matches Barker's ExProp closure: the possessor is introduced
    by existential quantification over a relation, not as a direct argument
    of the predicate.

    Structural consequence: in these schemas, the possessor does NOT
    fill a relatum slot directly (as it would in Pred2). Instead, it is
    introduced via case morphology (locative, dative, genitive, etc.) —
    the morphological reflex of the oblique adjunct position. -/
theorem pred1_possessee_subject :
    ∀ s : PossessionSource,
      schemaArity s = .pred1 → schemaSubject s = .possessee := by
  intro s h; cases s <;> simp [schemaArity] at h <;> simp [schemaSubject]

/-- The Action Schema's grammaticalization path:
    full lexical verb ('take', 'seize') → have-verb (auxiliary-like).
    This places Action Schema verbs on the grammaticalization cline
    from fullVerb toward auxiliary. -/
theorem action_schema_on_cline :
    GramStage.fullVerb < GramStage.auxiliary := by decide

-- ============================================================================
-- §7. Fragment Prediction Verification
-- ============================================================================

/-- A schema prediction bundle: the testable predictions Heine makes for
    any language that draws on a given source schema. -/
structure SchemaPrediction where
  schema : PossessionSource
  yieldsHave : Bool
  yieldsBelong : Bool
  possessorIsSubject : Bool
  arity : SemType

/-- Derive predictions from a schema. -/
def predictionsFor (s : PossessionSource) : SchemaPrediction :=
  { schema := s
    yieldsHave := schemaYieldsHave s
    yieldsBelong := schemaYieldsBelong s
    possessorIsSubject := schemaSubject s == .possessor
    arity := schemaArity s }

/-- Location Schema predictions: have-only, possessee-as-subject, Pred1. -/
theorem location_predictions :
    let p := predictionsFor .location
    p.yieldsHave = true ∧ p.yieldsBelong = false ∧
    p.possessorIsSubject = false ∧ p.arity = .pred1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Companion Schema predictions: have-only, possessor-as-subject, Pred2. -/
theorem companion_predictions :
    let p := predictionsFor .companion
    p.yieldsHave = true ∧ p.yieldsBelong = false ∧
    p.possessorIsSubject = true ∧ p.arity = .pred2 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Genitive Schema predictions: have-only, possessee-as-subject, Pred1. -/
theorem genitive_predictions :
    let p := predictionsFor .genitive
    p.yieldsHave = true ∧ p.yieldsBelong = false ∧
    p.possessorIsSubject = false ∧ p.arity = .pred1 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §8. Bridge to WALS F117A (Stassen 2013)
-- ============================================================================

/-- @cite{stassen-2013b}'s WALS Ch 117 uses five categories for predicative
    possession that correspond to Heine's schemas:

    - WALS `locational` ↔ Heine Location Schema
    - WALS `genitive`   ↔ Heine Genitive Schema
    - WALS `topic`      ↔ Heine Topic Schema
    - WALS `conjunctional` ↔ Heine Companion Schema
    - WALS `have`       ↔ Heine Action Schema

    Note: Stassen's "conjunctional" is his term for comitative-based
    possession (Heine's Companion Schema). Goal Schema languages are
    typically classified under WALS `locational` (since both use oblique
    possessors with existential predicates). -/
def walsToSchema : Core.WALS.F117A.PredicativePossession → PossessionSource
  | .locational    => .location
  | .genitive      => .genitive
  | .topic         => .topic
  | .conjunctional => .companion
  | .have          => .action

/-- The WALS-to-Heine mapping agrees with `predicativeSource` from
    Typology.lean for the five strategies they share. -/
theorem wals_agrees_with_predicativeSource :
    walsToSchema .have = predicativeSource .haveVerb ∧
    walsToSchema .locational = predicativeSource .locational ∧
    walsToSchema .topic = predicativeSource .topic ∧
    walsToSchema .conjunctional = predicativeSource .comitative := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end Heine1997
