/-!
# Island Constraint Types

Shared type definitions and classification functions for island constraints.
Raw data lives in individual study files for provenance tracking:
- `Studies/Ross1967.lean`: foundational island examples
- `Studies/HofmeisterSag2010.lean`: gradient acceptability data
- `Studies/ShenHuang2026.lean`: definite island + VOC + crosslinguistic data
- `Studies/CartnerEtAl2026.lean`: subject island + construction generality data
- `Studies/Adger2025.lean`: mereological syntax derivations
-/

-- ============================================================================
-- Constraint Types
-- ============================================================================

/-- Types of island constraints (descriptive labels) -/
inductive ConstraintType where
  | embeddedQuestion  -- Wh-word blocks further wh-dependency
  | complexNP         -- Complex NP blocks dependency
  | adjunct           -- Adjunct clause blocks dependency
  | coordinate        -- Coordination blocks asymmetric dependency
  | subject           -- Subject position blocks dependency
  | sententialSubject -- Sentential subject blocks dependency
  | mannerOfSpeaking  -- MoS verb complement backgrounds content (@cite{lu-pan-degen-2025})
  | definiteNominal   -- Definite/specific DP blocks dependency (@cite{chomsky-1973},
                       -- @cite{fiengo-higginbotham-1981}, @cite{shen-huang-2026})
  deriving Repr, DecidableEq

/-- Constraint strength classification -/
inductive ConstraintStrength where
  | strong  -- Consistently blocks the dependency
  | weak    -- Ameliorated in some contexts (e.g., D-linked wh-phrases)
  deriving Repr, DecidableEq

/-- Classification of constraint types by strength -/
def constraintStrength : ConstraintType → ConstraintStrength
  | .embeddedQuestion => .weak      -- Ameliorated with D-linking
  | .complexNP => .strong           -- Generally strong
  | .adjunct => .strong             -- Generally strong
  | .coordinate => .strong          -- Strong (but ATB pattern ok)
  | .subject => .weak               -- Varies cross-linguistically
  | .sententialSubject => .strong
  | .mannerOfSpeaking => .weak      -- Ameliorated by prosodic focus (@cite{lu-pan-degen-2025})
  | .definiteNominal => .weak       -- Ameliorated by VOCs in English (@cite{shen-huang-2026})

-- ============================================================================
-- Filler-Gap Dependency Construction Types
-- ============================================================================

/-- The three canonical filler-gap dependency constructions in English.
Each shares the abstract mechanism of movement (a filler displaced from a gap)
but differs in information-structural profile (@cite{abeille-et-al-2020}).

The distinction matters for testing whether island effects are
construction-specific (as @cite{abeille-et-al-2020} claim) or
construction-general (as @cite{cartner-et-al-2026} argue). -/
inductive FGDConstruction where
  /-- Wh-questions: "Which driver did Stephanie explain _ had already
  questioned the driver?" -/
  | whQuestion
  /-- Relative clauses: "I noticed [the investigator that Stephanie
  explained _ had already questioned the driver]." -/
  | relativeClause
  /-- Topicalization: "That investigator, Stephanie explained _ had already
  questioned the driver." -/
  | topicalization
  deriving DecidableEq, Repr, BEq

/-- Extraction position within the embedded clause.
The subject/object asymmetry is the core empirical target of subject island
research (@cite{ross-1967}, @cite{chomsky-1973}). -/
inductive ExtractionPosition where
  | subject
  | object
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- Island Source Classification
-- ============================================================================

/-- Source of an island constraint: what mechanism produces it.
Distinguishes structural accounts (subjacency), processing accounts
(memory load), semantic accounts (binding restrictions), and discourse
accounts (information structure). -/
inductive IslandSource where
  /-- Syntactic: island follows from structural configuration (PIC, subjacency) -/
  | syntactic
  /-- Semantic: island follows from a binding restriction (Specificity Condition) -/
  | semantic
  /-- Processing: island is an artifact of memory/retrieval difficulty -/
  | processing
  /-- Discourse: island arises from information-structural backgroundedness (@cite{goldberg-2006}, 2013;
  @cite{lu-pan-degen-2025}) -/
  | discourse
  deriving Repr, DecidableEq, BEq

/-- Classification of island constraints by source.

Some constraints have a single source; others are composite.
@cite{shen-huang-2026} show that definite nominal islands require BOTH
syntactic (PIC) and semantic (Specificity Condition) sources — neither
alone accounts for the full crosslinguistic pattern.

Traditional islands are syntactic; MoS islands are discourse-based.
Note: this classification is itself debated — @cite{hofmeister-sag-2010} argue that many
"syntactic" islands are actually processing-based. See `Comparisons/Islands.lean`. -/
def constraintSources : ConstraintType → List IslandSource
  | .embeddedQuestion  => [.syntactic]  -- but see @cite{hofmeister-sag-2010} for processing account
  | .complexNP         => [.syntactic]  -- but see @cite{hofmeister-sag-2010} for processing account
  | .adjunct           => [.syntactic]
  | .coordinate        => [.syntactic]
  | .subject           => [.syntactic]
  | .sententialSubject => [.syntactic]
  | .mannerOfSpeaking  => [.discourse]  -- @cite{lu-pan-degen-2025}
  | .definiteNominal   => [.syntactic, .semantic]
      -- PIC (syntactic) + Specificity Condition (semantic)
      -- @cite{shen-huang-2026}: both are needed for crosslinguistic coverage

-- ============================================================================
-- Wh-Dependency Type (@cite{shen-huang-2026} §4)
-- ============================================================================

/-- How a wh-dependency is established in a given language/construction.

@cite{shen-huang-2026}: overt wh-movement and wh-in-situ are subject to
DIFFERENT locality constraints. Movement is constrained by both the PIC
and the Specificity Condition. Binding (in-situ) is constrained only by
the Specificity Condition — the PIC does not apply because no element
crosses a phase boundary.

@cite{fox-pesetsky-2005} (cyclic linearization): binding does not change
linear order, so it cannot create ordering contradictions at Spell-out,
making it PIC-insensitive. -/
inductive WhDependencyType where
  /-- Overt movement to Spec,CP — subject to PIC + Specificity Condition.
      English wh-fronting, Slavic wh-fronting, etc. -/
  | movement
  /-- In-situ binding by a covert operator — subject to Specificity Condition only.
      Mandarin Chinese, Japanese, Korean wh-in-situ. -/
  | binding
  deriving DecidableEq, BEq, Repr

/-- Which island sources constrain a given dependency type.

Movement is constrained by both syntactic (PIC) and semantic (Specificity)
sources. Binding is constrained only by the semantic source.

This derives the key crosslinguistic prediction of @cite{shen-huang-2026}:
- English (movement): VOCs can ameliorate via PIC neutralization → partial effect
- Chinese (binding): VOCs cannot help because PIC is irrelevant → no VOC effect -/
def constraintsForDependencyType : WhDependencyType → List IslandSource
  | .movement => [.syntactic, .semantic]  -- PIC + Specificity
  | .binding  => [.semantic]              -- Specificity only

-- ============================================================================
-- VOC Neutralization (@cite{shen-huang-2026} §4.1)
-- ============================================================================

/-- Whether VOCs (verbs of creation) can neutralize this island source.

VOCs neutralize phasehood via N/D-incorporation (@cite{davies-dubinsky-2003}):
the created object's DP loses its phase status, removing the syntactic
barrier to extraction. But VOCs cannot affect the Specificity Condition
(semantic), processing difficulty, or discourse structure. -/
def vocNeutralizes : IslandSource → Bool
  | .syntactic  => true   -- N/D-incorporation removes phase boundary
  | .semantic   => false  -- specificity is a binding restriction, unaffected
  | .processing => false
  | .discourse  => false
