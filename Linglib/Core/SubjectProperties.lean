/-!
# Subject Properties @cite{comrie-1989}

@cite{comrie-1989} (Ch 5) argues that "subject" is not a primitive
cross-linguistic category but a **bundle** of coding and behavioral properties.
In accusative languages, all properties converge on the same NP (the S=A
argument). In ergative languages, they may diverge: coding properties
(case, agreement) pick out S=P (absolutive), while behavioral properties
(conjunction reduction, reflexivization, raising) often pick out S=A.

## Coding Properties

How the "subject" NP is morphologically identified:
- **Case marking**: receives the unmarked or nominative/absolutive case
- **Verb agreement**: triggers person/number agreement on the finite verb
- **Word order**: occupies the canonical pre-verbal or clause-initial position

## Behavioral Properties

How the "subject" NP participates in cross-clausal syntactic operations:
- **Conjunction reduction**: the omitted NP under coordination
- **Reflexivization**: the antecedent of clause-bound reflexives
- **Raising**: the NP that raises to a higher clause subject position
- **Equi-NP deletion**: the NP deleted as controlled PRO
- **Relativization**: the most accessible position on the
  @cite{keenan-comrie-1977} Accessibility Hierarchy

## Key Generalization

In accusative languages, all properties pick out S=A → full convergence.
In syntactically ergative languages (rare), coding picks out S=P while
behavioral properties still pick out S=A. In morphologically ergative
languages (common), coding picks out S=P but behavioral properties also
pick out S=P (Dyirbal-type). The split between these patterns is one of
the central diagnostics for "deep" vs "surface" ergativity.
-/

namespace Core.SubjectProperties

-- ============================================================================
-- § 1: Property Types
-- ============================================================================

/-- Coding properties: how the subject NP is morphologically marked.
    These are "surface" properties visible from case and agreement alone. -/
inductive CodingProperty where
  | caseMarking       -- receives nominative/absolutive case
  | verbAgreement     -- triggers person/number agreement on finite verb
  | wordOrderPosition -- occupies canonical subject position
  deriving DecidableEq, Repr

/-- Behavioral properties: how the subject NP participates in
    syntactic operations that span clause boundaries. These are
    the "deep" properties that motivate a grammatical-relation analysis. -/
inductive BehavioralProperty where
  | conjunctionReduction  -- deleted/omitted NP under coordination
  | reflexivization       -- antecedent of clause-bound reflexives
  | raisingTarget         -- NP that raises to higher clause
  | equiDeletion          -- controlled PRO in complement clause
  | relativizationAccess  -- most accessible on AH
  deriving DecidableEq, Repr

/-- All coding properties (for finite enumeration). -/
def CodingProperty.all : List CodingProperty :=
  [.caseMarking, .verbAgreement, .wordOrderPosition]

/-- All behavioral properties (for finite enumeration). -/
def BehavioralProperty.all : List BehavioralProperty :=
  [.conjunctionReduction, .reflexivization, .raisingTarget,
   .equiDeletion, .relativizationAccess]

-- ============================================================================
-- § 2: Subject Property Bundle
-- ============================================================================

/-- A subject property bundle: for each property, which NP grouping
    it picks out in a given language.

    - `true` = S=A grouping (accusative pattern for that property)
    - `false` = S=P grouping (ergative pattern for that property)

    A language's "subject" is well-defined when all properties agree;
    it is a non-primitive cluster concept when they diverge. -/
structure SubjectPropertyBundle where
  coding : CodingProperty → Bool
  behavioral : BehavioralProperty → Bool

-- ============================================================================
-- § 3: Canonical Bundles
-- ============================================================================

/-- Accusative convergence: all properties pick out S=A.
    English, Latin, Russian, Japanese, etc. -/
def accusativeBundle : SubjectPropertyBundle where
  coding := λ _ => true
  behavioral := λ _ => true

/-- Morphological ergativity with accusative syntax: coding picks S=P
    (absolutive case/agreement), but behavioral tests pick S=A.
    This is the common pattern in "ergative" languages: Dyirbal main
    clauses, many Australian and Mayan languages. -/
def morphErgativityBundle : SubjectPropertyBundle where
  coding := λ _ => false
  behavioral := λ _ => true

/-- Full (syntactic) ergativity: both coding AND behavioral properties
    pick out S=P. Rare cross-linguistically; Dyirbal subordinate clauses
    are the classic example. -/
def syntacticErgativityBundle : SubjectPropertyBundle where
  coding := λ _ => false
  behavioral := λ _ => false

-- ============================================================================
-- § 4: Convergence
-- ============================================================================

/-- Whether all subject properties converge on the same NP.
    Convergence means all coding and behavioral properties agree on either
    S=A (accusative) or S=P (ergative). Divergence — some properties
    picking S=A and others S=P — means "subject" is not a unitary concept
    in that language. -/
def SubjectPropertyBundle.converges (b : SubjectPropertyBundle) : Bool :=
  let allVals := CodingProperty.all.map b.coding ++
                 BehavioralProperty.all.map b.behavioral
  allVals.all (· == true) || allVals.all (· == false)

/-- Accusative bundle converges: all properties pick out S=A. -/
theorem accusative_converges : accusativeBundle.converges = true := by decide

/-- Syntactic ergativity bundle converges: all properties pick out S=P. -/
theorem syntacticErgativity_converges :
    syntacticErgativityBundle.converges = true := by decide

/-- Morphological ergativity diverges: coding picks S=P, behavioral picks S=A. -/
theorem morphErgativity_diverges :
    morphErgativityBundle.converges = false := by decide

end Core.SubjectProperties
