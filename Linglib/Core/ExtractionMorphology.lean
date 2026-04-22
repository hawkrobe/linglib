/-!
# Extraction Morphology
@cite{elkins-torrence-brown-2026} @cite{erlewine-2018} @cite{erlewine-2016}

Theory-neutral types for cross-linguistic extraction morphology ---
how languages morphologically mark that a constituent has undergone
A-bar-movement (wh-movement, relativization, focus fronting, etc.).

Languages vary dramatically in whether and how they track extraction:
- English: no overt marking (gap strategy)
- Austronesian (Tagalog, Malagasy): voice alternation marks which argument
  has been extracted
- Mayan (Mam, K'iche'): dedicated morphemes on verbal complex
  (Mam =(y)a', K'iche' *wi*)
- Celtic (Irish): complementizer changes form (*aL* vs. *aN*)
- Chamorro: agreement morphology tracks extracted position

-/

namespace Interfaces

-- ============================================================================
-- S 1: Extraction Marking Strategy
-- ============================================================================

/-- How a language morphologically marks extraction (A-bar-movement).

    This is a descriptive typology of the *surface* strategy; different
    syntactic theories will derive these differently. -/
inductive ExtractionMarkingStrategy where
  /-- No overt marking of extraction. The extracted position is a silent gap.
      E.g., English "What did you buy __?" -/
  | none
  /-- Voice alternation: the verbal voice morphology changes to mark which
      argument has been extracted. E.g., Tagalog Actor/Patient/Locative voice. -/
  | voiceAlternation
  /-- A dedicated morpheme appears on the verbal complex when extraction occurs.
      E.g., Mam =(y)a' on Voice0/Dir0, K'iche' *wi*, Irish complementizer *aL*. -/
  | dedicatedMorpheme
  /-- Agreement morphology on the verb tracks the extracted position.
      E.g., Chamorro wh-agreement. -/
  | agreementTracking
  /-- The complementizer changes form depending on whether extraction has
      occurred through its clause. E.g., Irish *aL* (direct) vs. *aN* (indirect). -/
  | complementizerChange
  /-- Extraction is structurally restricted to a designated position (the
      "pivot"), not by surface morphology but by clause-structural factors
      such as predicate fronting + anti-locality. Voice morphology determines
      *which* argument occupies the pivot, but the restriction itself is
      structural. E.g., Toba Batak. -/
  | structuralRestriction
  /-- Clause-local extraction of a specific argument role (typically
      agent/ergative) triggers an alternation in clause structure --- a
      "repair" that avoids a locality crash. The canonical case is
      Kaqchikel Agent Focus: clause-local agent extraction
      crashes the normal transitive because movement from Spec,TP to
      Spec,CP violates Spec-to-Spec Anti-Locality (SSAL), so the grammar
      selects an intransitive-like AF structure with distinct verbal
      morphology (*-Vn*, no Set A). Long-distance agent extraction does
      NOT trigger AF --- the repair is locality-sensitive. -/
  | agentFocusAlternation
  deriving DecidableEq, Repr

-- ============================================================================
-- S 2: Extraction Target
-- ============================================================================

/-- The grammatical position from which extraction occurs.

    This intersects with the @cite{keenan-comrie-1977} Accessibility Hierarchy
    (see `Phenomena/Relativization/Typology.lean`), but is defined
    independently because extraction morphology may make finer distinctions
    than relativization. -/
inductive ExtractionTarget where
  /-- Subject (ergative/nominative) extraction -/
  | subject
  /-- Direct object (accusative/absolutive) extraction -/
  | directObject
  /-- Indirect object (dative/applicative) extraction -/
  | indirectObject
  /-- Oblique (instrumental, locative, etc.) extraction -/
  | oblique
  /-- Possessor extraction -/
  | possessor
  deriving DecidableEq, Repr

/-- The thematic category of an argument being extracted: agent
    (external argument), patient (internal argument), or oblique.

    Coarser than `ThetaRole` (which distinguishes agent/experiencer/
    causer, patient/theme, goal/source/instrument). Used when the
    relevant distinction is which macro-role is extracted, not fine-
    grained thematic relations or structural positions.

    Complements `ExtractionTarget` (structural position): ArgumentRole
    identifies *what* is extracted; ExtractionTarget identifies *where*
    it was extracted. The two coincide in simple active clauses
    (agent = subject, patient = object) but diverge under voice
    alternation (in OV, the patient becomes the subject). -/
inductive ArgumentRole where
  | agent    -- external argument (agent, experiencer, causer)
  | patient  -- internal argument (patient, theme)
  | oblique  -- oblique argument (instrument, goal, source, etc.)
  deriving DecidableEq, Repr

/-- Default structural position for a given argument role (active voice). -/
def ArgumentRole.defaultPosition : ArgumentRole → ExtractionTarget
  | .agent => .subject
  | .patient => .directObject
  | .oblique => .oblique

/-- What is being extracted: a DP argument (which has a thematic role
    and needs Case licensing) or a non-DP adjunct (which has no
    thematic role and is Case-exempt).

    This distinction drives the DP/non-DP extraction asymmetry: in
    predicate-fronting languages like Toba Batak, only DP extraction
    is restricted to the pivot; adjuncts extract freely. -/
inductive Extractee where
  | dpArg : ArgumentRole → Extractee
  | adjunct : Extractee
  deriving DecidableEq, Repr

-- ============================================================================
-- S 3: Extraction Profile
-- ============================================================================

/-- A language's extraction morphology profile: what strategy it uses,
    which positions are marked, and whether the marking distinguishes
    between different extracted positions.

    Follows the `RelativizationProfile` pattern from
    `Phenomena/Relativization/Typology.lean`. -/
structure ExtractionProfile where
  /-- Language name -/
  language : String
  /-- Primary extraction-marking strategy -/
  strategy : ExtractionMarkingStrategy
  /-- Which extraction targets trigger overt marking.
      Empty for `none` strategy languages. -/
  markedPositions : List ExtractionTarget
  /-- Does the marking distinguish which position was extracted?
      E.g., Tagalog voice distinguishes subject/object/oblique;
      Mam =(y)a' marks only oblique. -/
  distinguishesPosition : Bool
  /-- Notes -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- S 4: Helpers
-- ============================================================================

/-- Does this profile mark extraction from a given position? -/
def ExtractionProfile.marks (p : ExtractionProfile) (t : ExtractionTarget) : Bool :=
  p.markedPositions.any (· == t)

/-- Does this profile use any overt extraction marking? -/
def ExtractionProfile.hasOvertMarking (p : ExtractionProfile) : Bool :=
  p.strategy != .none

end Interfaces
