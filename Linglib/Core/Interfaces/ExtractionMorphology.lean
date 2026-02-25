import Linglib.Core.Lexical.Word

/-!
# Extraction Morphology Interface

Theory-neutral interface for cross-linguistic extraction morphology —
how languages morphologically mark that a constituent has undergone
Ā-movement (wh-movement, relativization, focus fronting, etc.).

Languages vary dramatically in whether and how they track extraction:
- English: no overt marking (gap strategy)
- Austronesian (Tagalog, Malagasy): voice alternation marks which argument
  has been extracted
- Mayan (Mam, K'iche'): dedicated morphemes on verbal complex
  (Mam =(y)a', K'iche' *wi*)
- Celtic (Irish): complementizer changes form (*aL* vs. *aN*)
- Chamorro: agreement morphology tracks extracted position

This interface parametrizes these strategies without committing to a
particular syntactic theory of how extraction works.

## References

- Elkins, N., Y. Imanishi & J. Coon (2026). Wh-movement and oblique
  extraction in SJO Mam.
- Erlewine, M. Y. (2018). Extraction and licensing in Toba Batak.
  Language 94(3): 662–697.
- McCloskey, J. (2002). Resumption, successive cyclicity, and the
  locality of operations. In S. D. Epstein & T. D. Seely (eds.),
  Derivation and Explanation in the Minimalist Program.
-/

namespace Interfaces

-- ============================================================================
-- § 1: Extraction Marking Strategy
-- ============================================================================

/-- How a language morphologically marks extraction (Ā-movement).

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
      E.g., Mam =(y)a' on Voice⁰/Dir⁰, K'iche' *wi*, Irish complementizer *aL*. -/
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
      structural. E.g., Toba Batak (Erlewine 2018). -/
  | structuralRestriction
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Extraction Target
-- ============================================================================

/-- The grammatical position from which extraction occurs.

    This intersects with the Keenan-Comrie Accessibility Hierarchy (see
    `FillerGap/Typology.lean`), but is defined independently because
    extraction morphology may make finer distinctions than relativization. -/
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
  deriving DecidableEq, BEq, Repr

/-- The thematic category of an argument being extracted: agent
    (external argument), patient (internal argument), or oblique.

    Coarser than `ThetaRole` (which distinguishes agent/experiencer/
    causer, patient/theme, goal/source/instrument). Used when the
    relevant distinction is which macro-role is extracted, not fine-
    grained thematic relations or structural positions.

    Complements `ExtractionTarget` (structural position): ArgumentRole
    identifies *what* is extracted; ExtractionTarget identifies *where*
    it was extracted from. The two coincide in simple active clauses
    (agent = subject, patient = object) but diverge under voice
    alternation (in OV, the patient becomes the subject). -/
inductive ArgumentRole where
  | agent    -- external argument (agent, experiencer, causer)
  | patient  -- internal argument (patient, theme)
  | oblique  -- oblique argument (instrument, goal, source, etc.)
  deriving DecidableEq, BEq, Repr

/-- Default structural position for a given argument role (active voice). -/
def ArgumentRole.defaultPosition : ArgumentRole → ExtractionTarget
  | .agent => .subject
  | .patient => .directObject
  | .oblique => .oblique

-- ============================================================================
-- § 3: Extraction Profile
-- ============================================================================

/-- A language's extraction morphology profile: what strategy it uses,
    which positions are marked, and whether the marking distinguishes
    between different extracted positions.

    Follows the `RelativizationProfile` pattern from FillerGap/Typology.lean. -/
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
-- § 4: Helpers
-- ============================================================================

/-- Does this profile mark extraction from a given position? -/
def ExtractionProfile.marks (p : ExtractionProfile) (t : ExtractionTarget) : Bool :=
  p.markedPositions.any (· == t)

/-- Does this profile use any overt extraction marking? -/
def ExtractionProfile.hasOvertMarking (p : ExtractionProfile) : Bool :=
  p.strategy != .none

end Interfaces
