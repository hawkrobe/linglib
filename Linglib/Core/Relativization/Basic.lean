/-!
# Relativization: Basic Types

Theory-neutral types for cross-linguistic relativization data. These types
are used by language fragments to encode relative clause markers and their
distributional properties, and by phenomenon studies to verify typological
generalizations like the @cite{keenan-comrie-1977} Accessibility Hierarchy.

Mirrors `Core.Case.Basic` / `Core.Case.Hierarchy` for case inventories.
-/

namespace Core

-- ============================================================================
-- § 1: Grammatical Positions on the Accessibility Hierarchy
-- ============================================================================

/-- Grammatical positions on the @cite{keenan-comrie-1977} Accessibility
    Hierarchy (AH).

    The hierarchy ranks grammatical relations by their accessibility to
    relativization. Higher positions are more accessible: more languages
    can relativize them, and simpler strategies (gap) suffice.

    Subject > DirectObject > IndirectObject > Oblique > Genitive > ObjComparison -/
inductive AHPosition where
  /-- Subject: the most accessible position. Virtually all languages
      with relative clauses can relativize subjects. -/
  | subject
  /-- Direct object: the second most accessible position. -/
  | directObject
  /-- Indirect object: third position. -/
  | indirectObject
  /-- Oblique: fourth position (instrumentals, locatives, etc.). -/
  | oblique
  /-- Genitive: fifth position (possessors). -/
  | genitive
  /-- Object of comparison: the least accessible position
      ("the person [that I am taller than _]"). -/
  | objComparison
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Relative Clause Position
-- ============================================================================

/-- Position of the relative clause with respect to the head noun.

    Post-nominal is the dominant type cross-linguistically; pre-nominal
    correlates with OV word order; internally-headed and correlative
    (double-headed) types are rare but typologically significant. -/
inductive RCPosition where
  /-- Post-nominal: RC follows the head noun. E.g., English "the man
      [who left]", Arabic "ar-rajul [alladhi ghadara]". -/
  | postNominal
  /-- Pre-nominal: RC precedes the head noun. E.g., Japanese
      "[ _ kaetta] hito", Korean "[ _ tteonagan] saram". -/
  | preNominal
  /-- Internally-headed: the head noun appears inside the RC. E.g.,
      Bambara. -/
  | internallyHeaded
  /-- Correlative (double-headed): the head noun appears both inside
      and outside the RC. E.g., Hindi-Urdu "jo aadmii aayaa, vo
      aadmii meraa bhaaii hai". -/
  | correlative
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 3: NP_rel Type (what occupies the relativized position)
-- ============================================================================

/-- What occupies the relativized position (NP_rel) inside the RC.

    This is the core of @cite{keenan-comrie-1977}'s ±case distinction:
    -case strategies delete NP_rel (gap), while +case strategies retain
    a pronominal element that bears case marking. -/
inductive NPRelType where
  /-- Gap: NP_rel is deleted; no overt element at the extraction site.
      The "lightest" strategy. E.g., English "the man [that _ left]". -/
  | gap
  /-- Resumptive pronoun: NP_rel is a personal pronoun (usually
      bearing case). E.g., Arabic "al-madina [illi saafartu ila-ha]"
      'the-city [that I-traveled to-it]'. -/
  | resumptive
  /-- Relative pronoun: NP_rel is a dedicated relative pronoun that
      typically fronts to clause-initial position and bears case.
      E.g., English "the man [who left]", German "der Mann [der ging]". -/
  | relPronoun
  /-- Non-reduction: NP_rel is a full NP — the head noun is repeated
      inside the RC. E.g., Bambara. -/
  | nonReduction
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 4: Relative Clause Marker
-- ============================================================================

/-- A relative clause marker or construction in a language.

    Each marker introduces one type of relative clause with specific
    distributional properties. Fragments encode the actual linguistic
    objects — particles, pronouns, verbal suffixes — rather than
    typological strategy labels. The strategy classification is derived
    from marker properties in study files.

    Examples:
    - Welsh particle *a* (gap, -case, covers SU/DO)
    - Finnish relative pronoun *joka* (+case, covers SU–GEN)
    - Korean adnominal suffix *-(n)ɨn* (gap, -case, covers SU–OBL) -/
structure RelClauseMarker where
  /-- Surface form of the marker (e.g., "a", "joka", "that/∅", "-(n)ɨn"). -/
  form : String
  /-- What occupies the relativized position in this construction. -/
  npRel : NPRelType
  /-- Whether the relative element bears case marking (±case). -/
  bearsCaseMarking : Bool
  /-- Position of the RC with respect to the head noun. -/
  rcPosition : RCPosition
  /-- Which grammatical positions can be relativized using this marker. -/
  positions : List AHPosition
  /-- Additional notes. -/
  notes : String := ""
  deriving BEq, Repr

/-- Does this marker cover a given AH position? -/
def RelClauseMarker.covers (m : RelClauseMarker) (p : AHPosition) : Bool :=
  m.positions.any (· == p)

end Core
