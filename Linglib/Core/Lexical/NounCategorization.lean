/-!
# Noun Categorization Typology
@cite{aikhenvald-2000} @cite{chierchia-1998} @cite{dixon-1982}

Cross-linguistic typology of noun categorization devices, following
@cite{aikhenvald-2000} "Classifiers: A Typology of Noun Categorization Devices."

Defines the vocabulary types for describing noun categorization systems:
classifier types, semantic parameters, structural properties, and a
common `ClassifierEntry` type for individual classifier lexical entries.

Per-language system descriptions (`NounCategorizationSystem`) and the
Dixon noun-class vs. classifier divide live in
`Theories.Typology.NounCategorization` — they represent a specific
typological framework, not framework-agnostic infrastructure.

## Organization

- **§1 Classifier types**: The 9-type typology (Table 15.1)
- **§2 Semantic parameters**: What classifiers encode (§11.1.1)
- **§3 Structural properties**: Assignment, realization, scope
- **§4 ClassifierEntry**: Per-classifier lexical entry with semantic typing

-/

namespace Core.NounCategorization

-- ============================================================================
-- §1 Classifier Types (@cite{aikhenvald-2000} Table 15.1)
-- ============================================================================

/-- The 9 focal classifier types on the noun-categorization continuum.

    Aikhenvald (2000 §1.5, Table 15.1) establishes these as "focal points"
    distinguished by morphosyntactic locus, scope, and grammatical function.
    Real systems are gradient — a language's system may sit between types. -/
inductive ClassifierType where
  /-- Noun class / gender: closed agreement system, realized outside the noun
      on modifiers (head-modifier NP) or predicate (pred-arg agreement).
      Small inventory (2–20). Examples: Bantu, Indo-European gender. (Ch 2) -/
  | nounClass
  /-- Noun classifier: independent of other NP elements, characterizes the
      noun itself. Free forms or affixes on the noun. (Ch 3) -/
  | nounClassifier
  /-- Numeral classifier: appears in numeral/quantifier NPs, required for
      enumeration. Free forms or affixes on the numeral. (Ch 4) -/
  | numeralClassifier
  /-- Relational classifier: in possessive NPs, characterizes the possessive
      relation (how the noun can be possessed/handled). (Ch 5) -/
  | relationalClassifier
  /-- Possessed classifier: in possessive NPs, characterizes the possessed
      noun in terms of its inherent properties. (Ch 5) -/
  | possessedClassifier
  /-- Possessor classifier: in possessive NPs, characterizes the possessor.
      Very rare. (Ch 5) -/
  | possessorClassifier
  /-- Verbal classifier: marks agreement on the verb with an S or O argument.
      Incorporated classifiers, affixes, or suppletive verb stems. (Ch 6) -/
  | verbalClassifier
  /-- Locative classifier: in adpositional NPs, marks agreement with the head
      noun in locative expressions. (Ch 7) -/
  | locativeClassifier
  /-- Deictic classifier: appears on deictics, articles, demonstratives.
      Marks spatial location and/or determination. (Ch 7) -/
  | deicticClassifier
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- §2 Semantic Parameters (@cite{aikhenvald-2000} §11.1.1)
-- ============================================================================

/-- Universal semantic parameters employed in noun categorization.

    Aikhenvald (2000 §11.1.1) identifies three large classes: animacy,
    physical properties, and function. These parameters are found across
    ALL types of noun categorization device, though different types show
    different preferences (Table 11.13). -/
inductive SemanticParameter where
  -- (A) Animacy hierarchy — near-universal, the semantic "core"
  | animacy          -- animate vs. inanimate
  | humanness        -- human vs. non-human
  | sex              -- male vs. female
  -- (B–G) Physical properties
  | shape            -- dimensionality + shape (1D/2D/3D, round/flat/long)
  | size             -- large vs. small
  | consistency      -- rigid vs. flexible
  | material         -- wooden, metal, etc.
  | boundedness      -- bounded (ring) vs. unbounded (plain)
  -- (H) Functional properties
  | function         -- how the object is used/handled
  | arrangement      -- configuration (coil, cluster, row)
  | quanta           -- quantity/measure
  -- Social
  | socialStatus     -- honorific, kin, age
  -- Perceptual (salient but unattested in noun categorization)
  | colour           -- perceptually salient but no attested classifier system uses it
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- §2b Shape Dimensionality (@cite{downing-1996} Ch. 5; @cite{allan-1977})
-- ============================================================================

/-- Dimensionality sub-classification for shape-based classifiers.

    @cite{downing-1996} Ch. 5 and @cite{allan-1977} show that shape-based
    classifiers decompose along a dimensionality axis:
    - 1D: long, slender, elongated (e.g., Japanese 本 hon, Mandarin 条 tiáo)
    - 2D: flat, thin, planar (e.g., Japanese 枚 mai, Mandarin 张 zhāng)
    - 3D: round, compact, globular (e.g., Japanese 個 ko) -/
inductive ShapeDimension where
  | oneD    -- long, slender (1-dimensional extent)
  | twoD    -- flat, thin (2-dimensional extent)
  | threeD  -- round, compact (3-dimensional extent)
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- §3 Structural Properties
-- ============================================================================

/-- Morphosyntactic scope of a classifier type (Table 15.1, column 2). -/
inductive CategorizationScope where
  | headModifierNP     -- Inside a head-modifier NP (noun class agreement)
  | predicateArgument  -- Outside NP: clause-level pred-arg agreement
  | noun               -- The noun itself (noun classifiers)
  | numeralNP          -- Numeral/quantifier NP (numeral classifiers)
  | possessiveNP       -- Possessive NP (relational/possessed/possessor CL)
  | clause             -- Clause-level (verbal classifiers)
  | adpositionalNP     -- Adpositional NP (locative classifiers)
  | attributiveNP      -- Attributive NP (deictic classifiers)
  deriving DecidableEq, Repr, BEq

/-- Principles governing noun-to-class/classifier assignment (§2.3). -/
inductive AssignmentPrinciple where
  /-- Purely semantic: class determined by referent meaning -/
  | semantic
  /-- Morphological: class determined by derivational affix, declension, etc. -/
  | morphological
  /-- Phonological: class determined by initial segment, final vowel, etc. -/
  | phonological
  /-- Mixed: semantic core + morphological/phonological overlay -/
  | mixed
  deriving DecidableEq, Repr, BEq

/-- Surface realization of a classifier morpheme (Table 15.3). -/
inductive SurfaceRealization where
  | prefix | suffix | clitic | freeForm
  | suppletion | stress | reduplication
  | nounIncorporation | repeater
  deriving DecidableEq, Repr, BEq

-- ============================================================================
-- §4 ClassifierEntry: individual classifier lexical entry
-- ============================================================================

/-- A classifier lexical entry with semantic typing.

    Replaces the unstructured `Option String` representation.
    Each classifier carries its form, a gloss, and the semantic parameters
    that motivate its selection — making it possible to verify Aikhenvald's
    claims about which parameters different classifier types encode. -/
structure ClassifierEntry where
  /-- Surface form (e.g. "只", "匹", "本") -/
  form : String
  /-- Gloss (e.g. "small.animal", "flat.bound.object") -/
  gloss : String := ""
  /-- Semantic parameters motivating selection of this classifier -/
  semantics : List SemanticParameter := []
  /-- Is this the "general" or "default" classifier? (个 in Mandarin, つ in Japanese) -/
  isDefault : Bool := false
  /-- Sortal (inherent properties) vs. mensural (configuration/measure) -/
  isMensural : Bool := false
  /-- Shape dimensionality sub-classification (@cite{downing-1996} Ch. 5).
      Only meaningful when `semantics` includes `.shape`. -/
  shapeDimension : Option ShapeDimension := none
  deriving Repr, BEq

/-- Whether this classifier encodes a given semantic parameter. -/
def ClassifierEntry.encodes (c : ClassifierEntry) (p : SemanticParameter) : Bool :=
  c.semantics.any (· == p)

/-- The form string of a classifier entry (for backward compatibility). -/
def ClassifierEntry.toString (c : ClassifierEntry) : String := c.form

instance : ToString ClassifierEntry where
  toString := ClassifierEntry.toString

/-- Collect all distinct semantic parameters attested across a classifier inventory.
    Used to derive `preferredSemantics` from fragment data rather than hand-listing. -/
def collectSemantics (cls : List ClassifierEntry) : List SemanticParameter :=
  let all := cls.foldl (λ acc c => acc ++ c.semantics) []
  all.eraseDups

end Core.NounCategorization
