/-!
# Noun Categorization Typology

Cross-linguistic typology of noun categorization devices, following
Aikhenvald (2000) "Classifiers: A Typology of Noun Categorization Devices."

Defines the parameter space for classifying noun categorization systems:
classifier types, semantic parameters, structural properties, and a
common `ClassifierEntry` type for individual classifier lexical entries.

## Organization

- **§1 Classifier types**: The 9-type typology (Table 15.1)
- **§2 Semantic parameters**: What classifiers encode (§11.1.1)
- **§3 Structural properties**: Assignment, realization, scope
- **§4 ClassifierEntry**: Per-classifier lexical entry with semantic typing
- **§5 NounCategorizationSystem**: Per-language system description

## References

- Aikhenvald, A. Y. (2000). Classifiers: A Typology of Noun Categorization Devices.
- Dixon, R. M. W. (1982). Where Have All the Adjectives Gone?
- Chierchia, G. (1998). Reference to Kinds Across Languages.
-/

namespace Core.NounCategorization

-- ============================================================================
-- §1 Classifier Types (Aikhenvald 2000 Table 15.1)
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
-- §2 Semantic Parameters (Aikhenvald 2000 §11.1.1)
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

-- ============================================================================
-- §5 NounCategorizationSystem: per-language system description
-- ============================================================================

/-- A noun categorization system in a language.

    Captures Aikhenvald's 7 definitional properties (A–G from §1.5):
    (A) morphosyntactic locus → `scopes`
    (B) scope/domain → `classifierType` + `scopes`
    (C) assignment principles → `assignment`
    (D) surface realization → `realizations`
    (E) agreement → `hasAgreement`
    (F) markedness → `hasUnmarkedDefault`
    (G) grammaticalization → `isObligatory` -/
structure NounCategorizationSystem where
  /-- Language name -/
  language : String
  /-- Language family -/
  family : String
  /-- Aikhenvald classifier type -/
  classifierType : ClassifierType
  /-- Morphosyntactic scopes this system operates in (A, B) -/
  scopes : List CategorizationScope
  /-- How nouns are assigned to classes/classifiers (C) -/
  assignment : AssignmentPrinciple
  /-- Morphological realization types used (D) -/
  realizations : List SurfaceRealization
  /-- Does the system involve agreement? (E) — definitional for noun classes -/
  hasAgreement : Bool
  /-- Inventory size (number of classes or classifiers) -/
  inventorySize : Nat
  /-- Is realization obligatory or optional? (G) -/
  isObligatory : Bool
  /-- Is there a formally/functionally unmarked default? (F) -/
  hasUnmarkedDefault : Bool := false
  /-- Preferred semantic parameters (§11.2, Table 11.13) -/
  preferredSemantics : List SemanticParameter := []
  /-- Citation -/
  source : String := ""
  deriving Repr

-- ============================================================================
-- §6 Key Distinctions
-- ============================================================================

/-- Dixon's (1982) noun-class vs. classifier divide (Table 1.2).
    Noun classes: small, closed, grammaticalized, agreement.
    Classifiers: large, open, lexical, no agreement. -/
def isNounClassType (t : ClassifierType) : Bool :=
  t == .nounClass

/-- All non-noun-class types are "classifier" types in the broad sense. -/
def isClassifierType (t : ClassifierType) : Bool :=
  !isNounClassType t

end Core.NounCategorization
