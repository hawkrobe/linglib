
/-!
# Noun categorization devices
[aikhenvald-2000] [dixon-1982] [downing-1996] [allan-1977] [corbett-1991]

Theory-neutral cross-linguistic typology of noun-categorization devices, following
[aikhenvald-2000] *Classifiers: A Typology of Noun Categorization Devices*: the
device-type continuum (`ClassifierType`, with `nounClass` = gender at its agreement
pole), the semantic parameters classifiers employ, the per-classifier lexical
schema, and the per-language paradigm record. Graduated from the dissolved
`Typology/` drawer as a sibling of `Features/Gender`.

## Main definitions

* `ClassifierType` — [aikhenvald-2000]'s noun-categorization device types.
* `SemanticParameter`, `ShapeDimension` — the semantic axes ([allan-1977], [downing-1996]).
* `CategorizationScope`, `AssignmentPrinciple`, `SurfaceRealization`, `GrammaticalCategory`.
* `ClassifierEntry` — per-classifier lexical schema.
* `ClassifierStrategy` — competing composition frameworks (theory-laden; consumed by
  `Semantics/Classifier`, where the cross-paper disagreement is proved as theorems).
* `System` — Aikhenvald's per-language paradigm record (Bool property fields + `Prop` API).

## Implementation notes

The `nounClass` cell collapses what [corbett-1991] separates (target/controller
gender, gender vs. classifier); the per-language gender structure lives in
`Features/Gender`, and a noun-class `System`'s `inventorySize`/`hasAgreement` should
derive from a `Gender.System` rather than being stipulated (follow-on).
-/

namespace NounCategorization

-- ════════════════════════════════════════════════════
-- § 1. Classifier Types ([aikhenvald-2000])
-- ════════════════════════════════════════════════════

/-- The 9 focal classifier types on the noun-categorization continuum.

    [aikhenvald-2000] establishes these as "focal points" distinguished
    by morphosyntactic locus, scope, and grammatical function.
    Real systems are gradient — a language's system may sit between types.

    UNVERIFIED: The 9-type taxonomy is Aikhenvald's specific carve-up;
    other typologists (Allan 1977, Craig 1986, Grinevald 2000, Senft 2000)
    differ. The `nounClass` cell here is also more fine-grained per
    Corbett 1991 — see file docstring "Out of scope". -/
inductive ClassifierType where
  /-- Noun class / gender: closed agreement system, realized outside the noun
      on modifiers (head-modifier NP) or predicate (pred-arg agreement).
      Small inventory (2–20). Examples: Bantu, Indo-European gender. -/
  | nounClass
  /-- Noun classifier: independent of other NP elements, characterizes the
      noun itself. Free forms or affixes on the noun. -/
  | nounClassifier
  /-- Numeral classifier: appears in numeral/quantifier NPs, required for
      enumeration. Free forms or affixes on the numeral. -/
  | numeralClassifier
  /-- Relational classifier: in possessive NPs, characterizes the possessive
      relation (how the noun can be possessed/handled). -/
  | relationalClassifier
  /-- Possessed classifier: in possessive NPs, characterizes the possessed
      noun in terms of its inherent properties. -/
  | possessedClassifier
  /-- Possessor classifier: in possessive NPs, characterizes the possessor.
      Very rare. -/
  | possessorClassifier
  /-- Verbal classifier: marks agreement on the verb with an S or O argument.
      Incorporated classifiers, affixes, or suppletive verb stems. -/
  | verbalClassifier
  /-- Locative classifier: in adpositional NPs, marks agreement with the head
      noun in locative expressions. -/
  | locativeClassifier
  /-- Deictic classifier: appears on deictics, articles, demonstratives.
      Marks spatial location and/or determination. -/
  | deicticClassifier
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Semantic Parameters ([aikhenvald-2000])
-- ════════════════════════════════════════════════════

/-- Universal semantic parameters employed in noun categorization.

    [aikhenvald-2000] identifies three large classes: animacy,
    physical properties, and function. These parameters are found across
    ALL types of noun categorization device, though different types show
    different preferences. -/
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
  | socialStatus     -- honorific status of the referent (kin, age, social rank)
  | register         -- formality/register of the speech act (formal/written vs casual);
                     -- distinct from socialStatus, which tracks the referent's status.
                     -- Japanese 名 mei and Mandarin 位 wèi index register, not referent status.
  -- Perceptual (salient but unattested in noun categorization)
  | colour           -- perceptually salient but no attested classifier system uses it
  deriving DecidableEq, Repr

/-- Dimensionality sub-classification for shape-based classifiers.

    [downing-1996] and [allan-1977] show that shape-based
    classifiers decompose along a dimensionality axis:
    - 1D: long, slender, elongated (e.g., Japanese 本 hon, Mandarin 条 tiáo)
    - 2D: flat, thin, planar (e.g., Japanese 枚 mai, Mandarin 张 zhāng)
    - 3D: round, compact, globular (e.g., Japanese 個 ko) -/
inductive ShapeDimension where
  | oneD    -- long, slender (1-dimensional extent)
  | twoD    -- flat, thin (2-dimensional extent)
  | threeD  -- round, compact (3-dimensional extent)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. Structural Properties
-- ════════════════════════════════════════════════════

/-- Morphosyntactic scope of a classifier type. -/
inductive CategorizationScope where
  | headModifierNP     -- Inside a head-modifier NP (noun class agreement)
  | predicateArgument  -- Outside NP: clause-level pred-arg agreement
  | noun               -- The noun itself (noun classifiers)
  | numeralNP          -- Numeral/quantifier NP (numeral classifiers)
  | possessiveNP       -- Possessive NP (relational/possessed/possessor CL)
  | clause             -- Clause-level (verbal classifiers)
  | adpositionalNP     -- Adpositional NP (locative classifiers)
  | attributiveNP      -- Attributive NP (deictic classifiers)
  deriving DecidableEq, Repr

/-- Principles governing noun-to-class/classifier assignment. -/
inductive AssignmentPrinciple where
  /-- Purely semantic: class determined by referent meaning -/
  | semantic
  /-- Morphological: class determined by derivational affix, declension, etc. -/
  | morphological
  /-- Phonological: class determined by initial segment, final vowel, etc. -/
  | phonological
  /-- Mixed: semantic core + morphological/phonological overlay -/
  | mixed
  deriving DecidableEq, Repr

/-- Surface realization of a classifier morpheme. -/
inductive SurfaceRealization where
  | prefix | suffix | clitic | freeForm
  | suppletion | stress | reduplication
  | nounIncorporation | repeater
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 4. ClassifierEntry — per-classifier lexical entry
-- ════════════════════════════════════════════════════

/-- A classifier lexical entry with semantic typing.

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
  /-- Shape dimensionality sub-classification ([downing-1996]).
      Only meaningful when `semantics` includes `.shape`. -/
  shapeDimension : Option ShapeDimension := none
  deriving Repr, BEq

/-- Whether this classifier encodes a given semantic parameter. -/
def ClassifierEntry.encodes (c : ClassifierEntry) (p : SemanticParameter) : Bool :=
  c.semantics.any (· == p)

/-- Collect all distinct semantic parameters attested across a classifier inventory.
    Used to derive `preferredSemantics` from fragment data rather than hand-listing. -/
def collectSemantics (cls : List ClassifierEntry) : List SemanticParameter :=
  let all := cls.foldl (λ acc c => acc ++ c.semantics) []
  all.eraseDups

-- ════════════════════════════════════════════════════
-- § 5. Classifier Strategy ([little-moroney-royer-2022])
-- ════════════════════════════════════════════════════

/-- The semantic strategy a theoretical framework attributes to classifier
    constructions. Three competing positions are represented:

    - **forNumeral** (CLF-for-NUM): [krifka-1995], [bale-coon-2014],
      [little-moroney-royer-2022]. The classifier is a measure function
      required by the numeral. The numeral takes the classifier as its first
      argument: ⟦TWO⟧ = λm⟨e,n⟩λPλx.[P(x) ∧ m(x) = 2]. Predicts: numeral
      idiosyncrasies in CLF requirement, CLF obligatory even without a noun
      (counting contexts), CLF + plural marking can co-occur.
    - **forNoun** (CLF-for-N): [chierchia-1998], [jenks-2011],
      [nomoto-2013], [little-moroney-royer-2022]. The classifier
      atomizes the noun denotation so the numeral can count.
      ⟦CLF⟧ = λPλx.[P(x) ∧ ¬∃y[P(y) ∧ y < x]]. Predicts: noun idiosyncrasies
      in CLF requirement, CLF appears beyond numerals (with quantifiers,
      demonstratives, relative clauses), CLF + plural marking in complementary
      distribution.
    - **sudoBlocking**: [sudo-2016]. Classifier semantics live with
      *numerals*, not nouns. Numerals are universally type-n singular terms;
      a phonologically silent ∪-operator type-shifts them to predicates in
      languages without classifiers, but is *blocked* (per [chierchia-1998]'s
      Blocking Principle) in languages whose lexicon contains overt classifiers.
      Predicts: no numeral or noun idiosyncrasies, CLF appears *with* numerals
      not beyond them, CLF appears in counting contexts (via the ∩-operator).

    Strategy assignments to specific languages live in study files
    (`Studies/{NMP,LittleMoroneyRoyer2022,Sudo2016}.lean`),
    not in this file or in `System`. Each paper owns its
    own per-language commitments; cross-paper agreement and disagreement
    are first-class theorems in the study files. -/
inductive ClassifierStrategy where
  | forNumeral
  | forNoun
  | sudoBlocking
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 6. System — paradigm record
-- ════════════════════════════════════════════════════

/-- A noun categorization system in a language.

    Captures [aikhenvald-2000]'s 7 definitional properties (A–G):
    (A) morphosyntactic locus → `scopes`
    (B) scope/domain → `classifierType` + `scopes`
    (C) assignment principles → `assignment`
    (D) surface realization → `realizations`
    (E) agreement → `hasAgreement`
    (F) markedness → `hasUnmarkedDefault`
    (G) grammaticalization → `isObligatory`

    UNVERIFIED: A–G enumeration cited from memory. -/
structure System where
  /-- Language family (e.g., "Indo-European", "Sino-Tibetan", "Bantu"). -/
  family : String
  /-- Aikhenvald classifier type. -/
  classifierType : ClassifierType
  /-- Morphosyntactic scopes this system operates in (A, B). -/
  scopes : List CategorizationScope
  /-- How nouns are assigned to classes/classifiers (C). -/
  assignment : AssignmentPrinciple
  /-- Morphological realization types used (D). -/
  realizations : List SurfaceRealization
  /-- Does the system involve agreement? (E) — definitional for noun classes.
      Stored as `Bool` so the struct stays decidable as a whole; the
      user-facing predicate is `HasAgreement : Prop`. -/
  hasAgreement : Bool
  /-- Inventory size (number of classes or classifiers). -/
  inventorySize : Nat
  /-- Is realization obligatory or optional? (G). User-facing predicate:
      `IsObligatory : Prop`. -/
  isObligatory : Bool
  /-- Is there a formally/functionally unmarked default? (F). User-facing
      predicate: `HasUnmarkedDefault : Prop`. -/
  hasUnmarkedDefault : Bool := false
  /-- Preferred semantic parameters (Aikhenvald §11.2). -/
  preferredSemantics : List SemanticParameter := []
  /-- Does the language have obligatory grammatical number marking?
      User-facing predicate: `HasObligatoryNumber : Prop`. -/
  hasObligatoryNumber : Bool := false
  /-- Can classifiers and plural marking co-occur? Predicted by CLF-for-NUM
      ([little-moroney-royer-2022]: CLF and PL are in different
      projections) but not by CLF-for-N (same projection, complementary
      distribution per [borer-2005]). User-facing predicate:
      `PluralClfCooccur : Prop`. -/
  pluralClfCooccur : Bool := false
  /-- Citation backing the hand-coded values. -/
  source : String := ""
  deriving Repr, DecidableEq

namespace System

/-! ## Prop API for the boolean property fields

The struct's `hasAgreement`/`isObligatory`/`hasUnmarkedDefault`/
`hasObligatoryNumber`/`pluralClfCooccur` fields are stored as `Bool` so
the struct itself stays decidably equal. The user-facing predicates are
the `Prop` versions defined here, each with a `Decidable` instance via
the underlying `Bool`. Theorem statements should prefer the `Prop` form
(`s.HasAgreement` rather than `s.hasAgreement = true`); `decide` works
for either since the Bool projection reduces structurally for concrete
fragment values. -/

/-- The system involves agreement (E). -/
abbrev HasAgreement (s : System) : Prop := s.hasAgreement = true

/-- Realization is obligatory (G). -/
abbrev IsObligatory (s : System) : Prop := s.isObligatory = true

/-- The system has a formally/functionally unmarked default (F). -/
abbrev HasUnmarkedDefault (s : System) : Prop :=
  s.hasUnmarkedDefault = true

/-- The language has obligatory grammatical number marking. -/
abbrev HasObligatoryNumber (s : System) : Prop :=
  s.hasObligatoryNumber = true

/-- Classifiers and plural marking can co-occur. -/
abbrev PluralClfCooccur (s : System) : Prop :=
  s.pluralClfCooccur = true

/-- [dixon-1982]'s noun-class vs. classifier divide.
    Noun classes: small, closed, grammaticalized, agreement.
    Classifiers: large, open, lexical, no agreement. -/
def isNounClassType (t : ClassifierType) : Bool :=
  t == .nounClass

/-- All non-noun-class types are "classifier" types in the broad sense. -/
def isClassifierType (t : ClassifierType) : Bool :=
  !isNounClassType t

end System

-- ════════════════════════════════════════════════════
-- § 8. Grammatical-Category Interactions (Aikhenvald)
-- ════════════════════════════════════════════════════

/-- Grammatical categories that interact with classifier types
    ([aikhenvald-2000]). -/
inductive GrammaticalCategory where
  | definiteness | number | case_ | tenseAspect | possession
  deriving DecidableEq, Repr

/-- Whether a classifier type typically interacts with a grammatical category
    ([aikhenvald-2000]). -/
def interacts : ClassifierType → GrammaticalCategory → Bool
  | .nounClass, .definiteness => true
  | .nounClass, .number => true
  | .nounClass, .case_ => true
  | .nounClass, .tenseAspect => true
  | .nounClass, .possession => true
  | .numeralClassifier, .definiteness => true
  | .numeralClassifier, .number => true
  | .numeralClassifier, .possession => false
  | .numeralClassifier, .case_ => false
  | .numeralClassifier, .tenseAspect => false
  | .verbalClassifier, .tenseAspect => true
  | .verbalClassifier, .number => true
  | .relationalClassifier, .possession => true
  | .possessedClassifier, .possession => true
  | _, _ => false

end NounCategorization
