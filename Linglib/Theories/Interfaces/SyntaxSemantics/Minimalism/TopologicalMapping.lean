import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Theories.Semantics.Reference.Kripke

/-!
# The Topological Mapping Theory
@cite{longobardi-2005} @cite{longobardi-1994}

@cite{longobardi-2005} §9: a mapping theory from nominal syntactic forms to
logically oriented representations. The theory rests on two axioms and a
licensing condition, from which the Core Generalization — reference (to
individuals) iff N-to-D — follows as a theorem.

## Axioms

- **(52) Denotation Hypothesis**: Individuals are denoted in D.
- **(53) Licensing Condition**: Arguments denote individuals.
- **(54) Constants vs Variables**: A referential value is constant if a
  lexically referential expression occupies (or chains to) D; otherwise
  the argument is a variable bound by an operator.

## Derived Theorems

- **(55)** Arguments with empty D are variables.
- **(56)** An argument is a constant only if D contains a lexically
  referential expression.
- **(33) Core Generalization**: Reference (to individuals) iff N-to-D.

## Noun Taxonomy

Four classes of nominal heads, ranked by three diagnostic tests:
object-referentiality, predicative restrictions, and kind-referentiality.
-/

namespace Minimalism.TopologicalMapping

-- ============================================================================
-- § 1: Nominal Head Classification — Table (28)
-- ============================================================================

/-- The four classes of nominal heads, ranked from most prototypically
    referential (pronouns) to least (common nouns).

    @cite{longobardi-2005} table (28): these four classes are distinguished
    by three tests — object-referentiality (in D), predicative restrictions
    (not in D), and kind-referentiality (with definite article). -/
inductive NominalHeadClass where
  /-- Always in D in all argument environments. Object-referential only.
      Cannot function predicatively or as kind-denoting expressions. -/
  | pronoun
  /-- Raise to D obligatorily in argument function (Romance).
      Object-referential. Predicative use conditioned. No kind reading. -/
  | properName
  /-- Raise to D only under special conditions (genitive modifier,
      deictic context). Object-referential when raised. Full predicative
      use. Kind-referential with definite article. Examples: *casa*
      'home', *mamma* 'mom', *lunedì* 'Monday'. -/
  | specialCommon
  /-- Never raise to D. Never object-referential. Full predicative use.
      Kind-referential with definite article. -/
  | commonNoun
  deriving DecidableEq, Repr

/-- Object-referential: the nominal can denote a specific object
    (individual in Carlson's sense) by occupying the D position. -/
def objectReferential : NominalHeadClass → Bool
  | .pronoun      => true
  | .properName   => true
  | .specialCommon => true   -- conditioned: only when raised to D
  | .commonNoun   => false

/-- Can function as a predicate (i.e., survive without D). -/
def canBePredicate : NominalHeadClass → Bool
  | .pronoun      => false
  | .properName   => true   -- conditioned: only under marked circumstances
  | .specialCommon => true
  | .commonNoun   => true

/-- Kind-referential: can denote a kind when introduced by definite article. -/
def kindReferential : NominalHeadClass → Bool
  | .pronoun      => false
  | .properName   => false
  | .specialCommon => true
  | .commonNoun   => true

/-- Whether N-to-D raising is obligatory in argument position. -/
def raisingObligatory : NominalHeadClass → Bool
  | .pronoun      => true   -- always in D (base-generated)
  | .properName   => true   -- obligatory raising in argument function
  | .specialCommon => false  -- conditioned raising
  | .commonNoun   => false  -- never raises

/-- Table (28): the three diagnostics partition the four classes.
    Pronouns and proper names are object-referential but not kind-referential.
    Special common nouns and common nouns are kind-referential but differ
    in object-referentiality. -/
theorem table_28 :
    -- Object-referential partition
    objectReferential .pronoun = true ∧
    objectReferential .properName = true ∧
    objectReferential .specialCommon = true ∧
    objectReferential .commonNoun = false ∧
    -- Kind-referential partition
    kindReferential .pronoun = false ∧
    kindReferential .properName = false ∧
    kindReferential .specialCommon = true ∧
    kindReferential .commonNoun = true ∧
    -- Predicative partition
    canBePredicate .pronoun = false ∧
    canBePredicate .properName = true ∧
    canBePredicate .specialCommon = true ∧
    canBePredicate .commonNoun = true := by decide

-- ============================================================================
-- § 2: The Properness Hierarchy — (25)
-- ============================================================================

/-- The scalar hierarchy of properness from @cite{longobardi-2005} (25).

    Nominal expressions are ranked along a scale from most prototypically
    proper-like to most common-like. Access to the N-to-D derivational
    strategy decreases monotonically along this scale.

    a. Pronouns: always in D.
    b. Names of persons, geographical units: raise whenever D is empty.
    c. Names of days: raise only under particular semantic conditions.
    d. Casa, kinship terms: raise only if followed by genitive modifier.
    e. Normal common nouns: never raise. -/
def propernessRank : NominalHeadClass → Nat
  | .pronoun       => 0  -- most proper-like
  | .properName    => 1
  | .specialCommon => 2
  | .commonNoun    => 3  -- least proper-like

/-- Raising access decreases monotonically with properness rank:
    if class c₁ is more proper than c₂, then c₁'s raising is at least
    as obligatory as c₂'s. -/
theorem raising_monotone :
    ∀ c₁ c₂ : NominalHeadClass,
      propernessRank c₁ ≤ propernessRank c₂ →
        (raisingObligatory c₂ = true → raisingObligatory c₁ = true) := by
  intro c₁ c₂ h₁ h₂
  cases c₁ <;> cases c₂ <;> simp_all [propernessRank, raisingObligatory]

-- ============================================================================
-- § 3: The Topological Mapping Theory — Axioms (52)–(54)
-- ============================================================================

/-- The lexical type of a noun: whether it names objects or kinds.

    @cite{longobardi-2005} §4: nouns lexically divide into object-naming
    (proper names, pronouns — intrinsically referential) and kind-naming
    (common nouns — denote kinds, not individuals). -/
inductive LexicalNamingType where
  /-- Object-naming: learning the name means learning to apply it to a
      particular object. Proper names, pronouns. -/
  | objectNaming
  /-- Kind-naming: learning the name means learning to recognize a
      potentially open set of objects. Common nouns. -/
  | kindNaming
  deriving DecidableEq, Repr

/-- A nominal argument configuration, capturing the syntactic and semantic
    state of a DP in argument position. -/
structure NominalConfig where
  /-- The head noun's lexical naming type -/
  namingType : LexicalNamingType
  /-- Does D contain a lexically referential expression?
      (either an overt determiner/quantifier, or N raised to D,
      or an expletive article linked to a raised N in a CHAIN) -/
  dHasReferentialContent : Bool
  /-- Is the nominal in argument function? -/
  isArgument : Bool
  deriving DecidableEq, Repr

/-- **(52) Denotation Hypothesis**: Individuals are denoted in D.

    The D position is the locus of referential interpretation.
    A nominal denotes an individual (object or kind) iff its D position
    is associated with referential content. -/
def denotesIndividual (nc : NominalConfig) : Bool :=
  nc.dHasReferentialContent

/-- **(53) Licensing Condition**: Arguments denote individuals.

    Full Interpretation requires arguments to have a referential value
    (whether constant or variable). -/
def argumentLicensed (nc : NominalConfig) : Bool :=
  !nc.isArgument || denotesIndividual nc

/-- **(54a)** A constant: a fixed referential value denoting one and only
    one entity (kind or object). Requires D to contain (or CHAIN-link to)
    a lexically referential expression — either a raised N, an overt
    determiner, or a pronoun base-generated in D. -/
def isConstant (nc : NominalConfig) : Bool :=
  nc.dHasReferentialContent

/-- **(54b)** A variable: bound by an operator (existential, generic,
    or the variable-binding force of a lexical determiner) and ranging
    over a set of entities. Arises when D is empty (no referential content). -/
def isVariable (nc : NominalConfig) : Bool :=
  !nc.dHasReferentialContent

-- ============================================================================
-- § 4: Derived Theorems (55)–(56) and Core Generalization (33)
-- ============================================================================

/-- **(55)** Arguments with empty D are variables.

    From (52)+(53)+(54): if D is empty, then by (52) the nominal cannot
    denote an individual via D. By (53) it must still denote (being an
    argument). By (54b) the only remaining option is variable interpretation. -/
theorem empty_d_arguments_are_variables (nc : NominalConfig)
    (_hArg : nc.isArgument = true)
    (hEmptyD : nc.dHasReferentialContent = false) :
    isVariable nc = true := by
  simp [isVariable, hEmptyD]

/-- **(56)** An argument is a constant only if D contains a lexically
    referential expression.

    Equivalently: constant interpretation requires N-to-D (for proper names),
    an overt determiner, or a pronoun in D. -/
theorem constant_requires_d_content (nc : NominalConfig)
    (hConst : isConstant nc = true) :
    nc.dHasReferentialContent = true := hConst

/-- **(33) The Core Generalization**: Reference (to individuals) iff N-to-D.

    This is the paper's central result, unifying object reference and kind
    reference. A nominal refers to an individual (constant interpretation)
    if and only if D has referential content (achieved by N-to-D raising
    for proper names, by an overt determiner for common nouns, or by
    base-generation for pronouns). -/
theorem core_generalization (nc : NominalConfig) :
    isConstant nc = true ↔ nc.dHasReferentialContent = true :=
  ⟨constant_requires_d_content nc, id⟩

/-- **(41)** A nominal is an argument only if introduced by D.

    @cite{longobardi-2005} §7: this principle, from @cite{szabolcsi-1987}
    and @cite{stowell-1989-1991}, is derived from (52)+(53). In non-argument
    environments (predicates, vocatives, exclamations), nominals can occur
    without D. -/
theorem argument_requires_d (nc : NominalConfig)
    (hArg : nc.isArgument = true)
    (hLicensed : argumentLicensed nc = true) :
    denotesIndividual nc = true := by
  simp only [argumentLicensed, Bool.or_eq_true_iff] at hLicensed
  rcases hLicensed with h | h
  · simp [hArg] at h
  · exact h

-- ============================================================================
-- § 5: Why Proper Names Must Raise / Common Nouns Cannot
-- ============================================================================

/-- @cite{longobardi-2005} §10, question (57c): Why must proper names raise?

    Object-naming nouns cannot satisfy (54b) — they name objects, not kinds,
    so they cannot enter the interpretive formula Dx.x ∈ kind(N) that gives
    variables their meaning. Their only route to argumenthood is constant
    interpretation via (54a), which requires D content. Since proper names
    are bare (no overt determiner), they must raise N-to-D to fill D. -/
theorem proper_names_must_raise :
    ∀ nc : NominalConfig,
      nc.namingType = .objectNaming →
      nc.isArgument = true →
      argumentLicensed nc = true →
      nc.dHasReferentialContent = true := by
  intro nc _ hArg hLic
  exact argument_requires_d nc hArg hLic

/-- @cite{longobardi-2005} §10, question (57a): Why do common nouns not
    have to raise?

    Kind-naming nouns can satisfy (54b): they name kinds, so they can
    enter the formula Dx.x ∈ kind(N) as the restrictor of a variable.
    Empty D yields a variable bound by an existential or generic operator.
    No raising is needed for convergence. -/
theorem common_nouns_need_not_raise :
    ∀ nc : NominalConfig,
      nc.namingType = .kindNaming →
      nc.isArgument = true →
      nc.dHasReferentialContent = false →
      isVariable nc = true := by
  intro nc _ hArg hEmptyD
  exact empty_d_arguments_are_variables nc hArg hEmptyD

-- ============================================================================
-- § 6: Expletive Articles
-- ============================================================================

/-- Whether a definite article is expletive (semantically vacuous placeholder)
    or a genuine semantic operator.

    @cite{longobardi-2005} §8: when a proper name appears with a definite
    article (*la Maria*, *il Gianni*), the article is expletive — it does
    not contribute uniqueness or familiarity semantics. It merely fills the
    D position that N-raising would otherwise occupy. -/
inductive ArticleType where
  /-- Expletive: phonological placeholder for D, no semantic content.
      Forms a CHAIN with the noun. *la Maria* ≈ *Maria* raised to D. -/
  | expletive
  /-- Semantic operator: contributes uniqueness (ι), familiarity, or
      quantificational force. *il tavolo* 'the table' — real definite. -/
  | operator
  deriving DecidableEq, Repr

/-- An expletive article does not induce kind readings.

    @cite{longobardi-2005} (46)–(47): *la Maria* behaves identically to
    bare *Maria* — wide scope, rigid, no generic/kind reading. This
    distinguishes expletive articles from genuine definite operators,
    which CAN induce kind readings (*i cani* 'the dogs' = the dog-kind). -/
def expletiveBlocksKindReading : ArticleType → Bool
  | .expletive => true   -- no kind reading: article is semantically vacuous
  | .operator  => false  -- kind reading possible: article is a real operator

-- ============================================================================
-- § 7: Bridge to Reference/Basic.lean — Proper Names
-- ============================================================================

open Semantics.Reference.Basic (properName isDirectlyReferential
  constantCharacter)

/-- Proper names in D are directly referential.

    Bridge connecting the syntactic analysis (N-to-D raising creates
    constant interpretation) to the semantic analysis (proper names
    have constant character and rigid content). The two perspectives
    converge: syntactically, D is the locus of reference; semantically,
    proper names are rigid designators. -/
theorem proper_name_in_d_is_constant
    {C W E : Type*} (e : E) :
    isDirectlyReferential (properName (C := C) (W := W) e).character ∧
    constantCharacter (properName (C := C) (W := W) e).character :=
  ⟨Semantics.Reference.Basic.properName_isDirectlyReferential e,
   Semantics.Reference.Basic.properName_constantCharacter e⟩

end Minimalism.TopologicalMapping
