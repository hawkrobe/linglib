import Linglib.Semantics.Reference.Basic
import Linglib.Semantics.Reference.Kripke
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Syntax.Minimalist.Economy
import Linglib.Studies.Longobardi2001

/-!
# Longobardi (2005): Toward a Unified Grammar of Reference
@cite{longobardi-2005} @cite{longobardi-1994}

Zeitschrift für Sprachwissenschaft 24(1): 5–44.

## Core Contribution

A syntax–semantics mapping theory reducing reference to nominal head
position: a nominal refers to an individual (constant) iff its D
position contains referential content. This unifies object reference
and kind reference under a single structural generalization.

The paper rests on two axioms and a licensing condition, from which the
**Core Generalization** — reference (to individuals) iff N-to-D —
follows as a theorem.

## Axioms

- **(52) Denotation Hypothesis**: individuals are denoted in D.
- **(53) Licensing Condition**: arguments denote individuals.
- **(54) Constants vs Variables**: a referential value is constant if a
  lexically referential expression occupies (or chains to) D; otherwise
  the argument is a variable bound by an operator.

## Derived Theorems

- **(55)** arguments with empty D are variables.
- **(56)** an argument is a constant only if D contains a lexically
  referential expression.
- **(33) Core Generalization**: reference (to individuals) iff N-to-D.

## File Structure

§1–§4 formalize the axioms, derived theorems, and noun taxonomy.
§5–§7 formalize the Last Resort consequences and the bridge to the
character semantics of `Reference/Basic`. §8–§13 instantiate the
theory: N-to-D raising as head movement, Italian *solo* diagnostic,
expletive articles, and the bridge to @cite{longobardi-2001}'s
`DPParameter`/`ArgumentType`.
-/

namespace Longobardi2005

open Longobardi2001 (DPParameter ArgumentType
  romance english greek pnRequiresOvertD bnCanBeReferential)

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
def ObjectReferential : NominalHeadClass → Prop
  | .pronoun       => True
  | .properName    => True
  | .specialCommon => True   -- conditioned: only when raised to D
  | .commonNoun    => False

instance : DecidablePred ObjectReferential := fun c => by
  cases c <;> unfold ObjectReferential <;> infer_instance

/-- Can function as a predicate (i.e., survive without D). -/
def CanBePredicate : NominalHeadClass → Prop
  | .pronoun       => False
  | .properName    => True   -- conditioned: only under marked circumstances
  | .specialCommon => True
  | .commonNoun    => True

instance : DecidablePred CanBePredicate := fun c => by
  cases c <;> unfold CanBePredicate <;> infer_instance

/-- Kind-referential: can denote a kind when introduced by definite article. -/
def KindReferential : NominalHeadClass → Prop
  | .pronoun       => False
  | .properName    => False
  | .specialCommon => True
  | .commonNoun    => True

instance : DecidablePred KindReferential := fun c => by
  cases c <;> unfold KindReferential <;> infer_instance

/-- Whether N-to-D raising is obligatory in argument position. -/
def RaisingObligatory : NominalHeadClass → Prop
  | .pronoun       => True   -- always in D (base-generated)
  | .properName    => True   -- obligatory raising in argument function
  | .specialCommon => False  -- conditioned raising
  | .commonNoun    => False  -- never raises

instance : DecidablePred RaisingObligatory := fun c => by
  cases c <;> unfold RaisingObligatory <;> infer_instance

-- The (28) partition is true by construction over the four `def`s above.
-- The pretty-printed conjunction theorem (`table_28` in earlier drafts)
-- was a `decide`-readback of the definitions, not a derivation, and is
-- omitted per the no-encoding-conclusions rule.

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
    d. *Casa*, kinship terms: raise only if followed by genitive modifier.
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
        (RaisingObligatory c₂ → RaisingObligatory c₁) := by
  intro c₁ c₂ h₁ h₂
  cases c₁ <;> cases c₂ <;> simp_all [propernessRank, RaisingObligatory]

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
  /-- The head noun's lexical naming type. -/
  namingType : LexicalNamingType
  /-- Does D contain a lexically referential expression?
      (either an overt determiner/quantifier, or N raised to D,
      or an expletive article linked to a raised N in a CHAIN) -/
  dHasReferentialContent : Bool
  /-- Is the nominal in argument function? -/
  isArgument : Bool
  deriving DecidableEq, Repr

/-- **(52) Denotation Hypothesis**: individuals are denoted in D.

    The D position is the locus of referential interpretation. A nominal
    denotes an individual (object or kind) iff its D position is
    associated with referential content. -/
def denotesIndividual (nc : NominalConfig) : Bool :=
  nc.dHasReferentialContent

/-- **(53) Licensing Condition**: arguments denote individuals.

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

/-- **(54b)** A variable: bound by an operator (existential, generic, or
    the variable-binding force of a lexical determiner) and ranging over
    a set of entities. Arises when D is empty (no referential content). -/
def isVariable (nc : NominalConfig) : Bool :=
  !nc.dHasReferentialContent

-- ============================================================================
-- § 4: Derived Theorems (55)–(56) and Core Generalization (33)
-- ============================================================================

/-- **(55)** Arguments with empty D are variables.

    From (52)+(53)+(54): if D is empty, then by (52) the nominal cannot
    denote an individual via D. By (53) it must still denote (being an
    argument). By (54b) the only remaining option is variable
    interpretation. -/
theorem empty_d_arguments_are_variables (nc : NominalConfig)
    (_hArg : nc.isArgument = true)
    (hEmptyD : nc.dHasReferentialContent = false) :
    isVariable nc = true := by
  simp [isVariable, hEmptyD]

/-- **(56)** An argument is a constant only if D contains a lexically
    referential expression.

    Equivalently: constant interpretation requires N-to-D (for proper
    names), an overt determiner, or a pronoun in D. -/
theorem constant_requires_d_content (nc : NominalConfig)
    (hConst : isConstant nc = true) :
    nc.dHasReferentialContent = true := hConst

-- **(33) Core Generalization**: reference (to individuals) iff N-to-D.
-- True by definition once `isConstant nc := nc.dHasReferentialContent`
-- (54a). The earlier explicit `core_generalization : isConstant nc ↔
-- nc.dHasReferentialContent` was `Iff.rfl` after definitional unfolding
-- and is omitted per the no-encoding-conclusions rule.

/-- **(41)** A nominal is an argument only if introduced by D.

    @cite{longobardi-2005} §7: this principle, from @cite{szabolcsi-1987}
    and @cite{stowell-1989-1991}, is derived from (52)+(53). In
    non-argument environments (predicates, vocatives, exclamations),
    nominals can occur without D. -/
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

/-- @cite{longobardi-2005} §10, question (57c): why must proper names raise?

    Object-naming nouns cannot satisfy (54b) — they name objects, not
    kinds, so they cannot enter the interpretive formula Dx.x ∈ kind(N)
    that gives variables their meaning. Their only route to argumenthood
    is constant interpretation via (54a), which requires D content. Since
    proper names are bare (no overt determiner), they must raise N-to-D
    to fill D. -/
theorem proper_names_must_raise :
    ∀ nc : NominalConfig,
      nc.namingType = .objectNaming →
      nc.isArgument = true →
      argumentLicensed nc = true →
      isConstant nc = true := by
  intro nc _ hArg hLic
  exact argument_requires_d nc hArg hLic

/-- @cite{longobardi-2005} §10, question (57a): why do common nouns not
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

/-- Whether a definite article is expletive (semantically vacuous
    placeholder) or a genuine semantic operator.

    @cite{longobardi-2005} §8: when a proper name appears with a definite
    article (*la Maria*, *il Gianni*), the article is expletive — it does
    not contribute uniqueness or familiarity semantics. It merely fills
    the D position that N-raising would otherwise occupy. -/
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
def ExpletiveBlocksKindReading : ArticleType → Prop
  | .expletive => True   -- no kind reading: article is semantically vacuous
  | .operator  => False  -- kind reading possible: article is a real operator

instance : DecidablePred ExpletiveBlocksKindReading := fun a => by
  cases a <;> unfold ExpletiveBlocksKindReading <;> infer_instance

-- ============================================================================
-- § 7: Bridge to Reference/Basic — Proper Names as Directly Referential
-- ============================================================================

open Semantics.Reference.Basic (properName isDirectlyReferential
  constantCharacter)

/-- Proper names in D are directly referential.

    Bridge connecting the syntactic analysis (N-to-D raising creates
    constant interpretation) to the semantic analysis (proper names have
    constant character and rigid content). The two perspectives converge:
    syntactically, D is the locus of reference; semantically, proper
    names are rigid designators. -/
theorem proper_name_in_d_is_constant
    {C W E : Type*} (e : E) :
    isDirectlyReferential (properName (C := C) (W := W) e).character ∧
    constantCharacter (properName (C := C) (W := W) e).character :=
  ⟨Semantics.Reference.Basic.properName_isDirectlyReferential e,
   Semantics.Reference.Basic.properName_constantCharacter e⟩

-- ============================================================================
-- § 8: N-to-D Raising as Head-to-Head Movement
-- ============================================================================

/-- N-to-D raising is head-to-head movement within the nominal extended
    projection.

    @cite{longobardi-2005} §5: proper names in Romance undergo N-to-D
    raising — the noun head moves from N to D, crossing intervening
    material (adjectives, modifiers in α). This is the nominal analogue
    of V-to-T raising (@cite{pollock-1989}).

    The movement is head-to-head (not head-to-spec): the noun stays
    minimal and reprojects in D. Evidence: the raised name forms a
    morphological unit with D, not a phrasal specifier. -/
structure NtoDRaising where
  /-- The N head (proper name or special common noun) -/
  nHead : NominalHeadClass
  /-- Language parametric setting -/
  dpParam : DPParameter
  /-- Raising actually occurs -/
  raises : Bool
  /-- Raising is obligatory (convergence requires it) -/
  obligatory : Bool

/-- Italian proper names raise obligatorily to D.

    @cite{longobardi-2005} §5: *Gianni ha telefonato* vs **Ha telefonato Gianni*
    (in neutral intonation). The name must precede adjectives and
    modifiers that intervene between N and D. -/
def italianPN : NtoDRaising where
  nHead := .properName
  dpParam := romance
  raises := true
  obligatory := true

/-- Italian common nouns do NOT raise to D. -/
def italianCN : NtoDRaising where
  nHead := .commonNoun
  dpParam := romance
  raises := false
  obligatory := false

/-- English proper names: D is weak, so raising is vacuous (no overt D
    to target). Names occur bare in argument position. -/
def englishPN : NtoDRaising where
  nHead := .properName
  dpParam := english
  raises := false  -- no overt raising needed (weak D)
  obligatory := false

-- ============================================================================
-- § 9: Italian Diagnostic Data — Solo Paradigm
-- ============================================================================

/-- @cite{longobardi-2005} §2: the *solo* paradigm. *Solo* 'only' is an
    adverb that must c-command its associate. When *solo* precedes a
    proper name but follows a common noun, this diagnoses the structural
    position of the noun head.

    - *Solo Gianni...* — name has raised past *solo* (N-to-D)
    - *Il solo tavolo...* — common noun stays below *solo*

    This asymmetry is the primary diagnostic for N-to-D. -/
structure SoloDiagnostic where
  /-- The noun tested -/
  headClass : NominalHeadClass
  /-- Does the noun precede *solo*? -/
  precedesSolo : Bool

/-- Proper names precede *solo* (they have raised past it). -/
def soloPN : SoloDiagnostic :=
  { headClass := .properName, precedesSolo := true }

/-- Common nouns follow *solo* (they remain in situ). -/
def soloCN : SoloDiagnostic :=
  { headClass := .commonNoun, precedesSolo := false }

/-- The *solo* diagnostic confirms raising iff `precedesSolo`. -/
theorem solo_diagnoses_raising :
    soloPN.precedesSolo = true ∧ soloCN.precedesSolo = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 10: Expletive Articles with Proper Names
-- ============================================================================

/-- @cite{longobardi-2005} §8: Italian proper names optionally appear
    with a definite article (*la Maria*, *il Gianni*). This article is
    **expletive** — semantically vacuous, serving only as a phonological
    placeholder for D.

    Evidence: *la Maria* behaves identically to bare *Maria*:
    - Wide scope only (no narrow scope under quantifiers)
    - Rigid reference (same individual at every world)
    - No kind/generic reading
    This contrasts with genuine definite articles (*il tavolo* 'the
    table'), which CAN have narrow scope and kind readings. -/
structure ExpletiveArticleDatum where
  /-- The nominal expression -/
  form : String
  /-- Article type -/
  articleType : ArticleType
  /-- Has wide scope only (rigid) -/
  wideScopeOnly : Bool
  /-- Admits kind/generic reading -/
  kindReading : Bool

def laMaria : ExpletiveArticleDatum :=
  { form := "la Maria"
  , articleType := .expletive
  , wideScopeOnly := true
  , kindReading := false }

def ilTavolo : ExpletiveArticleDatum :=
  { form := "il tavolo"
  , articleType := .operator
  , wideScopeOnly := false
  , kindReading := true }

/-- Expletive articles block kind readings; operator articles allow them. -/
theorem expletive_vs_operator :
    ExpletiveBlocksKindReading laMaria.articleType ∧
    ¬ ExpletiveBlocksKindReading ilTavolo.articleType :=
  ⟨trivial, id⟩

/-- Expletive articles preserve rigidity (wide scope only). -/
theorem expletive_preserves_rigidity :
    laMaria.wideScopeOnly = true ∧ laMaria.kindReading = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 11: Bridge to Longobardi 2001 — ArgumentType ↔ NominalConfig
-- ============================================================================

/-- Map @cite{longobardi-2001}'s `ArgumentType` to the topological
    mapping's constant/variable distinction.

    Referential arguments = constants (D has referential content).
    Quantificational arguments = variables (D is empty, operator-bound). -/
def argumentTypeToConfig (at_ : ArgumentType) : NominalConfig :=
  match at_ with
  | .referential =>
    { namingType := .objectNaming
    , dHasReferentialContent := true
    , isArgument := true }
  | .quantificational =>
    { namingType := .kindNaming
    , dHasReferentialContent := false
    , isArgument := true }

/-- Referential arguments are constants in the topological mapping. -/
theorem referential_is_constant :
    isConstant (argumentTypeToConfig .referential) = true := rfl

/-- Quantificational arguments are variables in the topological mapping. -/
theorem quantificational_is_variable :
    isVariable (argumentTypeToConfig .quantificational) = true := rfl

-- ============================================================================
-- § 12: Bridge to DPParameter — Strong D Requires Overt D Content
-- ============================================================================

/-- @cite{longobardi-2001}'s `strongD` parameter corresponds to the
    topological mapping's requirement for overt referential content in D.

    When D is strong (Romance), referential interpretation requires
    visible association with D — either N-to-D raising or an overt
    determiner. When D is weak (English), the association can be
    covert. -/
theorem strong_d_bridge :
    pnRequiresOvertD romance = true ∧
    pnRequiresOvertD english = false ∧
    bnCanBeReferential romance = false ∧
    bnCanBeReferential english = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Greek confirms the prediction: strong D + opaque α forces overt
    articles on all referential arguments including proper names. -/
theorem greek_confirms :
    pnRequiresOvertD greek = true ∧
    bnCanBeReferential greek = false :=
  ⟨rfl, rfl⟩

end Longobardi2005
