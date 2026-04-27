import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalist.TopologicalMapping
import Linglib.Theories.Syntax.Minimalist.HeadMovement.Basic
import Linglib.Theories.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Theories.Syntax.Minimalist.Economy
import Linglib.Phenomena.Reference.Studies.Longobardi2001

/-!
# Longobardi (2005): Toward a Unified Grammar of Reference
@cite{longobardi-2005} @cite{longobardi-1994}

Zeitschrift für Sprachwissenschaft 24(1): 5--44.

## Core Contribution

A syntax-semantics mapping theory reducing reference to nominal head
position: a nominal refers to an individual (constant) iff its D
position contains referential content. This unifies object reference
and kind reference under a single structural generalization.

The theory layer (`TopologicalMapping.lean`) formalizes the axioms,
derived theorems, and noun taxonomy. This study file:

1. Instantiates N-to-D raising as `HeadToHeadMovement` on the nominal
   extended projection (N → D)
2. Records Italian diagnostic data (solo paradigm, expletive articles)
3. Bridges to @cite{longobardi-2001}'s `DPParameter` and `ArgumentType`
4. Derives Last Resort: proper names MUST raise (convergence); common
   nouns must NOT raise (economy)
-/

namespace Longobardi2005

open Minimalist.TopologicalMapping
open Longobardi2001 (DPParameter ArgumentType
  romance english greek pnRequiresOvertD bnCanBeReferential)

-- ============================================================================
-- § 1: N-to-D Raising as Head-to-Head Movement
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
-- § 2: Italian Diagnostic Data — Solo Paradigm
-- ============================================================================

/-- @cite{longobardi-2005} §2: the solo paradigm. *Solo* 'only' is an
    adverb that must c-command its associate. When *solo* precedes a
    proper name but follows a common noun, this diagnoses the structural
    position of the noun head.

    - *Solo Gianni...* — name has raised past solo (N-to-D)
    - *Il solo tavolo...* — common noun stays below solo

    This asymmetry is the primary diagnostic for N-to-D. -/
structure SoloDiagnostic where
  /-- The noun tested -/
  headClass : NominalHeadClass
  /-- Does the noun precede solo? -/
  precedesSolo : Bool

/-- Proper names precede solo (they have raised past it). -/
def soloPN : SoloDiagnostic :=
  { headClass := .properName, precedesSolo := true }

/-- Common nouns follow solo (they remain in situ). -/
def soloCN : SoloDiagnostic :=
  { headClass := .commonNoun, precedesSolo := false }

/-- The solo diagnostic confirms raising iff precedesSolo. -/
theorem solo_diagnoses_raising :
    soloPN.precedesSolo = true ∧ soloCN.precedesSolo = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 3: Expletive Articles with Proper Names
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
-- § 4: Bridge to Longobardi 2001 — ArgumentType ↔ NominalConfig
-- ============================================================================

/-- Map @cite{longobardi-2001}'s `ArgumentType` to the topological mapping's
    constant/variable distinction.

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
-- § 5: Last Resort — Why PNs Must Raise and CNs Must Not
-- ============================================================================

/-- @cite{longobardi-2005} §10: N-to-D raising is a Last Resort operation.

    **Convergence side**: Object-naming nouns (proper names) MUST raise
    because they cannot satisfy (54b) — they name objects, not kinds,
    so variable interpretation is unavailable. Their only path to
    argumenthood is constant interpretation via (54a), requiring D
    content. Since they are bare, they must raise to fill D.

    **Economy side**: Kind-naming nouns (common nouns) must NOT raise
    because they CAN satisfy (54b) — variable interpretation suffices.
    Raising would be a gratuitous operation violating economy. -/
theorem last_resort_proper_names :
    ∀ nc : NominalConfig,
      nc.namingType = .objectNaming →
      nc.isArgument = true →
      argumentLicensed nc = true →
      isConstant nc = true := by
  intro nc _ hArg hLic
  exact argument_requires_d nc hArg hLic

/-- Common nouns with empty D receive variable interpretation.
    Variable interpretation suffices for argumenthood (bound by Ex/Gen),
    so no raising is needed — raising would violate economy. -/
theorem last_resort_common_nouns :
    ∀ nc : NominalConfig,
      nc.namingType = .kindNaming →
      nc.isArgument = true →
      nc.dHasReferentialContent = false →
      isVariable nc = true := by
  intro nc _ hArg hEmpty
  exact empty_d_arguments_are_variables nc hArg hEmpty

-- ============================================================================
-- § 6: Bridge to DPParameter — Strong D Requires Overt D Content
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
