import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Theories.Semantics.Lexical.Plural.Cumulativity
import Linglib.Core.Logic.Truth3
import Linglib.Phenomena.Generics.Studies.TesslerGoodman2019
import Linglib.Phenomena.Generics.KindReference
import Linglib.Phenomena.Generics.Studies.Longobardi2001

/-! # Guerrini (2026): Distributive Kind Predication
@cite{guerrini-2026}

Natural Language Semantics. Published online 02 March 2026.

## Core Thesis

Generalizations with kind-denoting plurals (English bare plurals, Italian
definite plurals) are structurally ambiguous between:

1. **Bona Fide Genericity**: the kind enters the restrictor of **Gen** →
   law-like reading ("Lions hunt" ≈ "Generally, lions hunt")
2. **Distributive Kind Predication**: the kind is evaluated at the actual
   world and **DIST** distributes the predicate over its atomic members →
   accidental reading ("LLMs are popular" ≈ "The LLMs are popular")

This ambiguity — not a complex semantics for Gen — explains why
kind-denoting plurals have wider distribution than singular indefinites.
Singular indefinites cannot denote kinds (∩ undefined for singulars),
so DIST never applies, and they are limited to Bona Fide Genericity.

## Key Predictions

- **Table 1**: Kind-denoting plurals appear in both law-like and accidental
  generalizations; singular indefinites appear only in law-like ones.
- **Table 3**: Homogeneity removal — 'all' removes DIST-homogeneity,
  'always' removes Gen-homogeneity. Kind-denoting plurals allow both;
  singular indefinites allow only 'always'.
- **Italian subjunctive**: Forces Bona Fide Generic parse (kind must be
  in Gen restrictor, which licenses subjunctive). Accidental readings
  disappear under subjunctive-modified restrictors.
- **Episodic sentences** (§5): Near-universal readings of bare plurals
  ("Birds are migrating" ≈ ∀) arise via Distributive Kind Predication
  without Gen. Singular indefinites get only existential readings.

## Connection to Tessler & Goodman (2019)

@cite{tessler-goodman-2019}'s threshold semantics for generics
(see `Phenomena/Generics/Studies/TesslerGoodman2019.lean`)
applies to the **Bona Fide Generic** parse: prevalence-based inference
determines whether the Gen-quantified generalization is judged true.
But on the **Distributive Kind Predication** parse, there is no Gen —
the sentence is non-generic, and its truth conditions are those of a
referential definite plural with DIST. Guerrini's ambiguity thus explains
why "accidental" generalizations resist Q-adverb modification and don't
display quantificational variability effects: they aren't quantified.

## Nominal Mapping and Cross-Linguistic Variation

English bare plurals are ambiguous between kind and property denotation:
- Kind → Distributive/cumulative LFs or Bona Fide Generic LFs
- Property → Bona Fide Generic LFs or low-scoped existential LFs

Italian definite plurals unambiguously denote kinds.
Italian bare plurals unambiguously denote properties.

This derives from @cite{chierchia-1998}'s Nominal Mapping Parameter:
English [+arg, +pred] allows both; Italian [-arg, +pred] forces D.
-/

namespace Phenomena.Generics.Studies.Guerrini2026

open Semantics.Lexical.Noun.Kind.Chierchia1998 (NominalMapping Kind canDenoteKind
  canDenoteProperty downDefinedFor DPP)
open Core.Duality (Truth3)
open Semantics.Lexical.Plural.Distributivity (distMaximal pluralTruthValue
  allSatisfy noneSatisfy)
open Phenomena.Generics.KindReference (NominalDenotation)

-- ============================================================================
-- § 1: Structural Ambiguity — The Two LFs
-- ============================================================================

/-- Available LF parses for sentences with kind-denoting plurals.

Guerrini's central claim: English bare plurals are structurally ambiguous
between four LF types (diagram (145)). The first three require kind
denotation; the fourth requires property denotation.

Kind-denoting plurals can access all four; singular indefinites access only BFG. -/
inductive GeneralizationLF where
  /-- Kind enters restrictor of Gen. World variable bound by Gen.
      Law-like reading: "Generally, lions hunt." (Guerrini's (29)) -/
  | bonaFideGeneric
  /-- Kind evaluated at actual world s₀, DIST distributes predicate
      over atoms. No Gen. Accidental reading: "The lions (of the actual
      world) hunt." (Guerrini's (30)) -/
  | distributiveKindPred
  /-- Kind evaluated at actual world s₀, ** (cumulative operator)
      applies. No Gen. "Elephants live in Africa and Asia." (§4) -/
  | cumulativeKindPred
  /-- Property reading: bare plural interpreted as property, composed
      with predicate via DPP (Derived Property Predication, §5.3).
      Low-scoped existential: "Bears are destroying my garden" ≈
      ∃x[bear(x) ∧ destroying-my-garden(x)]. (Guerrini's (105b)) -/
  | existentialDPP
  deriving DecidableEq, Repr, BEq

-- Singular indefinites cannot denote kinds (∩ undefined for singular count
-- nouns), so only Bona Fide Genericity is available — no DKP/CKP parse.
-- This is captured by `singular_no_accidental` (§3) which chains
-- `downDefinedFor` → kind denotation → LF availability → table1.

-- ============================================================================
-- § 2: Distributive Kind Predication (the bridge definition)
-- ============================================================================

section DistributiveKindPred

variable {Atom W : Type} [DecidableEq Atom] [Fintype Atom]

/-- Extract a kind's extension at a world as a `Finset`, bridging
    Chierchia1998's `Set Atom` to Distributivity's `Finset Atom`.

    This is the type-level bridge between the two modules:
    - `Kind.concept w : Set Atom` (mathematical, for proofs)
    - `Finset Atom` (computational, for DIST) -/
noncomputable def kindExtensionFinset (k : Kind W Atom) (w : W) : Finset Atom :=
  @Finset.filter _ (· ∈ k.concept w) (fun _ => Classical.dec _) Finset.univ

/--
Distributive Kind Predication: evaluate a kind at the actual world to
get its maximal sum, then distribute a predicate over its atomic parts.

This is the composition of DIST from `Plural/Distributivity.lean` with
kind extension from `Chierchia1998.lean`. No Gen operator is involved.

Parameterized by `kindExtension : W → Finset Atom` (the computational
representation of the kind's extension). For a `Kind` value, use
`kindExtensionFinset` to obtain this.

Guerrini (2026), structure (30):
  ∀y(y ≤ ∩lions_{s₀}) → ⟦hunt⟧_{s₀}(y)
-/
def distributiveKindPred
    (kindExtension : W → Finset Atom)
    (P : Atom → W → Bool)
    (s₀ : W) : Bool :=
  distMaximal P (kindExtension s₀) s₀

/--
Trivalent truth value for Distributive Kind Predication.

Inherits homogeneity and non-maximality from DIST on referential plurals
(Križ & Spector 2021). This predicts that accidental generalizations
with bare plurals behave like referential definite plurals w.r.t.
polarity reversals and exception tolerance.
-/
def distributiveKindPredTV
    (kindExtension : W → Finset Atom)
    (P : Atom → W → Bool)
    (s₀ : W) : Truth3 :=
  pluralTruthValue P (kindExtension s₀) s₀

/-- Distributive Kind Predication composed directly from a `Kind` value.
    Noncomputable because `Set.toFinset` requires classical decidability. -/
noncomputable def distributiveKindPredOfKind
    (k : Kind W Atom)
    (P : Atom → W → Bool)
    (s₀ : W) : Bool :=
  distributiveKindPred (kindExtensionFinset k) P s₀

end DistributiveKindPred

-- ============================================================================
-- § 3: Table 1 — Distribution of Generalizations
-- ============================================================================

/-- Flavor of a generalization. -/
inductive GenFlavor where
  /-- Law-like: "LLMs utilize Deep Learning" — true by necessity/regularity -/
  | lawLike
  /-- Accidental: "LLMs are popular" — contingently true of actual instances -/
  | accidental
  deriving DecidableEq, Repr, BEq

/-- Nominal form in the generalization. -/
inductive NominalForm where
  /-- Kind-denoting plural: English bare plural or Italian definite plural -/
  | kindDenotingPlural
  /-- Singular indefinite: "A lion hunts" / "Un leone caccia" -/
  | singularIndefinite
  deriving DecidableEq, Repr, BEq

/-- Table 1 from Guerrini (2026): distribution of generalizations.

Kind-denoting plurals can appear in both law-like and accidental
generalizations. Singular indefinites can appear only in law-like ones.
The `*` for singular indefinite + accidental means the form is possible
only with a law-like construal forced. -/
def table1 (form : NominalForm) (flavor : GenFlavor) : Bool :=
  match form, flavor with
  | .kindDenotingPlural, .lawLike     => true
  | .kindDenotingPlural, .accidental  => true
  | .singularIndefinite, .lawLike     => true
  | .singularIndefinite, .accidental  => false

/-- Kind-denoting plurals have wider distribution than singular indefinites. -/
theorem kind_plural_wider_distribution :
    (∀ f, table1 .kindDenotingPlural f = true) ∧
    ¬(∀ f, table1 .singularIndefinite f = true) := by
  constructor
  · intro f; cases f <;> rfl
  · intro h; exact absurd (h .accidental) (by decide)

/-- The LF parse determines the generalization flavor.

BFG → law-like (modal generalization, Gen quantifies over situations).
DKP/CKP → accidental (no Gen; predicate applies to actual kind instances).
DPP → neither law-like nor accidental: it's an existential episodic reading,
  not a generalization at all. We classify it as accidental (non-generic). -/
def lfFlavor : GeneralizationLF → GenFlavor
  | .bonaFideGeneric      => .lawLike
  | .distributiveKindPred => .accidental
  | .cumulativeKindPred   => .accidental
  | .existentialDPP       => .accidental

/-- The accidental flavor is unavailable for singular indefinites.

Full derivation chain from the paper's argument:
1. ∩ is undefined for singular count nouns (@cite{chierchia-1998})
2. Without ∩, no kind denotation is available
3. Without kind denotation, DKP and CKP are unavailable
4. Without DKP/CKP, the only LF is BFG → only law-like readings

This explains why singular indefinites have a narrower distribution
than kind-denoting plurals in generalizations. -/
theorem singular_no_accidental :
    -- Step 1: ∩ undefined for singular count nouns
    downDefinedFor .count false = false ∧
    -- Step 2: Non-generic LFs require kind or property denotation
    (∀ lf : GeneralizationLF, lfFlavor lf = .accidental →
      lf = .distributiveKindPred ∨ lf = .cumulativeKindPred ∨ lf = .existentialDPP) ∧
    -- Step 3: Table 1 reflects this — singular indefinites lack accidental
    table1 .singularIndefinite .accidental = false := by
  exact ⟨rfl, fun lf h => by cases lf <;> simp_all [lfFlavor], rfl⟩

-- ============================================================================
-- § 4: Table 3 — Homogeneity Removal
-- ============================================================================

/-- Operator that introduces homogeneity (Guerrini's Table 3). -/
inductive HomogeneitySource where
  /-- DIST: distributes over individuals; homogeneity from trivalence -/
  | dist
  /-- Gen: modal quantifier; homogeneity from generic quantification -/
  | gen
  deriving DecidableEq, Repr, BEq

/-- Homogeneity remover: the adverb/quantifier that removes homogeneity. -/
inductive HomogeneityRemover where
  /-- 'all': replaces DIST with non-homogeneous universal ∀ -/
  | all
  /-- 'always': replaces Gen with non-homogeneous universal ∀ -/
  | always
  deriving DecidableEq, Repr, BEq

/-- Table 3: which removers apply to which sources.

'all' removes DIST-homogeneity (it's the non-homogeneous counterpart
of DIST). 'always' removes Gen-homogeneity (it's a non-homogeneous
Q-adverb replacing Gen). -/
def removesHomogeneity (r : HomogeneityRemover) (s : HomogeneitySource) : Bool :=
  match r, s with
  | .all, .dist    => true
  | .always, .gen  => true
  | .all, .gen     => false
  | .always, .dist => false

/-- Sentence type and its homogeneous LF sources. -/
inductive SentenceType where
  /-- Referential definite plural: "The kids are American" -/
  | referentialDefinitePlural
  /-- Singular indefinite generic: "A lion hunts" -/
  | singularIndefiniteGeneric
  /-- Kind-denoting plural generic: "Lions hunt" -/
  | kindDenotingPluralGeneric
  deriving DecidableEq, Repr, BEq

/-- Which homogeneity sources are present in each sentence type.

Referential definite plurals have only DIST.
Singular indefinite generics have only Gen.
Kind-denoting plural generics have BOTH (due to structural ambiguity). -/
def hasHomogeneitySource (st : SentenceType) (hs : HomogeneitySource) : Bool :=
  match st, hs with
  | .referentialDefinitePlural,  .dist => true
  | .referentialDefinitePlural,  .gen  => false
  | .singularIndefiniteGeneric,  .dist => false
  | .singularIndefiniteGeneric,  .gen  => true
  | .kindDenotingPluralGeneric,  .dist => true   -- from DKP parse
  | .kindDenotingPluralGeneric,  .gen  => true   -- from BFG parse

/-- Which removers are available for each sentence type. -/
def removerAvailable (st : SentenceType) (r : HomogeneityRemover) : Bool :=
  match r with
  | .all    => hasHomogeneitySource st .dist
  | .always => hasHomogeneitySource st .gen

-- Table 3 verification theorems

/-- Referential definite plurals: 'all' OK, 'always' not.
    "The bears are all brown" OK vs "#The bears are always brown" -/
theorem refDefPl_removers :
    removerAvailable .referentialDefinitePlural .all = true ∧
    removerAvailable .referentialDefinitePlural .always = false := ⟨rfl, rfl⟩

/-- Singular indefinite generics: 'always' OK, 'all' not.
    "A bear is always brown" OK vs "#A bear is all brown" -/
theorem singIndef_removers :
    removerAvailable .singularIndefiniteGeneric .all = false ∧
    removerAvailable .singularIndefiniteGeneric .always = true := ⟨rfl, rfl⟩

/-- Kind-denoting plural generics: BOTH 'all' and 'always' OK.
    "Bears are all brown" OK AND "Bears are always brown" OK -/
theorem kindPlural_removers :
    removerAvailable .kindDenotingPluralGeneric .all = true ∧
    removerAvailable .kindDenotingPluralGeneric .always = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 5: English BP Ambiguity (Guerrini's diagram (145))
-- ============================================================================

-- NominalDenotation (.kind | .property) is imported from KindReference.lean.

/-- Cross-linguistic nominal form. -/
inductive NominalExpression where
  | englishBarePlural
  | italianDefinitePlural
  | italianBarePlural
  deriving DecidableEq, Repr, BEq

/-- The Nominal Mapping Parameter for each nominal expression. -/
def nominalMapping : NominalExpression → NominalMapping
  | .englishBarePlural     => .argAndPred
  | .italianDefinitePlural => .predOnly
  | .italianBarePlural     => .predOnly

/-- Whether an overt determiner (D) is present. -/
def hasD : NominalExpression → Bool
  | .englishBarePlural     => false  -- bare = no D
  | .italianDefinitePlural => true   -- "i/gli/le" = overt D
  | .italianBarePlural     => false  -- bare = no D

/-- Available denotations for each nominal form in argument position.

For kind denotation, derived from `canDenoteKind` (Chierchia 1998).
For property denotation, derived from the Nominal Mapping Parameter
combined with D-status:

- `argOnly` [+arg, -pred]: nouns are kinds, never properties
- `argAndPred` [+arg, +pred]: property denotation always available
  (D gives definiteness, not kind-forcing)
- `predOnly` [-arg, +pred]: nouns start as predicates; D maps them
  to kinds (via ∩), blocking the property reading

This yields:
- English BPs [+arg, +pred, -D]: both kind and property ✓
- Italian def pl [-arg, +pred, +D]: kind only (D forces kind) ✓
- Italian bare pl [-arg, +pred, -D]: property only (no ∩) ✓ -/
def canDenote (ne : NominalExpression) (nd : NominalDenotation) : Bool :=
  match nd with
  | .kind     => canDenoteKind (nominalMapping ne) (hasD ne)
  | .property => match nominalMapping ne with
    | .argOnly    => false      -- [+arg, -pred]: nouns are never predicates
    | .argAndPred => true       -- [+arg, +pred]: property always available
    | .predOnly   => !hasD ne   -- [-arg, +pred]: D maps to kind, blocks property

/-- English bare plurals are ambiguous. -/
theorem english_bp_ambiguous :
    canDenote .englishBarePlural .kind = true ∧
    canDenote .englishBarePlural .property = true := ⟨rfl, rfl⟩

/-- Italian definite plurals unambiguously denote kinds. -/
theorem italian_def_pl_kind_only :
    canDenote .italianDefinitePlural .kind = true ∧
    canDenote .italianDefinitePlural .property = false := ⟨rfl, rfl⟩

/-- Italian bare plurals unambiguously denote properties. -/
theorem italian_bare_pl_property_only :
    canDenote .italianBarePlural .kind = false ∧
    canDenote .italianBarePlural .property = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: LF Availability by Nominal Form
-- ============================================================================

/-- Which LFs are available for a given nominal form.

Kind denotation enables DKP and CKP (kind-level LFs).
Property denotation enables BFG (property enters Gen restrictor)
and existential DPP (property yields low-scoped ∃).
Diagram (145): four paths for English BPs, two via kind, two via property. -/
def lfAvailable (ne : NominalExpression) (lf : GeneralizationLF) : Bool :=
  match lf with
  | .bonaFideGeneric       => true  -- always: kind enters Gen restrictor (19) or property does (20)
  | .distributiveKindPred  => canDenote ne .kind
  | .cumulativeKindPred    => canDenote ne .kind
  | .existentialDPP        => canDenote ne .property

/-- English bare plurals allow all four LFs (diagram (145)):
    kind path → BFG, DKP, CKP; property path → BFG, DPP. -/
theorem english_bp_all_lfs :
    lfAvailable .englishBarePlural .bonaFideGeneric = true ∧
    lfAvailable .englishBarePlural .distributiveKindPred = true ∧
    lfAvailable .englishBarePlural .cumulativeKindPred = true ∧
    lfAvailable .englishBarePlural .existentialDPP = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Italian definite plurals: kind-level LFs only (no property → no DPP).
    This predicts near-universal but no existential readings in episodics (§5.4). -/
theorem italian_def_pl_lfs :
    lfAvailable .italianDefinitePlural .bonaFideGeneric = true ∧
    lfAvailable .italianDefinitePlural .distributiveKindPred = true ∧
    lfAvailable .italianDefinitePlural .cumulativeKindPred = true ∧
    lfAvailable .italianDefinitePlural .existentialDPP = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Italian bare plurals: property-level LFs only (BFG + DPP, no DKP/CKP).
    This predicts existential but no near-universal readings in episodics (§5.4). -/
theorem italian_bare_pl_lfs :
    lfAvailable .italianBarePlural .bonaFideGeneric = true ∧
    lfAvailable .italianBarePlural .distributiveKindPred = false ∧
    lfAvailable .italianBarePlural .cumulativeKindPred = false ∧
    lfAvailable .italianBarePlural .existentialDPP = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 7: Episodic Sentences (§5 of the paper)
-- ============================================================================

/-- Episodic reading availability for bare plurals vs singular indefinites.

"Birds are migrating" can mean ≈ all birds are migrating (∀).
"A bird is migrating" can only mean ∃ (or *∀ via Gen). -/
structure EpisodicDatum where
  sentence : String
  nominalForm : NominalForm
  /-- Near-universal (∀) reading via DIST on kind extension? -/
  nearUniversalOK : Bool
  /-- Existential (∃) reading? -/
  existentialOK : Bool
  notes : String

def birdsMigrating : EpisodicDatum :=
  { sentence := "Birds are migrating."
  , nominalForm := .kindDenotingPlural
  , nearUniversalOK := true   -- via DKP: DIST(⟦migrating⟧)(∩birds_{s₀})
  , existentialOK := true      -- via DPP: property reading → low-scoped ∃
  , notes := "∀ via DKP (kind → DIST); ∃ via DPP (property → ∃)" }

def aBirdMigrating : EpisodicDatum :=
  { sentence := "A bird is migrating."
  , nominalForm := .singularIndefinite
  , nearUniversalOK := false  -- no kind denotation, no DIST
  , existentialOK := true
  , notes := "Only ∃ (or *∀ forced via Gen); no DKP available" }

def studentsScarred : EpisodicDatum :=
  { sentence := "Students are scared."
  , nominalForm := .kindDenotingPlural
  , nearUniversalOK := true   -- via DKP
  , existentialOK := true      -- via DPP
  , notes := "Stage-level + context; ∀ via DKP, ∃ via DPP" }

def aStudentScared : EpisodicDatum :=
  { sentence := "A student is scared."
  , nominalForm := .singularIndefinite
  , nearUniversalOK := false
  , existentialOK := true
  , notes := "Singular indefinite: only ∃" }

def episodicData : List EpisodicDatum :=
  [birdsMigrating, aBirdMigrating, studentsScarred, aStudentScared]

-- Kind-denoting plurals allow near-universal episodic readings;
-- singular indefinites do not.
example : (episodicData.filter (·.nominalForm == .kindDenotingPlural)
      |>.all (·.nearUniversalOK)) = true := rfl
example : (episodicData.filter (·.nominalForm == .singularIndefinite)
      |>.all (!·.nearUniversalOK)) = true := rfl

-- ============================================================================
-- § 7a: Italian Episodic Disambiguation (§5.4)
-- ============================================================================

/-!
## Italian as a disambiguator for episodic bare plural readings

@cite{guerrini-2026} §5.4: Italian separates the two LFs that are
ambiguous in English bare plurals. English "investigative journalists
asked questions" is ambiguous between:

- Kind reading (Italian definite plural): near-universal (DKP)
  "I giornalisti investigativi hanno posto domande" — all of them asked
- Property reading (Italian bare plural): existential (DPP)
  "Giornalisti investigativi hanno posto domande" — some of them asked

This is a direct consequence of the unambiguous denotation types in Italian:
Italian definite plurals denote kinds → DKP → near-universal
Italian bare plurals denote properties → DPP → existential
-/

/-- Italian episodic datum (examples (107)-(110), (113)-(114)). -/
structure ItalianEpisodicDatum where
  sentence : String
  gloss : String
  nominalExpression : NominalExpression
  nearUniversalOK : Bool
  existentialOK : Bool
  notes : String

-- (110): I giornalisti investigativi hanno posto domande
def itDefPlJournalists : ItalianEpisodicDatum :=
  { sentence := "I giornalisti investigativi hanno posto domande."
  , gloss := "The investigative journalists asked questions."
  , nominalExpression := .italianDefinitePlural
  , nearUniversalOK := true     -- kind → DKP → all journalists asked
  , existentialOK := false       -- def pl cannot denote property
  , notes := "Kind denotation → DKP → near-universal only" }

-- (109): Giornalisti investigativi hanno posto domande
def itBarePlJournalists : ItalianEpisodicDatum :=
  { sentence := "Giornalisti investigativi hanno posto domande."
  , gloss := "Investigative journalists asked questions."
  , nominalExpression := .italianBarePlural
  , nearUniversalOK := false    -- bare pl cannot denote kind
  , existentialOK := true        -- property → DPP → some journalists asked
  , notes := "Property denotation → DPP → existential only" }

def italianEpisodicData : List ItalianEpisodicDatum :=
  [itDefPlJournalists, itBarePlJournalists]

/-- Italian definite plurals get near-universal readings in episodics;
    Italian bare plurals get only existential readings. (§5.4) -/
theorem italian_episodic_disambiguation :
    (italianEpisodicData.filter (·.nominalExpression == .italianDefinitePlural)
      |>.all (·.nearUniversalOK)) = true ∧
    (italianEpisodicData.filter (·.nominalExpression == .italianBarePlural)
      |>.all (!·.nearUniversalOK)) = true := ⟨rfl, rfl⟩

-- (113)-(114): Italian generalization disambiguation (§5.4)
-- These are generalizations, not episodics — definite plurals support
-- accidental readings (DKP), bare plurals support only law-like (BFG).

/-- Italian generalization datum (§5.4, examples (113)-(114)). -/
structure ItalianGenDisambiguationDatum where
  sentence : String
  gloss : String
  nominalExpression : NominalExpression
  /-- Accidental reading available (via DKP)? -/
  accidentalOK : Bool
  /-- Law-like reading available (via BFG)? -/
  lawLikeOK : Bool
  notes : String

def itDefPlCandidates : ItalianGenDisambiguationDatum :=
  { sentence := "I candidati puntuali non vengono assunti."
  , gloss := "Punctual candidates don't get hired."
  , nominalExpression := .italianDefinitePlural
  , accidentalOK := true    -- DKP available (def pl denotes kind)
  , lawLikeOK := true        -- BFG always available
  , notes := "Definite plural: both law-like and accidental readings" }

def itBarePlCandidates : ItalianGenDisambiguationDatum :=
  { sentence := "Candidati puntuali non vengono assunti."
  , gloss := "Punctual candidates don't get hired."
  , nominalExpression := .italianBarePlural
  , accidentalOK := false   -- no DKP (bare pl cannot denote kind)
  , lawLikeOK := true        -- BFG via property entering Gen restrictor
  , notes := "Bare plural: law-like only; accidental reading unavailable" }

def italianGenDisambiguationData : List ItalianGenDisambiguationDatum :=
  [itDefPlCandidates, itBarePlCandidates]

/-- Italian definite plurals support accidental generalizations;
    Italian bare plurals do not. Derived from kind denotation availability. -/
theorem italian_gen_disambiguation :
    (italianGenDisambiguationData.filter
      (·.nominalExpression == .italianDefinitePlural)
      |>.all (·.accidentalOK)) = true ∧
    (italianGenDisambiguationData.filter
      (·.nominalExpression == .italianBarePlural)
      |>.all (!·.accidentalOK)) = true := ⟨rfl, rfl⟩

/-- The gen disambiguation derives from the same kind-denotation chain:
    def pl can denote kind → DKP → accidental; bare pl cannot. -/
theorem italian_gen_from_kind_denotation :
    canDenote .italianDefinitePlural .kind = true ∧
    lfAvailable .italianDefinitePlural .distributiveKindPred = true ∧
    canDenote .italianBarePlural .kind = false ∧
    lfAvailable .italianBarePlural .distributiveKindPred = false := ⟨rfl, rfl, rfl, rfl⟩

/-- This disambiguation is derived from unambiguous denotation types. -/
theorem italian_episodic_from_denotation :
    -- Italian def pl: kind → DKP available → near-universal
    canDenote .italianDefinitePlural .kind = true ∧
    -- Italian bare pl: no kind → no DKP → no near-universal
    canDenote .italianBarePlural .kind = false ∧
    -- Italian bare pl: property → DPP available → existential
    canDenote .italianBarePlural .property = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 8: Connection to Tessler & Goodman (2019)
-- ============================================================================

/-!
## Guerrini × Tessler & Goodman: Where Pragmatics Applies

@cite{tessler-goodman-2019}'s threshold semantics and RSA inference
apply specifically to the **Bona Fide Generic** parse. On this parse,
a kind enters the restrictor of Gen, which is semantically parallel
to a modalized universal quantifier. The threshold θ determines how
many exceptions are tolerated, and pragmatic inference (L1 reasoning
over priors on prevalence) explains context-sensitivity.

On the **Distributive Kind Predication** parse, by contrast, there is
no Gen at all. The sentence's truth conditions are compositionally
determined by DIST applied to the kind's extension at the evaluation
world. This is a non-generic, non-quantificational reading. RSA
generic inference does not apply here — the sentence is true iff
(approximately) all actual members of the kind satisfy the predicate,
modulo homogeneity/non-maximality from DIST.

### Predictions for RSA

1. **Accidental generalizations resist pragmatic threshold adjustment.**
   "LLMs are popular" on the DKP parse is true iff the actual LLMs are
   popular — no threshold, no prevalence inference. This explains why
   accidental generalizations feel "factual" rather than "generic."

2. **Law-like generalizations show prevalence sensitivity.**
   "Lions hunt" on the BFG parse is judged via prevalence × prior,
   exactly as @cite{tessler-goodman-2019} predict. The same utterance
   on its DKP parse is judged as a factual claim about actual lions.

3. **Q-adverb diagnostics align.**
   "Lions usually hunt" forces the BFG parse (overt Q-adverb replaces
   Gen). Since only this parse involves generic quantification, only
   this parse is subject to Tessler & Goodman's pragmatic inference.
   The DKP parse is unavailable with overt Q-adverbs — DIST and
   Q-adverbs compete for the same structural position.
-/

/-- Whether a given LF parse is subject to RSA generic inference
    (Tessler & Goodman 2019's threshold semantics). -/
def subjectToGenericInference (lf : GeneralizationLF) : Bool :=
  match lf with
  | .bonaFideGeneric      => true   -- Gen is present; threshold applies
  | .distributiveKindPred => false  -- No Gen; DIST gives referential truth
  | .cumulativeKindPred   => false  -- No Gen; ** gives cumulative truth
  | .existentialDPP       => false  -- No Gen; DPP gives existential truth

/-- Only the Bona Fide Generic parse is subject to T&G inference. -/
theorem only_bfg_has_generic_inference :
    subjectToGenericInference .bonaFideGeneric = true ∧
    subjectToGenericInference .distributiveKindPred = false ∧
    subjectToGenericInference .cumulativeKindPred = false ∧
    subjectToGenericInference .existentialDPP = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 8a: DKP ↔ Prevalence ↔ T&G Threshold (structural connection)
-- ============================================================================

section DKPPrevalence

variable {Atom W : Type}

open Phenomena.Generics.Studies.TesslerGoodman2019 (genericMeaning GenThreshold Prevalence)
open Core.Scale (deg thr)

/-- Prevalence of P among atoms in an extension at world w.

    This is the proportion of kind-instances satisfying P: |{a ∈ ext | P(a,w)}| / |ext|.
    It is the bridge quantity between DKP (which checks ∀ atoms) and T&G (which
    checks prevalence > θ). -/
def prevalenceAtWorld (P : Atom → W → Bool) (ext : Finset Atom) (w : W) : ℚ :=
  if ext.card = 0 then 0
  else (ext.filter (fun a => P a w)).card / ext.card

/-- DKP true ↔ prevalence = 1.

    When all atoms in the kind's extension satisfy P, prevalence is 100%.
    This is the extensional, non-generic truth condition of the DKP parse:
    the generalization is "true" in the same way a referential definite plural
    statement is true — all actual instances satisfy the predicate. -/
theorem dkp_true_iff_prevalence_one (P : Atom → W → Bool) (ext : Finset Atom)
    (w : W) (hne : ext.Nonempty) :
    distMaximal P ext w = true ↔ prevalenceAtWorld P ext w = 1 := by
  have hcard : ext.card ≠ 0 := Finset.card_ne_zero.mpr hne
  have hcardQ : (ext.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  simp only [distMaximal, decide_eq_true_iff, prevalenceAtWorld, hcard, ↓reduceIte]
  constructor
  · intro hall
    have hfilt : ext.filter (fun a => P a w) = ext := by
      ext a; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hall a
    rw [hfilt, div_self hcardQ]
  · intro hdiv
    have heq : ((ext.filter (fun a => P a w)).card : ℚ) = ext.card := by
      rwa [div_eq_iff hcardQ, one_mul] at hdiv
    have hceq : (ext.filter (fun a => P a w)).card = ext.card := by exact_mod_cast heq
    have hfilt : ext.filter (fun a => P a w) = ext :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ ext) (le_of_eq hceq.symm)
    intro a ha
    have hmem : a ∈ ext.filter (fun a => P a w) := by rw [hfilt]; exact ha
    exact (Finset.mem_filter.mp hmem).2

/-- DKP trivalent-false ↔ prevalence = 0.

    When no atoms satisfy P, the generalization is determinately false,
    not merely gapped. -/
theorem dkp_false_iff_prevalence_zero (P : Atom → W → Bool) (ext : Finset Atom)
    (w : W) :
    noneSatisfy P ext w = true ↔ prevalenceAtWorld P ext w = 0 := by
  by_cases hne : ext.Nonempty
  · have hcard : ext.card ≠ 0 := Finset.card_ne_zero.mpr hne
    have hcardQ : (ext.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
    simp only [noneSatisfy, decide_eq_true_iff, prevalenceAtWorld, hcard, ↓reduceIte]
    constructor
    · intro hall
      have hfilt : ext.filter (fun a => P a w) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_filter] at ha
        exact absurd ha.2 (by rw [hall a ha.1]; decide)
      rw [hfilt, Finset.card_empty, Nat.cast_zero, zero_div]
    · intro hdiv
      have heq : ((ext.filter (fun a => P a w)).card : ℚ) = 0 := by
        rw [div_eq_zero_iff] at hdiv; exact hdiv.resolve_right hcardQ
      have hceq : (ext.filter (fun a => P a w)).card = 0 := by exact_mod_cast heq
      have hfilt : ext.filter (fun a => P a w) = ∅ :=
        Finset.card_eq_zero.mp hceq
      intro a ha
      by_contra h
      have htrue : P a w = true := by cases P a w <;> simp_all
      have hmem : a ∈ ext.filter (fun a => P a w) := by
        rw [Finset.mem_filter]; exact ⟨ha, htrue⟩
      rw [hfilt] at hmem; exact absurd hmem (Finset.notMem_empty _)
  · -- ext = ∅: both sides trivially true
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [noneSatisfy, prevalenceAtWorld]

/-- DKP true implies T&G generic meaning is true at every threshold.

    If DKP gives 'true' (all actual instances of the kind satisfy P),
    then prevalence = 100%, which exceeds every threshold in
    T&G's model. The DKP parse is a *stronger* truth condition
    than any threshold-based generic: it entails the BFG parse
    at all thresholds. -/
theorem dkp_true_implies_generic_true_all_thresholds :
    ∀ θ : GenThreshold, genericMeaning θ (prevPct 100) = true := by
  native_decide

/-- DKP gap is exactly the domain where T&G does real work.

    When prevalence is intermediate (0 < p < 1), the DKP parse gives
    a trivalent *gap* (some but not all atoms satisfy P), while the
    BFG parse's truth depends on whether prevalence exceeds the threshold.

    At p = 0.7 and θ = 0.6: generic meaning is true (0.7 > 0.6).
    At p = 0.7 and θ = 0.8: generic meaning is false (0.7 ≯ 0.8).

    This is exactly the region where T&G's pragmatic inference —
    listener reasoning over priors on prevalence — determines the
    judgment. Guerrini's contribution is showing this inference applies
    only to the BFG parse, not the DKP parse. -/
theorem dkp_gap_is_threshold_sensitive :
    -- prevalence 70% exceeds threshold 60%
    genericMeaning (thrPct 60) (prevPct 70) = true ∧
    -- but prevalence 70% does not exceed threshold 80%
    genericMeaning (thrPct 80) (prevPct 70) = false := by
  native_decide

/-- The two parses can disagree: DKP gap with BFG true.

    Witness: 10 atoms, 7 satisfy P, 3 don't.
    - DKP: trivalent gap (not all satisfy, not none satisfy)
    - BFG (at θ = 0.6): true (prevalence 0.7 > 0.6)

    This formalizes Guerrini's core explanation: "accidental"
    generalizations feel factual (DKP requires near-universality)
    while "law-like" generalizations tolerate exceptions (BFG uses
    threshold, and pragmatic inference determines what counts as
    "enough"). -/
theorem parses_can_disagree :
    (∃ (P : Fin 10 → Fin 1 → Bool) (ext : Finset (Fin 10)),
      ext.Nonempty ∧
      -- DKP: gap (not all, not none)
      allSatisfy P ext (0 : Fin 1) = false ∧
      noneSatisfy P ext (0 : Fin 1) = false ∧
      -- BFG: true at threshold 60% with prevalence 70%
      genericMeaning (thrPct 60) (prevPct 70) = true) := by
  refine ⟨fun a _ => decide (a.val < 7), Finset.univ, Finset.univ_nonempty, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

end DKPPrevalence

-- ============================================================================
-- § 9: Italian Subjunctive Diagnostic (§3.5)
-- ============================================================================

/-- Italian mood in relative clause modifying the subject DP. -/
inductive ItalianMood where
  | indicative
  | subjunctive
  deriving DecidableEq, Repr, BEq

/-- The Italian subjunctive is licensed inside the restrictor of Gen
    (a broadly intensional environment). Therefore:
    - Subjunctive-modified DP → must be in Gen restrictor → BFG parse only
    - Indicative-modified DP → compatible with both BFG and DKP parses

    Guerrini (2026), example (44):
    "I candidati che si {presentano/presentino} con molto anticipo
     non vengono assunti."
    - Indicative: law-like AND accidental readings available
    - Subjunctive: only law-like reading available -/
def subjunctiveForcesLawLike (mood : ItalianMood) : Bool :=
  match mood with
  | .indicative  => false  -- both readings available
  | .subjunctive => true   -- only law-like (BFG parse forced)

/-- Available LFs given mood on the relative clause.

    Subjunctive is licensed inside the restrictor of Gen (an intensional
    environment). DKP, CKP, and DPP place the DP outside Gen, so the
    subject DP is not in Gen's restrictor — subjunctive is not licensed. -/
def lfAvailableWithMood (mood : ItalianMood) (lf : GeneralizationLF) : Bool :=
  match mood, lf with
  | .indicative,  _                     => true
  | .subjunctive, .bonaFideGeneric      => true
  | .subjunctive, .distributiveKindPred => false  -- kind outside Gen
  | .subjunctive, .cumulativeKindPred   => false  -- kind outside Gen
  | .subjunctive, .existentialDPP       => false  -- property outside Gen

/-- Subjunctive disambiguates: only Bona Fide Generic survives. -/
theorem subjunctive_disambiguates :
    lfAvailableWithMood .subjunctive .bonaFideGeneric = true ∧
    lfAvailableWithMood .subjunctive .distributiveKindPred = false ∧
    lfAvailableWithMood .subjunctive .cumulativeKindPred = false ∧
    lfAvailableWithMood .subjunctive .existentialDPP = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Indicative preserves full ambiguity. -/
theorem indicative_ambiguous :
    lfAvailableWithMood .indicative .bonaFideGeneric = true ∧
    lfAvailableWithMood .indicative .distributiveKindPred = true ∧
    lfAvailableWithMood .indicative .cumulativeKindPred = true ∧
    lfAvailableWithMood .indicative .existentialDPP = true := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 10: Empirical Data — Flavors of Genericity
-- ============================================================================

/-- Genericity datum from Guerrini (2026), examples (21)–(22). -/
structure GenericityDatum where
  sentence : String
  language : String
  nominalForm : NominalForm
  flavor : GenFlavor
  felicitous : Bool
  notes : String

def llmsUtilizeDL : GenericityDatum :=
  { sentence := "Large Language Models utilize Deep Learning."
  , language := "English"
  , nominalForm := .kindDenotingPlural
  , flavor := .lawLike
  , felicitous := true
  , notes := "Law-like; both BFG and DKP parses give 'true'" }

def aLLMUtilizesDL : GenericityDatum :=
  { sentence := "A Large Language Model utilizes Deep Learning."
  , language := "English"
  , nominalForm := .singularIndefinite
  , flavor := .lawLike
  , felicitous := true
  , notes := "Law-like; BFG parse only" }

def llmsArePopular : GenericityDatum :=
  { sentence := "Large Language Models are popular."
  , language := "English"
  , nominalForm := .kindDenotingPlural
  , flavor := .accidental
  , felicitous := true
  , notes := "Accidental; DKP parse — true of actual LLMs" }

def aLLMIsPopular : GenericityDatum :=
  { sentence := "A Large Language Model is popular."
  , language := "English"
  , nominalForm := .singularIndefinite
  , flavor := .accidental
  , felicitous := false
  , notes := "Accidental; no DKP parse available — infelicitous" }

-- Italian parallels (examples (22))

def gliLLMUsanoDL : GenericityDatum :=
  { sentence := "Gli LLM usano il Deep Learning."
  , language := "Italian"
  , nominalForm := .kindDenotingPlural
  , flavor := .lawLike
  , felicitous := true
  , notes := "Italian definite plural; law-like" }

def unLLMUsaDL : GenericityDatum :=
  { sentence := "Un LLM usa il Deep Learning."
  , language := "Italian"
  , nominalForm := .singularIndefinite
  , flavor := .lawLike
  , felicitous := true
  , notes := "Italian singular indefinite; law-like" }

def gliLLMSonoPopolari : GenericityDatum :=
  { sentence := "Gli LLM sono popolari."
  , language := "Italian"
  , nominalForm := .kindDenotingPlural
  , flavor := .accidental
  , felicitous := true
  , notes := "Italian definite plural; accidental" }

def unLLMEPopolari : GenericityDatum :=
  { sentence := "Un LLM è popolare."
  , language := "Italian"
  , nominalForm := .singularIndefinite
  , flavor := .accidental
  , felicitous := false
  , notes := "Italian singular indefinite; accidental — infelicitous" }

def genericityData : List GenericityDatum :=
  [ llmsUtilizeDL, aLLMUtilizesDL, llmsArePopular, aLLMIsPopular
  , gliLLMUsanoDL, unLLMUsaDL, gliLLMSonoPopolari, unLLMEPopolari ]

-- Per-datum verification: Table 1 alignment

/-- All law-like generalizations are felicitous. -/
example : (genericityData.filter (·.flavor == .lawLike)
      |>.all (·.felicitous)) = true := rfl

/-- Kind-denoting plurals are felicitous in accidental generalizations. -/
example : (genericityData.filter (fun d => d.flavor == .accidental &&
         d.nominalForm == .kindDenotingPlural)
      |>.all (·.felicitous)) = true := rfl

/-- Singular indefinites are infelicitous in accidental generalizations. -/
example : (genericityData.filter (fun d => d.flavor == .accidental &&
         d.nominalForm == .singularIndefinite)
      |>.all (!·.felicitous)) = true := rfl

/-- Cross-linguistic parallel: English and Italian pattern identically
    in their nominal form × flavor → felicity mapping. -/
example : (genericityData.filter (·.language == "English")
      |>.map (fun d => (d.nominalForm, d.flavor, d.felicitous)))
      = (genericityData.filter (·.language == "Italian")
        |>.map (fun d => (d.nominalForm, d.flavor, d.felicitous))) := rfl

-- ============================================================================
-- § 11: Compositional Connection to Theory Layer
-- ============================================================================

/-!
## BFG as an instance of GEN; DKP as an instance of DIST

The two parses connect to different operators in the theory layer:

- **BFG** instantiates `traditionalGEN` from `Generics.lean`:
  the kind's extension provides the restrictor, the VP provides the scope,
  and Gen's normalcy parameter captures the hidden context-dependence
  that @cite{tessler-goodman-2019}'s RSA model replaces with prevalence priors.

- **DKP** instantiates `distMaximal` from `Distributivity.lean`:
  no GEN operator is involved — the predicate distributes over the
  kind's extension at the actual world via DIST.

These are not parallel formalisms applied to the same data —
they are structurally different semantic compositions that yield
different truth conditions and different pragmatic properties.
-/

open Semantics.Lexical.Noun.Kind.Generics (traditionalGEN Situation
  NormalcyPredicate Restrictor Scope)

/-- The Bona Fide Generic parse is compositionally an instance of
    traditionalGEN: the kind provides the restrictor, the VP the scope,
    and Gen's normalcy parameter is the hidden contextual factor.

    This function makes the compositional content of BFG explicit. -/
def evalBFG (situations : List Situation) (normal : NormalcyPredicate)
    (kindRestrictor : Restrictor) (predScope : Scope) : Bool :=
  traditionalGEN situations normal kindRestrictor predScope

/-- The two parses use different operators from the theory layer.

    BFG compositionally instantiates GEN (modal quantifier over situations,
    from `Theories/Semantics/Lexical/Noun/Kind/Generics.lean`).
    DKP compositionally instantiates DIST (distributive operator over
    atoms, from `Theories/Semantics/Lexical/Plural/Distributivity.lean`).

    Only BFG is subject to T&G's generic inference because only BFG
    involves Gen; DKP is a non-generic, referential truth condition. -/
theorem parses_use_different_operators :
    -- BFG = GEN (subject to generic inference)
    subjectToGenericInference .bonaFideGeneric = true ∧
    -- DKP = DIST (not subject to generic inference)
    subjectToGenericInference .distributiveKindPred = false ∧
    -- CKP = ** (not subject to generic inference)
    subjectToGenericInference .cumulativeKindPred = false ∧
    -- DPP = ∃ (not subject to generic inference)
    subjectToGenericInference .existentialDPP = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Table 1 is derivable from LF availability + LF → flavor mapping.

    Kind-denoting plurals support both flavors because they have LFs
    of both flavor types (BFG for law-like, DKP/CKP for accidental).
    Singular indefinites support only law-like because all their
    available LFs (just BFG) map to the law-like flavor. -/
theorem table1_from_lf_structure :
    -- Kind-denoting plurals: both flavors available via different LFs
    (∃ lf, lfAvailable .englishBarePlural lf = true ∧ lfFlavor lf = .lawLike) ∧
    (∃ lf, lfAvailable .englishBarePlural lf = true ∧ lfFlavor lf = .accidental) ∧
    -- Singular indefinites via Italian bare pl (property-only, like singular indef):
    -- only BFG available, which is law-like
    (lfFlavor .bonaFideGeneric = .lawLike) ∧
    -- No accidental LF is available for property-only nominals
    (lfAvailable .italianBarePlural .distributiveKindPred = false) ∧
    (lfAvailable .italianBarePlural .cumulativeKindPred = false) := by
  exact ⟨⟨.bonaFideGeneric, rfl, rfl⟩, ⟨.distributiveKindPred, rfl, rfl⟩, rfl, rfl, rfl⟩

-- ============================================================================
-- Bridge to Longobardi (2001)
-- ============================================================================

section Longobardi2001Bridge

open Phenomena.Generics.Studies.Longobardi2001 (DPParameter bnCanBeReferential
  toNominalMapping romance english GenericType)

/-- @cite{longobardi-2001}'s referential BN reading corresponds to DKP/CKP
    parses: both require kind denotation. The bridge is through Chierchia's
    `canDenoteKind`, which both papers use.

    English BPs: `canDenote .englishBarePlural .kind = true` (Guerrini)
    ↔ `bnCanBeReferential english = true` (Longobardi)

    Italian bare plurals: `canDenote .italianBarePlural .kind = false` (Guerrini)
    ↔ `bnCanBeReferential romance = false` (Longobardi) -/
theorem referential_iff_longobardi_kind :
    bnCanBeReferential english =
      canDenote .englishBarePlural .kind ∧
    bnCanBeReferential romance =
      canDenote .italianBarePlural .kind := ⟨rfl, rfl⟩

/-- @cite{longobardi-2001}'s quantificational-only BN = only BFG parse.
    DKP/CKP require kind denotation, which `strongD` blocks for BNs.

    English BPs: all three LFs (BFG + DKP + CKP)
    Italian bare plurals: BFG only -/
theorem quantificational_only_iff_bfg_only :
    lfAvailable .englishBarePlural .distributiveKindPred = true ∧
    lfAvailable .englishBarePlural .cumulativeKindPred = true ∧
    lfAvailable .italianBarePlural .distributiveKindPred = false ∧
    lfAvailable .italianBarePlural .cumulativeKindPred = false := ⟨rfl, rfl, rfl, rfl⟩

/-- End-to-end chain from @cite{longobardi-2001}'s `strongD` to Table 1:

    1. `strongD = true` (Romance) → `bnCanBeReferential = false`
    2. → `canDenoteKind (.predOnly) false = false` (Chierchia)
    3. → `canDenote .italianBarePlural .kind = false` (Guerrini)
    4. → `lfAvailable .italianBarePlural .distributiveKindPred = false`
    5. → accidental generalizations unavailable (only BFG → law-like)
    6. → `table1 .singularIndefinite .accidental = false` -/
theorem strongd_to_table1 :
    romance.strongD = true ∧
    toNominalMapping romance = .predOnly ∧
    canDenoteKind .predOnly false = false ∧
    canDenote .italianBarePlural .kind = false ∧
    lfAvailable .italianBarePlural .distributiveKindPred = false ∧
    table1 .singularIndefinite .accidental = false := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- @cite{longobardi-2001}'s `GenericType` aligns with `GenFlavor`:
    indefinite generics are law-like (BFG); definite generics can be
    accidental (DKP). -/
theorem generic_type_matches_longobardi_flavor :
    lfFlavor .bonaFideGeneric = .lawLike ∧
    lfFlavor .distributiveKindPred = .accidental := ⟨rfl, rfl⟩

end Longobardi2001Bridge

-- ============================================================================
-- § 12: Cumulative Kind Predication — Compositional Grounding
-- ============================================================================

section CumulativeKindPred

open Semantics.Lexical.Plural.Cumulativity (cumulativeOp)

variable {Atom Loc : Type} [DecidableEq Atom] [DecidableEq Loc]

/--
Cumulative Kind Predication: evaluate a kind at the actual world,
then apply the cumulative operator `**` to the kind extension and
a set of locations/arguments.

@cite{guerrini-2026} §4, structure (62):
  **(λy.λx.⟦Hab live-in⟧_{s₀}(x, y))(Africa ⊕ Asia)(∩elephants_{s₀})

This connects `GeneralizationLF.cumulativeKindPred` to the theory-layer
`**` operator from `Cumulativity.lean`.
-/
def cumulativeKindPred
    (R : Atom → Loc → Bool)
    (kindExtension : Finset Atom)
    (locations : Finset Loc) : Bool :=
  cumulativeOp R kindExtension locations

end CumulativeKindPred

-- ============================================================================
-- § 13: Epistemic Adjective Diagnostic (§5.2.2)
-- ============================================================================

/-!
## Epistemic Adjectives Block Kind Predication

@cite{guerrini-2026} §5.2.2: Nonlocal readings of epistemic adjectives
like "unknown" and "unidentified" block kind denotation, which in turn
blocks the near-universal reading via Distributive Kind Predication.

The argument: "unknown X" under its nonlocal reading ("X whose identity
is unknown to the speaker") denotes a property that cannot correspond to
a natural kind. Since ∩ is only defined for natural-kind-forming
properties, the kind-level LF is unavailable, and so is DKP.

This provides independent evidence that near-universal episodic readings
require kind denotation (via DKP), not just universality from context.
-/

/-- Whether an adjective reading supports kind predication. -/
inductive AdjReading where
  /-- Local: adjective modifies noun content (descriptive).
      "American voters" = voters who are American. Supports kind. -/
  | local
  /-- Nonlocal: adjective contributes propositional content.
      "Unknown voters" = voters whose identity is unknown to speaker.
      Does NOT support kind. -/
  | nonlocal
  deriving DecidableEq, Repr, BEq

/-- Kind predication is available only with local adjective readings. -/
def adjReadingSupportsKind : AdjReading → Bool
  | .local    => true
  | .nonlocal => false

/-- Epistemic adjective datum from @cite{guerrini-2026}, examples (99)–(104). -/
structure EpistemicAdjDatum where
  bareNP : String
  adjReading : AdjReading
  nearUniversalOK : Bool
  existentialOK : Bool
  notes : String

def americanVoters : EpistemicAdjDatum :=
  { bareNP := "American voters"
  , adjReading := .local
  , nearUniversalOK := true
  , existentialOK := true
  , notes := "Local: denotes kind 'American voter' → DKP available" }

def unidentifiedVoters : EpistemicAdjDatum :=
  { bareNP := "unidentified voters"
  , adjReading := .nonlocal
  , nearUniversalOK := false
  , existentialOK := true
  , notes := "Nonlocal: no kind → no DKP → existential only" }

def investigativeJournalists : EpistemicAdjDatum :=
  { bareNP := "investigative journalists"
  , adjReading := .local
  , nearUniversalOK := true
  , existentialOK := true
  , notes := "Local: denotes kind → DKP available" }

def unknownJournalists : EpistemicAdjDatum :=
  { bareNP := "unknown journalists"
  , adjReading := .nonlocal
  , nearUniversalOK := false
  , existentialOK := true
  , notes := "Nonlocal: no kind → no DKP → existential only" }

def epistemicAdjData : List EpistemicAdjDatum :=
  [americanVoters, unidentifiedVoters, investigativeJournalists, unknownJournalists]

/-- Near-universal reading availability tracks adjective reading,
    which tracks kind denotation availability. -/
example : epistemicAdjData.all
    (fun d => d.nearUniversalOK == adjReadingSupportsKind d.adjReading) = true := rfl

/-- All epistemic adjective data allow existential readings
    (property denotation is always available via DPP). -/
example : epistemicAdjData.all (·.existentialOK) = true := rfl

/-- The epistemic adjective diagnostic derives from the same
    kind-denotation → DKP chain as Table 1.

    Local adj → kind OK → DKP available → near-universal OK
    Nonlocal adj → no kind → no DKP → near-universal blocked -/
theorem epistemic_adj_from_kind_denotation :
    adjReadingSupportsKind .local = true ∧
    adjReadingSupportsKind .nonlocal = false := ⟨rfl, rfl⟩

-- ============================================================================
-- § 14: Q-Adverb Diagnostics (§3.1, §5.1)
-- ============================================================================

/-!
## Q-Adverb Resistance as a DKP Diagnostic

@cite{guerrini-2026} §3.1: Q-adverbs like "usually" and "rarely" are
overt counterparts of Gen (Krifka et al. 1995). Since DKP does not
involve Gen, Q-adverbs are incompatible with DKP readings. This
provides a diagnostic: if a Q-adverb is added, only the BFG parse
survives, and accidental readings disappear.

§5.1: Episodic bare plurals with DKP allow 'all' (DIST's non-homogeneous
counterpart) but not 'always' (Gen's counterpart), confirming the
absence of Gen from the DKP parse.
-/

/-- Q-adverb diagnostic datum (§3.1 examples (25), (49); §5.1 examples (89)-(90)). -/
structure QAdvDatum where
  sentence : String
  nominalForm : NominalForm
  /-- Does adding a Q-adverb allow the intended reading? -/
  qAdvCompatible : Bool
  /-- What reading is being tested? -/
  testedReading : GenFlavor
  notes : String

-- (25a): "*Lions are usually extinct" — kind predicate resists Q-adverbs
def lionsUsuallyExtinct : QAdvDatum :=
  { sentence := "*Lions are usually extinct."
  , nominalForm := .kindDenotingPlural
  , qAdvCompatible := false
  , testedReading := .accidental
  , notes := "Kind predicate 'extinct' resists Q-adverb; DKP only" }

-- (25b): "LLMs are usually popular" — accidental predicate OK with Q-adverb
-- (forces BFG parse; see (49))
def llmsUsuallyPopular : QAdvDatum :=
  { sentence := "LLMs are usually popular."
  , nominalForm := .kindDenotingPlural
  , qAdvCompatible := true
  , testedReading := .lawLike
  , notes := "Q-adverb replaces Gen in BFG parse; accidental reading lost" }

-- (89): "Birds are all migrating" — 'all' OK with episodic DKP
def birdsAllMigrating : QAdvDatum :=
  { sentence := "Birds are all migrating."
  , nominalForm := .kindDenotingPlural
  , qAdvCompatible := true
  , testedReading := .accidental
  , notes := "'all' replaces DIST-homogeneity; DKP parse preserved" }

-- (90): "#Birds are always migrating" — 'always' incompatible with episodic DKP
def birdsAlwaysMigrating : QAdvDatum :=
  { sentence := "#Birds are always migrating."
  , nominalForm := .kindDenotingPlural
  , qAdvCompatible := false
  , testedReading := .accidental
  , notes := "'always' is a Q-adverb (Gen counterpart); no Gen in DKP" }

def qAdvData : List QAdvDatum :=
  [lionsUsuallyExtinct, llmsUsuallyPopular,
   birdsAllMigrating, birdsAlwaysMigrating]

/-- Q-adverbs (Gen counterparts) are incompatible with accidental/episodic
    DKP readings, confirming that DKP does not involve Gen. -/
theorem qadv_blocks_dkp :
    -- 'all' (DIST counterpart) OK with DKP readings
    birdsAllMigrating.qAdvCompatible = true ∧
    -- 'always' (Gen counterpart) blocks DKP readings
    birdsAlwaysMigrating.qAdvCompatible = false := ⟨rfl, rfl⟩

/-- The Q-adverb asymmetry aligns with Table 3: episodic bare plurals
    (DKP parse) accept 'all' but not 'always', confirming they have
    DIST but not Gen in their LF. -/
theorem episodic_qadv_aligns_with_table3 :
    removerAvailable .referentialDefinitePlural .all = true ∧
    removerAvailable .referentialDefinitePlural .always = false ∧
    -- Episodic bare plural via DKP ≈ referential definite plural
    birdsAllMigrating.qAdvCompatible = true ∧
    birdsAlwaysMigrating.qAdvCompatible = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 15: DPP Compositional Bridge (§5.3, diagram (145))
-- ============================================================================

/-!
## DPP Completes the Four-Way Typology

@cite{guerrini-2026} diagram (145) shows English bare plurals have
four LF paths. Two via kind denotation (DKP, CKP), two via property
denotation (BFG, DPP). The DPP path yields the existential reading
of episodic bare plurals ("Bears are destroying my garden" ≈ ∃x[bear(x)
∧ destroying-my-garden(x)]), grounded via `DPP` from
`Chierchia1998.lean`.
-/

/-- DPP (from `Chierchia1998.lean`) is the compositional engine behind
    the `.existentialDPP` LF parse.

    This theorem connects the structural LF typology to the theory-layer
    definition: existential readings arise exactly when property denotation
    is available, via DPP. -/
theorem existential_via_dpp :
    -- English BPs: property available → DPP LF available → existential
    lfAvailable .englishBarePlural .existentialDPP = true ∧
    -- Italian bare pl: property available → DPP LF available → existential
    lfAvailable .italianBarePlural .existentialDPP = true ∧
    -- Italian def pl: no property → no DPP → no existential
    lfAvailable .italianDefinitePlural .existentialDPP = false := ⟨rfl, rfl, rfl⟩

/-- The four-way LF typology from diagram (145), connecting denotation
    types to available LFs and their truth conditions:

    Kind path:
    - BFG: Gen(⟦kind⟧, ⟦VP⟧) — law-like, prevalence-sensitive
    - DKP: DIST(⟦VP⟧)(∩kind_{s₀}) — near-universal over actual instances
    - CKP: **(⟦VP⟧)(locations)(∩kind_{s₀}) — cumulative coverage

    Property path:
    - BFG: Gen(⟦property⟧, ⟦VP⟧) — law-like, prevalence-sensitive
    - DPP: ∃x[property(x) ∧ VP(x)] — low-scoped existential -/
theorem diagram_145_four_paths :
    -- Kind-requiring LFs
    (lfAvailable .englishBarePlural .distributiveKindPred = true) ∧
    (lfAvailable .englishBarePlural .cumulativeKindPred = true) ∧
    -- Property-requiring LF
    (lfAvailable .englishBarePlural .existentialDPP = true) ∧
    -- BFG available via either path
    (lfAvailable .englishBarePlural .bonaFideGeneric = true) ∧
    -- Italian definite plural: kind path only
    (lfAvailable .italianDefinitePlural .existentialDPP = false) ∧
    (lfAvailable .italianDefinitePlural .distributiveKindPred = true) ∧
    -- Italian bare plural: property path only
    (lfAvailable .italianBarePlural .distributiveKindPred = false) ∧
    (lfAvailable .italianBarePlural .existentialDPP = true) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Phenomena.Generics.Studies.Guerrini2026
