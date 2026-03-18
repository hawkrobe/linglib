import Linglib.Theories.Semantics.Lexical.Noun.Kind.Chierchia1998
import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Theories.Semantics.Lexical.Plural.Cumulativity
import Linglib.Theories.Semantics.Composition.Tree
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

/-- Computable kind extension from a Bool-valued membership test.
    Use this for finite verification instead of the noncomputable
    `kindExtensionFinset`, which requires Classical.dec for Set membership.

    Example usage:
    ```
    def lionMember : World → Animal → Bool
      | _, .simba => true | _, .nala => true | _, _ => false
    def lionExt := kindExtensionOfBool lionMember
    ```
    Then pass `lionExt` directly to `distributiveKindPred`. -/
def kindExtensionOfBool [Fintype Atom] (member : W → Atom → Bool) (w : W) : Finset Atom :=
  Finset.univ.filter (member w)

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

/-- Both generalization and episodic disambiguation derive from the same
    kind-denotation chain:
    def pl can denote kind → DKP available → accidental / near-universal;
    bare pl cannot → no DKP → no accidental / no near-universal. -/
theorem italian_disambiguation_from_kind_denotation :
    canDenote .italianDefinitePlural .kind = true ∧
    lfAvailable .italianDefinitePlural .distributiveKindPred = true ∧
    canDenote .italianBarePlural .kind = false ∧
    lfAvailable .italianBarePlural .distributiveKindPred = false ∧
    -- Additionally, bare pl has property → DPP → existential
    canDenote .italianBarePlural .property = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

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

/-- Table 1 is derivable from LF availability + LF → flavor mapping.

    Kind-denoting plurals support both flavors because they have LFs
    of both flavor types (BFG for law-like, DKP/CKP for accidental).
    Singular indefinites support only law-like because all their
    available LFs (just BFG) map to the law-like flavor. -/
theorem table1_from_lf_structure :
    -- Kind-denoting plurals: both flavors available via different LFs
    (∃ lf, lfAvailable .englishBarePlural lf = true ∧ lfFlavor lf = .lawLike) ∧
    (∃ lf, lfAvailable .englishBarePlural lf = true ∧ lfFlavor lf = .accidental) ∧
    -- Property-only nominals (Italian bare pl, singular indef — by different
    -- mechanisms: Italian bare pl is [-arg,+pred] without D; singular indef
    -- has ∩ undefined for singular count nouns): only BFG available → law-like
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
-- § 12a: Gen Does Not Encode Cumulativity (§4.2)
-- ============================================================================

/-!
## Cumulativity Comes from ** (CKP), Not from Gen

@cite{guerrini-2026} §4.2: Gen itself does not encode cumulativity. Evidence:

1. **Q-adverb test**: Adding Q-adverbs (which replace Gen) removes
   cumulative readings. "Wugs are always/often/typically black, white,
   green, and red" — only the "all four colors simultaneously" reading
   survives, not the cumulative "each wug is one color" reading (ex. (69)).

2. **Italian subjunctive test**: Forcing the BFG parse (kind in Gen's
   restrictor) removes cumulative readings. "I linguisti che si occupino
   di semantica..." — only distributive, not cumulative (ex. (71)).

This means cumulative readings must arise from the CKP LF (which uses **
independently of Gen), not from a cumulative BFG LF.
-/

/-- Q-adverbs remove cumulative readings (§4.2, ex. (68)-(69)):
    forcing BFG parse eliminates cumulativity. -/
structure CumulativityDiagnosticDatum where
  sentence : String
  hasCumulative : Bool
  hasDistributive : Bool
  notes : String

def wugsColors : CumulativityDiagnosticDatum :=
  { sentence := "Wugs are black, white, green, and red."
  , hasCumulative := true
  , hasDistributive := true
  , notes := "ex. (68a); cumulative (each wug one color) and distributive (each wug all colors)" }

def wugsQAdvColors : CumulativityDiagnosticDatum :=
  { sentence := "Wugs are always/often/typically black, white, green, and red."
  , hasCumulative := false
  , hasDistributive := true
  , notes := "ex. (69); Q-adverb forces BFG → only distributive survives" }

/-- Q-adverbs kill cumulative readings, confirming that cumulative
    readings arise from ** (CKP) and not from Gen. -/
theorem qadv_kills_cumulativity :
    wugsColors.hasCumulative = true ∧
    wugsQAdvColors.hasCumulative = false ∧
    -- Both retain the distributive/simultaneous reading
    wugsColors.hasDistributive = true ∧
    wugsQAdvColors.hasDistributive = true := ⟨rfl, rfl, rfl, rfl⟩

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

-- (25a): "*Lions are usually extinct" — direct kind predicate resists Q-adverbs.
-- NB: 'extinct' is a DIRECT kind predicate — it applies to the kind qua kind,
-- not distributively to individual lions. This is distinct from Guerrini's
-- Distributive Kind Predication (DKP), which distributes over atoms via DIST.
-- Q-adverb resistance follows from the absence of Gen in direct kind predication
-- (Cohen 2001, §3.6 of the paper). `testedReading` is `.lawLike` here because
-- the test sentence probes whether Gen (which Q-adverbs replace) is present;
-- it is not, hence the infelicity.
def lionsUsuallyExtinct : QAdvDatum :=
  { sentence := "*Lions are usually extinct."
  , nominalForm := .kindDenotingPlural
  , qAdvCompatible := false
  , testedReading := .lawLike
  , notes := "Direct kind predicate — applies to kind, not individuals; Gen absent → Q-adverb blocked" }

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
-- § 14a: Quantificational Variability Effects (§1, §3.1, §5.1)
-- ============================================================================

/-!
## QVE Absence as a DKP Diagnostic

@cite{guerrini-2026} §1, §3.1, §5.1: Quantificational Variability Effects
(QVEs) are the hallmark of generic quantification. A sentence like "Birds
rarely fly" (= QVE with 'rarely') is interpreted as "few birds fly" — the
Q-adverb varies the quantificational force. QVEs arise when Gen is present,
because Q-adverbs are overt counterparts of Gen.

Key fact: episodic bare plurals lack QVEs (examples (8), (90), (92)):
- "Birds are rarely migrating" ≉ "Few birds are migrating"
- "Birds are always migrating" does NOT yield episodic QVE

This absence is predicted by the DKP analysis: no Gen → no Q-adverb slot
→ no QVE. On the BFG analysis, QVEs would be expected but don't appear.
-/

/-- Whether a given LF parse supports Quantificational Variability Effects.

    QVEs arise only when Gen is present (Gen is the covert Q-adverb that
    overt Q-adverbs like 'usually', 'rarely' replace). -/
def supportsQVE (lf : GeneralizationLF) : Bool :=
  match lf with
  | .bonaFideGeneric      => true   -- Gen present → QVE possible
  | .distributiveKindPred => false  -- no Gen → no QVE
  | .cumulativeKindPred   => false  -- no Gen → no QVE
  | .existentialDPP       => false  -- no Gen → no QVE

/-- Only BFG supports QVEs. DKP's absence of QVEs is a direct consequence
    of not having Gen in the LF. Examples (8), (90), (92) in the paper. -/
theorem only_bfg_supports_qve :
    supportsQVE .bonaFideGeneric = true ∧
    supportsQVE .distributiveKindPred = false ∧
    supportsQVE .cumulativeKindPred = false ∧
    supportsQVE .existentialDPP = false := ⟨rfl, rfl, rfl, rfl⟩

/-- QVE absence aligns with Q-adverb incompatibility: both are
    consequences of the same structural fact (no Gen in DKP). -/
theorem qve_absence_matches_qadv_incompatibility :
    -- DKP has no QVEs
    supportsQVE .distributiveKindPred = false ∧
    -- DKP is not subject to generic inference
    subjectToGenericInference .distributiveKindPred = false ∧
    -- DKP is an accidental flavor (no Gen)
    lfFlavor .distributiveKindPred = .accidental := ⟨rfl, rfl, rfl⟩

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

-- ============================================================================
-- § 16: Habituality and the Two LF Structures (§3.4)
-- ============================================================================

/-!
## The Role of Hab in Both LF Structures

@cite{guerrini-2026} §3.4: The VP in habitual sentences involves a habitual
aspect operator **Hab** (formalized in `Theories/Semantics/Lexical/Verb/Habituals.lean`
as `traditionalHAB`). On the "habituality is genericity" view
(@cite{chierchia-1995}, @cite{chierchia-1998}), Hab IS Gen applied to situations
involving a single individual. On the Dobrovie-Sorin (2001) view, Hab is a
distinct operator below Gen.

Either way, the paper's structural ambiguity holds. The two LF structures
(41a) and (41b)/(42b) share the same "low part" (⟦Hab VP⟧) but differ in
what appears ABOVE it:

- **(41a) BFG**: Gen(kind, ⟦Hab VP⟧) — Gen binds the kind's world variable
- **(41b) DKP**: DIST(⟦Hab VP⟧)(kind_{s₀}) — kind evaluated at actual world

For episodic sentences ("Birds are migrating"), there is no Hab at all —
the VP is evaluated directly at s₀. DKP still applies (DIST over kind
extension), but BFG requires Hab/Gen to be present. This is why episodic
bare plurals get near-universal readings without generic quantification.
-/

/-- VP aspect: habitual or episodic.

    Habitual VPs involve the Hab operator (see `Habituals.lean`).
    Episodic VPs are evaluated directly at the world of evaluation. -/
inductive VPAspect where
  | habitual   -- ⟦Hab VP⟧: habitual/generic aspect
  | episodic   -- ⟦VP⟧_{s₀}: episodic aspect, evaluated at actual world
  deriving DecidableEq, Repr, BEq

/-- Which LFs are compatible with which aspect.

    BFG requires Gen, which in turn requires either Hab or an overt Q-adverb
    to provide the quantificational structure. In episodic sentences (no Hab,
    no Q-adverb), BFG is unavailable — only DKP/CKP/DPP survive. -/
def lfCompatibleWithAspect (asp : VPAspect) (lf : GeneralizationLF) : Bool :=
  match asp, lf with
  | .habitual, _                     => true   -- all LFs OK with Hab
  | .episodic, .bonaFideGeneric      => false  -- Gen requires Hab or Q-adverb
  | .episodic, .distributiveKindPred => true   -- DIST(VP)(kind_{s₀})
  | .episodic, .cumulativeKindPred   => true   -- **(VP)(locs)(kind_{s₀})
  | .episodic, .existentialDPP       => true   -- ∃x[P(x) ∧ VP(x)]

/-- In episodic sentences, BFG is unavailable — only DKP/CKP/DPP. -/
theorem episodic_no_bfg :
    lfCompatibleWithAspect .episodic .bonaFideGeneric = false ∧
    lfCompatibleWithAspect .episodic .distributiveKindPred = true ∧
    lfCompatibleWithAspect .episodic .cumulativeKindPred = true ∧
    lfCompatibleWithAspect .episodic .existentialDPP = true := ⟨rfl, rfl, rfl, rfl⟩

/-- This explains the episodic asymmetry (§5):
    - Bare plurals in episodics: DKP available → near-universal ✓
    - Singular indefinites in episodics: no DKP, no BFG (episodic) → only ∃

    The singular indefinite chain goes through ∩ being undefined for
    singular count nouns (`downDefinedFor`), NOT through the Italian
    bare plural's [-arg] parameter (which is a different mechanism). -/
theorem episodic_kind_plural_advantage :
    -- Kind-denoting plural: DKP available in episodic
    lfCompatibleWithAspect .episodic .distributiveKindPred = true ∧
    canDenote .englishBarePlural .kind = true ∧
    -- Singular indefinite: ∩ undefined for singular count → no kind denotation
    downDefinedFor .count false = false ∧
    -- Episodic: no Gen/Hab → no BFG
    lfCompatibleWithAspect .episodic .bonaFideGeneric = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 17: Singular Kind Terms Diverge from Plural Kind Terms (§6.2)
-- ============================================================================

/-!
## Singular Kinds Cannot Support Accidental or Cumulative Readings

@cite{guerrini-2026} §6.2: Singular kind terms ("the dodo", "the madrigal")
differ strikingly from plural kind terms ("dodos", "madrigals"):

1. Kind predication OK for both ("The dodo is extinct" / "Dodos are extinct")
2. Genericity + QVE OK for singular kinds ("The lion rarely has a mane")
3. **Accidental readings unavailable** for singular kinds
4. **Cumulative readings unavailable** for singular kinds

This follows from treating singular kinds as atomic (following
@cite{barker-1992}, @cite{schwarzschild-1996}, @cite{dayal-2004}).
DIST does not apply to atoms (only to pluralities), so DKP is unavailable.
The cumulative operator ** similarly requires pluralities.
-/

/-- Number of a kind-denoting term. -/
inductive KindTermNumber where
  | singular  -- "the dodo", "the madrigal"
  | plural    -- "dodos", "madrigals", "LLMs"
  deriving DecidableEq, Repr, BEq

/-- Singular kind terms are atomic — DIST and ** do not apply.
    Only BFG is available (kind enters Gen restrictor). -/
def singularKindLFAvailable (lf : GeneralizationLF) : Bool :=
  match lf with
  | .bonaFideGeneric      => true   -- kind in Gen restrictor: OK
  | .distributiveKindPred => false  -- DIST requires plurality: blocked
  | .cumulativeKindPred   => false  -- ** requires plurality: blocked
  | .existentialDPP       => false  -- singular kinds are not properties

/-- Singular kind terms support only law-like readings. -/
theorem singular_kind_law_like_only :
    singularKindLFAvailable .bonaFideGeneric = true ∧
    singularKindLFAvailable .distributiveKindPred = false ∧
    singularKindLFAvailable .cumulativeKindPred = false ∧
    singularKindLFAvailable .existentialDPP = false := ⟨rfl, rfl, rfl, rfl⟩

/-- Singular kind divergence datum from §6.2, examples (133)–(136). -/
structure SingularKindDivergenceDatum where
  sentence : String
  kindTermNumber : KindTermNumber
  accidentalOK : Bool
  cumulativeOK : Bool
  notes : String

def madrigalPopularSg : SingularKindDivergenceDatum :=
  { sentence := "The madrigal is popular."
  , kindTermNumber := .singular
  , accidentalOK := false
  , cumulativeOK := false
  , notes := "Only law-like: the form is inherently popular" }

def madrigalPopularPl : SingularKindDivergenceDatum :=
  { sentence := "Madrigals are popular."
  , kindTermNumber := .plural
  , accidentalOK := true
  , cumulativeOK := false
  , notes := "Also accidental via DKP: actual madrigals happen to be popular" }

def wugColorsSg : SingularKindDivergenceDatum :=
  { sentence := "The wug is white, green, black, and yellow."
  , kindTermNumber := .singular
  , accidentalOK := false
  , cumulativeOK := false
  , notes := "Singular kind is atomic — DIST/CKP inapplicable; only the 'all four colors' reading (direct predication)" }

def wugColorsPl : SingularKindDivergenceDatum :=
  { sentence := "Wugs are white, green, black, and yellow."
  , kindTermNumber := .plural
  , accidentalOK := true
  , cumulativeOK := true
  , notes := "Cumulative available: each wug is one color" }

def singularKindDivergenceData : List SingularKindDivergenceDatum :=
  [madrigalPopularSg, madrigalPopularPl, wugColorsSg, wugColorsPl]

/-- Singular kind terms lack accidental and cumulative readings;
    plural kind terms support both. -/
theorem singular_plural_divergence :
    (singularKindDivergenceData.filter (·.kindTermNumber == .singular)
      |>.all (!·.accidentalOK)) = true ∧
    (singularKindDivergenceData.filter (·.kindTermNumber == .singular)
      |>.all (!·.cumulativeOK)) = true ∧
    (singularKindDivergenceData.filter (·.kindTermNumber == .plural)
      |>.all (·.accidentalOK)) = true := ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- § 18: Greenberg Data — Temporally Modified Sentences (§3.7)
-- ============================================================================

/-!
## Greenberg (2002, 2004, 2007): Further Evidence for DKP

@cite{guerrini-2026} §3.7: @cite{greenberg-2002} @cite{greenberg-2004}
@cite{greenberg-2007} presented data teasing apart bare plurals from
singular indefinites in accidentally-flavored generalizations.

**Temporally modified sentences** (@cite{greenberg-2004}): "Italian restaurants
are closed today" can be true accidentally (national holiday). The singular
"An Italian restaurant is closed today" requires a law-like link.

**"Extremely unnatural kinds"** (@cite{greenberg-2007}): "Norwegian students
with names ending in 's' wear thick green socks" — true via DKP (actual
students happen to), but the singular is infelicitous (no law-like link).
-/

/-- Greenberg datum from @cite{guerrini-2026} §3.7. -/
structure GreenbergDatum where
  sentence : String
  nominalForm : NominalForm
  accidentalOK : Bool
  lawLikeOK : Bool
  notes : String

def italianRestaurantsPl : GreenbergDatum :=
  { sentence := "Italian restaurants are closed today."
  , nominalForm := .kindDenotingPlural
  , accidentalOK := true
  , lawLikeOK := true
  , notes := "ex. (50a); from Greenberg (2004); both readings for bare plural" }

def italianRestaurantSg : GreenbergDatum :=
  { sentence := "An Italian restaurant is closed today."
  , nominalForm := .singularIndefinite
  , accidentalOK := false
  , lawLikeOK := true
  , notes := "ex. (50b); from Greenberg (2004); only law-like for singular indef" }

def norwegianStudentsPl : GreenbergDatum :=
  { sentence := "Norwegian students with names ending in 's' wear thick green socks."
  , nominalForm := .kindDenotingPlural
  , accidentalOK := true
  , lawLikeOK := false
  , notes := "ex. (51a); from Greenberg (2007); accidental only (no law-like link)" }

def norwegianStudentSg : GreenbergDatum :=
  { sentence := "A Norwegian student with a name ending in 's' wears thick green socks."
  , nominalForm := .singularIndefinite
  , accidentalOK := false
  , lawLikeOK := false
  , notes := "ex. (51b); from Greenberg (2007); infelicitous (no DKP, no link for BFG)" }

def greenbergData : List GreenbergDatum :=
  [italianRestaurantsPl, italianRestaurantSg, norwegianStudentsPl, norwegianStudentSg]

/-- Bare plurals support accidental readings; singular indefinites do not. -/
theorem greenberg_accidental_asymmetry :
    (greenbergData.filter (·.nominalForm == .kindDenotingPlural)
      |>.all (·.accidentalOK)) = true ∧
    (greenbergData.filter (·.nominalForm == .singularIndefinite)
      |>.all (!·.accidentalOK)) = true := ⟨rfl, rfl⟩

-- ============================================================================
-- § 19: Episodic Homogeneity Removal (§5.1)
-- ============================================================================

/-!
## Homogeneity in Episodic Bare Plurals

@cite{guerrini-2026} §5.1: Near-universal episodic readings ("Birds are
migrating") arise from DKP — DIST over the kind extension at s₀. Since
there is no Gen in this LF:

- 'all' removes homogeneity (targets DIST): "Birds are all migrating" ✓
- 'always' does NOT apply (no Gen to target): "#Birds are always migrating"
  forces a habitual/generic reparse, not an episodic reading.

This is a direct consequence of Table 3 (§4): episodic DKP has
DIST-homogeneity but no Gen-homogeneity.
-/

/-- Episodic homogeneity removal datum. -/
structure EpisodicHomogeneityDatum where
  sentence : String
  remover : HomogeneityRemover
  episodicOK : Bool
  notes : String

def birdsAllMigratingEp : EpisodicHomogeneityDatum :=
  { sentence := "Birds are all migrating."
  , remover := .all
  , episodicOK := true
  , notes := "'all' removes DIST homogeneity; episodic maintained" }

def birdsAlwaysMigratingEp : EpisodicHomogeneityDatum :=
  { sentence := "Birds are always migrating."
  , remover := .always
  , episodicOK := false
  , notes := "Forces habitual/law-like reading; episodic lost" }

def studentsAllScaredEp : EpisodicHomogeneityDatum :=
  { sentence := "Students are all scared."
  , remover := .all
  , episodicOK := true
  , notes := "'all' removes DIST homogeneity; stage-level episodic" }

def studentsAlwaysScaredEp : EpisodicHomogeneityDatum :=
  { sentence := "Students are always scared."
  , remover := .always
  , episodicOK := false
  , notes := "Forces generic reading; not episodic" }

def episodicHomogeneityData : List EpisodicHomogeneityDatum :=
  [birdsAllMigratingEp, birdsAlwaysMigratingEp,
   studentsAllScaredEp, studentsAlwaysScaredEp]

/-- In episodic DKP, 'all' preserves the episodic reading but 'always'
    forces a generic reparse. DIST but no Gen → only 'all' applies. -/
theorem episodic_all_not_always :
    (episodicHomogeneityData.filter (·.remover == .all)
      |>.all (·.episodicOK)) = true ∧
    (episodicHomogeneityData.filter (·.remover == .always)
      |>.all (!·.episodicOK)) = true := ⟨rfl, rfl⟩

/-- Derives from Table 3: episodic DKP has DIST-homogeneity
    (removable by 'all') but no Gen-homogeneity ('always' vacuous). -/
theorem episodic_homogeneity_from_table3 :
    hasHomogeneitySource .referentialDefinitePlural .dist = true ∧
    hasHomogeneitySource .referentialDefinitePlural .gen = false ∧
    removesHomogeneity .all .dist = true ∧
    removesHomogeneity .always .dist = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 20: Bridge to Homogeneity and Non-Maximality (§5.1, §5.2, §6.1)
-- ============================================================================

/-!
## DKP Inherits Homogeneity and Non-Maximality from DIST

@cite{guerrini-2026} §5.1, §6.1: The near-universal reading from Distributive
Kind Predication is **homogeneous** and **non-maximal**, just like referential
definite plurals. This follows directly from DKP being compositionally
DIST applied to the kind extension — the trivalent truth conditions are
inherited, not stipulated.

This connects to the theory-neutral homogeneity data in
`Phenomena/Plurals/Homogeneity.lean` (@cite{kriz-2015} @cite{kriz-spector-2021})
and non-maximality data in `Phenomena/Plurals/NonMaximality.lean`.

The paper's examples (88)–(90) make this explicit:
- "Birds are migrating" — possibly non-maximal, ∼ ∀ (DKP + homogeneity)
- "Birds are not migrating" — possibly non-maximal, ∼ ¬∃ (negated homogeneity)
- "Birds are all migrating" — maximal, ∼ ∀ ('all' removes DIST homogeneity)
- "#Birds are always migrating" — forces generic reparse (Gen absent)

These are exactly the predictions of `distributiveKindPredTV` (§2) inheriting
`pluralTruthValue` from `Distributivity.lean`.
-/

/-- DKP truth value is computed via DIST (`pluralTruthValue`), so it
    inherits the homogeneity gap from referential definite plurals.

    This is the formal bridge between Guerrini's analysis and the
    Križ & Spector homogeneity theory: the same trivalent operator
    that gives definite plurals their characteristic behavior also
    gives kind-denoting plurals their non-maximal, exception-tolerant
    readings. The parallel is not stipulated — it's structural. -/
theorem dkp_homogeneity_from_dist {Atom W : Type} [DecidableEq Atom] [Fintype Atom]
    (kindExtension : W → Finset Atom) (P : Atom → W → Bool) (s₀ : W) :
    distributiveKindPredTV kindExtension P s₀ = pluralTruthValue P (kindExtension s₀) s₀ := rfl

-- ============================================================================
-- §21  Compositional Tree Demo: BFG vs DKP vs DPP
-- ============================================================================

/-!
## Compositional Trees: Two LF Parses Evaluated End-to-End

@cite{guerrini-2026} structures (29), (30), (105b)

Demonstrates that the BFG and DKP parses of "Lions hunt" can be represented
as `Tree Unit String` values and evaluated via the existing `interp` machinery,
with covert operators (Gen, DIST, DPP) as lexicon entries.

### The scenario

Three lions: Simba (hunts), Nala (hunts), Mufasa (doesn't hunt).

- **BFG** parse: Gen(lion, hunt) — "generally, lions hunt" → **true**
  (2 out of 3 lions hunt; the generic quantifier tolerates exceptions)
- **DKP** parse: DIST(hunt)(∩lions_{s₀}) — "all actual lions hunt" → **false**
  (Mufasa doesn't hunt; DIST requires universality)
- **DPP** parse: DPP(lion, hunt) — "some lion hunts" → **true**
  (existential; at least one lion hunts)

This demonstrates the core of @cite{guerrini-2026}: the same surface sentence
"Lions hunt" has two structurally distinct LFs that can **disagree** in
truth value.
-/

section CompositionalTreeDemo

open Semantics.Montague
open Semantics.Composition.Tree
open Semantics.Lexical.CovertQuantifier (genThreshold dist dpp)
open Core.Tree

/-- Demo entity domain: three individual lions plus the lion-kind
    (the maximal sum ∩lions_{s₀}, treated as a fourth entity). -/
inductive DemoEntity where
  | simba | nala | mufasa | lionKind
  deriving DecidableEq, Repr

instance : BEq DemoEntity := ⟨fun a b => decide (a = b)⟩

private def demoModel : Model :=
  { Entity := DemoEntity, decEq := inferInstance }

private def demoAtoms : List DemoEntity := [.simba, .nala, .mufasa]

/-- Mereological decomposition: lionKind → its atoms, atoms → self. -/
private def atomsOf : DemoEntity → List DemoEntity
  | .lionKind => [.simba, .nala, .mufasa]
  | x => [x]

/-- Lexicon: overt words + covert operators from reusable constructors.

    Gen, DIST, DPP are instantiated from theory-layer constructors
    (`genThreshold`, `dist`, `dpp`) rather than
    being defined ad hoc. -/
private def guerriniLex : Lexicon demoModel := fun s =>
  match s with
  | "lion"   => some ⟨.e ⇒ .t, fun x => match x with
      | .simba | .nala | .mufasa => true | .lionKind => false⟩
  | "hunt"   => some ⟨.e ⇒ .t, fun x => match x with
      | .simba | .nala => true | .mufasa | .lionKind => false⟩
  | "∩lions" => some ⟨.e, DemoEntity.lionKind⟩
  | "Gen"    => some (genThreshold demoModel demoAtoms 2 3)
  | "DIST"   => some (dist demoModel atomsOf)
  | "DPP"    => some (dpp demoModel demoAtoms)
  | _        => none

private def g₀ : Semantics.Montague.Variables.Assignment demoModel :=
  fun _ => DemoEntity.simba

/-- BFG parse: Gen(lion, hunt) — @cite{guerrini-2026}, structure (29). -/
private def bfgTree : Tree Unit String :=
  .bin (.bin (.leaf "Gen") (.leaf "lion")) (.leaf "hunt")

/-- DKP parse: DIST(hunt)(∩lions) — @cite{guerrini-2026}, structure (30). -/
private def dkpTree : Tree Unit String :=
  .bin (.leaf "∩lions") (.bin (.leaf "DIST") (.leaf "hunt"))

/-- DPP parse: DPP(lion, hunt) — @cite{guerrini-2026}, structure (105b). -/
private def dppTree : Tree Unit String :=
  .bin (.bin (.leaf "DPP") (.leaf "lion")) (.leaf "hunt")

/-- The three parses disagree: same surface sentence, different truth values.

    BFG: true  — Gen tolerates exceptions (2/3 lions hunt)
    DKP: false — DIST requires all atoms (Mufasa doesn't hunt)
    DPP: true  — ∃ requires at least one (Simba hunts) -/
theorem three_parses_disagree :
    evalTree guerriniLex g₀ bfgTree = some true ∧
    evalTree guerriniLex g₀ dkpTree = some false ∧
    evalTree guerriniLex g₀ dppTree = some true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- When all lions hunt, BFG and DKP agree: both true. -/
theorem all_hunt_agreement :
    let lexAll : Lexicon demoModel := fun s =>
      match s with
      | "lion"   => some ⟨.e ⇒ .t, fun x => match x with
          | .simba | .nala | .mufasa => true | .lionKind => false⟩
      | "hunt"   => some ⟨.e ⇒ .t, fun x => match x with
          | .simba | .nala | .mufasa => true | .lionKind => false⟩
      | "∩lions" => some ⟨.e, DemoEntity.lionKind⟩
      | "Gen"    => some (genThreshold demoModel demoAtoms 2 3)
      | "DIST"   => some (dist demoModel atomsOf)
      | _        => none
    evalTree lexAll g₀ bfgTree = some true ∧
    evalTree lexAll g₀ dkpTree = some true := by
  constructor <;> native_decide

end CompositionalTreeDemo

end Phenomena.Generics.Studies.Guerrini2026
