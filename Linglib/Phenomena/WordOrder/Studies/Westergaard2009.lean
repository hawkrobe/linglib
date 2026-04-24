import Linglib.Phenomena.WordOrder.Typology
import Linglib.Phenomena.WordOrder.SubjectAuxInversion
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic
import Linglib.Theories.Syntax.Minimalism.HeadMovement.GermanicV2
import Linglib.Theories.Syntax.HPSG.Inversion
import Linglib.Features.InformationStructure
import Linglib.Fragments.Norwegian.V2
import Linglib.Fragments.English.V2
import Linglib.Fragments.English.Typology
import Linglib.Fragments.German.V2
import Linglib.Fragments.German.Typology
import Linglib.Fragments.Danish.V2

/-!
# Westergaard (2009): Micro-Cues, Information Structure, and Economy
@cite{westergaard-2009}

Marit Westergaard. *The Acquisition of Word Order: Micro-Cues, Information
Structure, and Economy.* Linguistik Aktuell/Linguistics Today 145.
John Benjamins, 2009.

## Core Claim

V2 is not a single parameter. It decomposes into **micro-parameters**:
one per clause-type head in a split-CP (ForceP) domain. Each
micro-parameter is independently settable to + (verb movement to that
head) or − (no verb movement). Different Germanic languages and dialects
are characterized by different profiles of + and − across these heads.

The book distinguishes two levels:
- **Micro-parameters** (Table 3.1): settings in the adult grammar
- **Micro-cues** (Ch. 3 §4, Ch. 10 §3): observable input patterns that
  trigger each parameter setting in acquisition

## Formalization

1. **`ForceHead`**: the seven clause-type heads (theory layer)
2. **`V2Profile`**: `Profile ForceHead` (theory layer; set of active
   heads)
3. **Language profiles**: per-language Fragment files write set literals
4. **`MicroCue`**: syntactic templates from Ch. 3 §4
5. **Bridge theorems** to SAI data, V2 data, and GermanicV2
6. **Information Structure**: [±FOC] conditioning of "optional" V2

## Adjacent literature

- @cite{holmberg-2015} (HSK 42 handbook entry on Verb second) is the
  standard recent survey of V2 covering the same Pol°/Int°/Decl° split
  Westergaard formalizes.
- @cite{wiklund-bentzen-hroarsdottir-hrafnbjargarson-2009} elaborates
  embedded-V2 micro-variation across Scandinavian *that*-clauses,
  conditioning embedded V2 on matrix predicate class — a dimension
  Table 3.1 collapses.

## The Split-ForceP Model

@cite{westergaard-2009} splits @cite{rizzi-1997}'s ForceP into
clause-type-specific projections. All seven heads are in the CP domain
(above FinP). Crucially, the distinctions among Decl°, Int°, Pol°, Excl°,
Imp° are **finer** than @cite{rizzi-1997}'s inventory — they are all
"flavors of Force" that the existing `Cat` enum does not distinguish.

Fin° and Wh° do correspond to existing `Cat` heads (`.Fin` and `.C`
respectively), but the five Force-level heads (Decl°, Int°, Pol°, Excl°,
Imp°) are all at the Force level. Note: @cite{westergaard-2009}'s Pol°
is a CP-domain head for yes/no-questions (the verb-fronting target;
y/n questions surface as V1, with Spec-PolP either empty or hosting
a covert Q-operator depending on analysis — @cite{roberts-1993},
Rizzi 1996 posit a Q-operator satisfying a wh-criterion; the V1
surface order is what `.Pol` records, theory-neutrally).
NOT @cite{laka-1990}'s ΣP
(which is `Cat.Pol` in linglib at F-value 2).
-/

namespace Westergaard2009

open Minimalism (ForceHead V2Profile WhElementStatus WhBlocksMovementTo)
open Features.InformationStructure (DiscourseStatus)

-- Fragment data (theory-neutral)
open Fragments.Norwegian (stdNorwegian nordmoreNorwegian)
open Fragments.English (stdEnglish belfastEnglish)
open Fragments.German (german)
open Fragments.Danish (danish)

-- ============================================================================
-- § 0  V2 Types
-- ============================================================================

/-! Shared types for describing V2 word order variation. -/

/-- Clause types relevant to V2 variation. -/
inductive V2ClauseType where
  | declarative
  | whQuestion
  | yesNoQuestion
  | exclamative
  | imperative
  | embeddedDecl
  | embeddedQuestion
  deriving DecidableEq, Repr

/-- V2 status of a clause type in a given language/dialect. -/
inductive V2Status where
  /-- V2 is obligatory -/
  | obligatory
  /-- V2 is impossible (verb stays low or appears finally) -/
  | impossible
  /-- V2 alternates with non-V2, conditioned by other factors -/
  | optional
  deriving DecidableEq, Repr

/-- A single V2 observation: what happens in a given clause type. -/
structure V2Datum where
  sentence : String
  language : String
  clauseType : V2ClauseType
  v2Status : V2Status
  description : String := ""
  citation : String := ""
  deriving Repr

-- ============================================================================
-- § 1  Table 3.1 Verification
-- ============================================================================

/-! @cite{westergaard-2009}'s Table 3.1 enumerates V2 micro-parameter
    settings for six Germanic varieties (Standard Norwegian, Standard
    English, Nordmøre Norwegian, Belfast English, German, Danish).
    Each row is a `V2Profile` set literal in the corresponding Fragment
    file; the theorem below pins down all six rows simultaneously, so
    flipping a single field in a Fragment breaks one conjunct.
    -- UNVERIFIED: page reference for Table 3.1 (cited as p. 41 in earlier
    -- drafts of this file) has not been independently checked against
    -- the published Benjamins edition. -/
theorem table_3_1_complete :
    stdNorwegian       = ({.Decl, .Int, .Pol}       : V2Profile) ∧
    stdEnglish         = ({.Int, .Pol}              : V2Profile) ∧
    nordmoreNorwegian  = ({.Decl, .Pol}             : V2Profile) ∧
    belfastEnglish     = ({.Int, .Pol, .Imp, .Wh}   : V2Profile) ∧
    german             = ({.Decl, .Int, .Pol, .Fin} : V2Profile) ∧
    danish             = ({.Decl, .Int, .Pol, .Excl} : V2Profile) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 2  Micro-Cues (Ch. 3 §4, Ch. 10 §3)
-- ============================================================================

/-! Ch. 3 §4 introduces the *cues* — the syntactic templates in the
    input that trigger each micro-parameter. A micro-cue is a piece of
    I-language structure that children produce on exposure to the
    relevant input. Ch. 10 §3 (34)–(37) gives the final formulations.

    The distinction from Table 3.1: micro-parameters are the *grammar's*
    settings; micro-cues are the *observable evidence* in the input
    that leads children to set each parameter.

    Final micro-cue formulations (Ch. 10 (34)–(37)):
    - (34) DeclP[XP Decl°[+V] ...] — V2 in declaratives
    - (35) IntP[wh Int°[+V] ...] — V2 in wh-questions (wh-phrase in SpecIntP)
    - (36) IntP[wh[Int°] ...] — non-V2 in wh-questions (wh-head *in* Int°)
    - (37) TopP[DP[−FOC] Top° IntP[wh[Int°] ...]] — given subject → non-V2

    NOTE: (36) and (37) are the two key innovations. (36) captures the
    wh-head/phrase distinction: monosyllabic wh-words are heads that
    occupy Int° directly, blocking verb movement. (37) captures the
    TopP/[±FOC] mechanism: given subjects ([−FOC]) move to SpecTopP,
    which is the structural basis for the information-structure
    conditioning of V2 in § 10 below. -/

/-- A micro-cue: a syntactic template that serves as evidence for
    a particular micro-parameter setting in acquisition. -/
structure MicroCue where
  /-- Which head this cue is evidence for -/
  target : ForceHead
  /-- The syntactic template (schematic notation) -/
  template : String
  /-- Description of the cue -/
  description : String := ""
  deriving Repr

/-- Cue for V2 in wh-questions. -/
def cueIntV2 : MicroCue :=
  { target := .Int
    template := "IntP[wh Int°V]"
    description := "Wh-element in SpecIntP, finite verb raised to Int°" }

/-- Cue for V2 in declaratives. -/
def cueDeclV2 : MicroCue :=
  { target := .Decl
    template := "DeclP[XP Decl°V]"
    description := "Non-subject XP in SpecDeclP, finite verb raised to Decl°" }

/-- Cue for V2 in exclamatives. -/
def cueExclV2 : MicroCue :=
  { target := .Excl
    template := "ExclP[wh Excl°V]"
    description := "Wh-exclamative with finite verb raised to Excl°" }

/-- Cue for V2 in embedded questions. -/
def cueWhV2 : MicroCue :=
  { target := .Wh
    template := "WhP[wh Wh°V]"
    description := "Embedded question with finite verb raised to Wh°" }

/-- Cue for non-V2 in exclamatives. -/
def cueExclNonV2 : MicroCue :=
  { target := .Excl
    template := "ExclP[wh ... VP[V]]"
    description := "Exclamative with verb remaining in VP (no verb movement to Excl°)" }

/-- Cue for non-V2 in embedded questions. -/
def cueWhNonV2 : MicroCue :=
  { target := .Wh
    template := "WhP[wh ... VP[V]]"
    description := "Embedded question with verb remaining in VP" }

/-- Cue for V2 in yes/no-questions. -/
def cuePolV2 : MicroCue :=
  { target := .Pol
    template := "PolP[Pol°V ...]"
    description := "Finite verb raised to Pol° in yes/no-questions" }

/-- Cue for V2 in imperatives. -/
def cueImpV2 : MicroCue :=
  { target := .Imp
    template := "ImpP[Imp°V ...]"
    description := "Finite verb raised to Imp° in imperatives" }

/-- Cue for wh-head-in-Int° (non-V2 in wh-questions).
    Ch. 10 (36): IntP[wh[Int°] ...] — the monosyllabic wh-word
    occupies Int° itself, blocking verb movement to that position. -/
def cueWhHeadInInt : MicroCue :=
  { target := .Int
    template := "IntP[wh[Int°] ...]"
    description := "Wh-head occupies Int°, blocking verb movement (Ch. 10 (36))" }

/-- Cue for given-subject-blocking-V2 in Tromsø monosyllabic
    *wh*-questions. Ch. 10 (37): TopP[DP[−FOC] Top° IntP[wh[Int°] ...]] —
    the [−FOC] subject moves to SpecTopP, leaving Int° empty (verb
    stays low → non-V2). The TopP/[±FOC] mechanism is what derives the
    information-structure conditioning of "optional" V2 in § 10. -/
def cueGivenSubjectNonV2 : MicroCue :=
  { target := .Int
    template := "TopP[DP[−FOC] Top° IntP[wh[Int°] ...]]"
    description := "Given subject ([−FOC]) in SpecTopP → non-V2 (Ch. 10 (37))" }

/-- A cue is *expressed* in a language iff its target head is in the
    language's `V2Profile`. Children exposed to an expressed cue will
    set the corresponding parameter to +. -/
def CueExpressed (lang : V2Profile) (c : MicroCue) : Prop := c.target ∈ lang

instance (lang : V2Profile) [DecidablePred (· ∈ lang)] (c : MicroCue) :
    Decidable (CueExpressed lang c) := by
  unfold CueExpressed; infer_instance

-- ============================================================================
-- § 3  V2 Data from the Book
-- ============================================================================

/-! V2 observations from across the book, organized by language. -/

-- Norwegian V2 Variation (Tromsø dialect, Ch. 2 Table 2.3)

/-- Non-subject-initial declaratives: V2 obligatory. -/
def no_decl_nonsubj : V2Datum :=
  { sentence := "Av og til snakker vi tysk"
    language := "Norwegian (Tromsø)"
    clauseType := .declarative
    v2Status := .obligatory
    description := "Non-subject-initial declarative: V2 obligatory"
    citation := "Ch. 2 Table 2.3" }

/-- Yes/no-questions: V2 obligatory. -/
def no_yesno : V2Datum :=
  { sentence := "Snakker dere norsk?"
    language := "Norwegian (Tromsø)"
    clauseType := .yesNoQuestion
    v2Status := .obligatory
    description := "Yes/no-question: V2 obligatory"
    citation := "Ch. 1 (3)" }

/-- Wh-questions with long (polysyllabic) wh-phrases: V2 obligatory. -/
def no_wh_long : V2Datum :=
  { sentence := "Korfor gikk ho?"
    language := "Norwegian (Tromsø)"
    clauseType := .whQuestion
    v2Status := .obligatory
    description := "Wh-question with disyllabic korfor 'why': V2 obligatory"
    citation := "Ch. 2 (40)" }

/-- Wh-questions with short (monosyllabic) wh-words: V2 optional,
    conditioned by information structure. -/
def no_wh_short : V2Datum :=
  { sentence := "Ka legen sa? / Ka sa legen?"
    language := "Norwegian (Tromsø)"
    clauseType := .whQuestion
    v2Status := .optional
    description := "Wh-question with monosyllabic ka 'what': V2/non-V2 depends on subject givenness"
    citation := "Ch. 2 (43)–(45)" }

/-- Exclamatives: non-V2 obligatory. -/
def no_excl : V2Datum :=
  { sentence := "Kor rart han snakke!"
    language := "Norwegian (Tromsø)"
    clauseType := .exclamative
    v2Status := .impossible
    description := "Exclamative: non-V2 obligatory"
    citation := "Ch. 1 (5)" }

/-- Embedded declaratives: non-V2 (mostly). -/
def no_emb_decl : V2Datum :=
  { sentence := "Han sa (at) han ikke kommer"
    language := "Norwegian (Tromsø)"
    clauseType := .embeddedDecl
    v2Status := .impossible
    description := "Embedded declarative: non-V2 (verb below negation)"
    citation := "Ch. 2 (36)" }

-- Cross-Germanic Contrasts

/-- Standard English: no V2 in declaratives (SVO base order). -/
def en_decl : V2Datum :=
  { sentence := "The children have seen this film"
    language := "English"
    clauseType := .declarative
    v2Status := .impossible
    description := "English declarative: no V2 (SVO base order)"
    citation := "Ch. 3 Table 3.1" }

/-- Standard English: V2 in wh-questions (via SAI). -/
def en_wh : V2Datum :=
  { sentence := "What will you wear tonight?"
    language := "English"
    clauseType := .whQuestion
    v2Status := .obligatory
    description := "English wh-question: V2 (subject-auxiliary inversion)"
    citation := "Ch. 3 Table 3.1" }

/-- Belfast English: V2 in embedded questions too. -/
def belfast_emb_q : V2Datum :=
  { sentence := "I wonder could he come"
    language := "English (Belfast)"
    clauseType := .embeddedQuestion
    v2Status := .obligatory
    description := "Belfast English: V2 in embedded questions"
    citation := "Ch. 3 Table 3.1; @cite{henry-1995}" }

/-- Danish: V2 in exclamatives (unlike Norwegian and English). -/
def da_excl : V2Datum :=
  { sentence := "Hvor er han sød!"
    language := "Danish"
    clauseType := .exclamative
    v2Status := .obligatory
    description := "Danish exclamative: V2 (unlike Norwegian/English)"
    citation := "Ch. 2 (19)" }

/-- German root declaratives: V2 obligatory. -/
def de_decl : V2Datum :=
  { sentence := "Diesen Film haben die Kinder gesehen"
    language := "German"
    clauseType := .declarative
    v2Status := .obligatory
    description := "German root declarative: V2"
    citation := "@cite{vikner-1995}" }

/-- German embedded clauses with complementizer: verb-final (no V2).
    @cite{westergaard-2009}'s analysis: the verb raises to Fin° (hence
    +Fin° in Table 3.1) but not to C, surfacing clause-finally because
    Westergaard tacitly assumes a head-final FinP for German embedded
    clauses (Vikner-style V-to-I where the I-position itself is final).
    Alternative analyses (Haider 2010; @cite{harizanov-gribanova-2019})
    derive the same surface order without V-to-Fin, leaving the verb
    in its base position. The codebase records the Westergaard +Fin°
    side; see `HarizanovGribanova2019.lean` for the formal contrast. -/
def de_emb : V2Datum :=
  { sentence := "... dass die Kinder diesen Film gesehen haben"
    language := "German"
    clauseType := .embeddedDecl
    v2Status := .impossible
    description := "German embedded clause with dass: surface verb-final (V-to-Fin into head-final FinP per Westergaard; alternative analyses leave V in V)"
    citation := "@cite{vikner-1995}; cf. @cite{harizanov-gribanova-2019}" }

-- ============================================================================
-- § 4  Cross-Language Comparison Theorems
-- ============================================================================

/-- Standard Norwegian and Standard English differ only on Decl°.
    Captures the classic observation that English lost V2 in
    declaratives but retained it in questions. -/
theorem no_en_differ_only_on_decl :
    Core.Typology.Profile.DiffersExactlyOn stdNorwegian stdEnglish .Decl := by
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_symmDiff]; decide
  · intro fh hne; cases fh <;> first | (exact absurd rfl hne) | (constructor <;> decide)

/-- Nordmøre Norwegian is the mirror image of English on Decl° vs. Int°. -/
theorem nordmore_en_mirror_decl_int :
    .Decl ∈ nordmoreNorwegian ∧ .Int ∉ nordmoreNorwegian ∧
    .Decl ∉ stdEnglish        ∧ .Int ∈ stdEnglish := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Danish differs from Standard Norwegian only on Excl°. -/
theorem danish_no_differ_only_on_excl :
    Core.Typology.Profile.DiffersExactlyOn danish stdNorwegian .Excl := by
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_symmDiff]; decide
  · intro fh hne; cases fh <;> first | (exact absurd rfl hne) | (constructor <;> decide)

/-- All six languages in @cite{westergaard-2009} Table 3.1 agree on
    +Pol° (verb-fronting / V1 in yes/no-questions). NOT a Germanic
    universal beyond this sample: Yiddish embedded y/n questions with
    *tsi* and certain colloquial registers complicate the picture, and
    on some analyses Pol° is epiphenomenal on Int° rather than an
    independent micro-parameter. -/
theorem pol_universal :
    .Pol ∈ stdNorwegian ∧ .Pol ∈ stdEnglish ∧ .Pol ∈ nordmoreNorwegian ∧
    .Pol ∈ belfastEnglish ∧ .Pol ∈ german ∧ .Pol ∈ danish := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- German is the only Table 3.1 language with +Fin° (V-to-I in
    embedded clauses). -/
theorem fin_only_german :
    .Fin ∈ german ∧
    .Fin ∉ stdNorwegian ∧ .Fin ∉ stdEnglish ∧ .Fin ∉ nordmoreNorwegian ∧
    .Fin ∉ belfastEnglish ∧ .Fin ∉ danish := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 5  Wh Head/Phrase Distinction
-- ============================================================================

/-! Ch. 7 argues that monosyllabic wh-words are syntactic heads (X°)
    while polysyllabic wh-constituents are phrases (XP). When a wh-head
    occupies Int°, it blocks verb movement, making non-V2 possible.
    When a wh-phrase is in SpecIntP, Int° is free for the verb → V2
    obligatory.

    Tromsø Norwegian wh-words:
    - Monosyllabic (heads): *ka* 'what' (1σ), *kem* 'who' (1σ),
      *kor* 'where' (1σ)
    - Polysyllabic (phrases): *korfor* 'why' (2σ), *korsen* 'how' (2σ),
      *katti* 'when' (2σ) -/

/-- Tromsø wh-word data: (form, gloss, syllable count). -/
def tromsøWhWords : List (String × String × Nat) :=
  [("ka", "what", 1), ("kem", "who", 1), ("kor", "where", 1),
   ("korfor", "why", 2), ("korsen", "how", 2), ("katti", "when", 2)]

/-- All monosyllabic Tromsø wh-words classify as heads. -/
theorem tromsø_mono_are_heads :
    ∀ w ∈ tromsøWhWords, w.2.2 ≤ 1 →
      WhElementStatus.fromSyllableCount w.2.2 = .head := by decide

/-- All polysyllabic Tromsø wh-words classify as phrases. -/
theorem tromsø_poly_are_phrases :
    ∀ w ∈ tromsøWhWords, 1 < w.2.2 →
      WhElementStatus.fromSyllableCount w.2.2 = .phrase := by decide

/-- Wh-heads block verb movement to the wh-question heads (`.Int`
    matrix, `.Wh` embedded) only; phrase wh-words never block. -/
theorem wh_blocking :
    WhBlocksMovementTo .head .Int ∧ WhBlocksMovementTo .head .Wh ∧
    ¬ WhBlocksMovementTo .head .Decl ∧ ¬ WhBlocksMovementTo .phrase .Int := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 6  Bridge to SAI Data
-- ============================================================================

/-! English SAI (from `SubjectAuxInversion.lean`) is the surface reflex
    of +Int° and +Pol° in the English V2 profile. -/

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English matrix wh-questions require inversion (ex01) and the profile
    contains Int°. -/
theorem english_wh_sai_consistent :
    ex01.inverted = true ∧
    ex01.acceptability = .grammatical ∧
    ForceHead.Int ∈ stdEnglish := by
  refine ⟨rfl, rfl, ?_⟩; decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English matrix yes/no-questions require inversion (ex04) and the
    profile contains Pol°. -/
theorem english_yn_sai_consistent :
    ex04.inverted = true ∧
    ex04.acceptability = .grammatical ∧
    ForceHead.Pol ∈ stdEnglish := by
  refine ⟨rfl, rfl, ?_⟩; decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English declaratives lack V2: Decl° is not in the profile. -/
theorem english_decl_no_v2_consistent :
    ForceHead.Decl ∉ stdEnglish := by decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- Belfast English embedded inversion is consistent with +Wh°. -/
theorem belfast_embedded_inv_consistent :
    ex23.acceptability = .dialectal ∧
    ex24.acceptability = .dialectal ∧
    ForceHead.Wh ∈ belfastEnglish := by
  refine ⟨rfl, rfl, ?_⟩; decide

-- ============================================================================
-- § 7  Bridge to V2 Data
-- ============================================================================

/-- Norwegian yes/no-questions are obligatorily V2, consistent with +Pol°. -/
theorem no_yesno_consistent :
    no_yesno.v2Status = .obligatory ∧ ForceHead.Pol ∈ stdNorwegian := by
  refine ⟨rfl, ?_⟩; decide

/-- Norwegian exclamatives are non-V2, consistent with −Excl°. -/
theorem no_excl_consistent :
    no_excl.v2Status = .impossible ∧ ForceHead.Excl ∉ stdNorwegian := by
  refine ⟨rfl, ?_⟩; decide

/-- Danish exclamatives are V2, consistent with +Excl°. -/
theorem da_excl_consistent :
    da_excl.v2Status = .obligatory ∧ ForceHead.Excl ∈ danish := by
  refine ⟨rfl, ?_⟩; decide

/-- German embedded clauses are verb-final (no V2), even though German
    has +Fin° (V-to-I). V2 = verb-to-C requires +Decl°/+Int° etc.;
    verb-final is consistent with −Wh° (no V-to-C in embedded contexts). -/
theorem de_emb_no_v2 :
    de_emb.v2Status = .impossible ∧ ForceHead.Wh ∉ german := by
  refine ⟨rfl, ?_⟩; decide

-- ============================================================================
-- § 7b  Bridge to HPSG Inversion (@cite{sag-wasow-bender-2003})
-- ============================================================================

/-! `Theories/Syntax/HPSG/Inversion.lean` derives English matrix/embedded
    question word-order asymmetries from an `[INV ±]` feature on clauses,
    with `matrixRequiresInvPlus` and `embeddedRequiresInvMinus` constraints.
    @cite{westergaard-2009}'s English profile commits to +Int° (matrix
    wh) and +Pol° (matrix y/n), which are the V-to-C steps that surface
    as inversion. The two frameworks agree on the same surface contrast
    via different machinery; the bridge theorem makes the agreement
    visible. -/

/-- Westergaard and @cite{sag-wasow-bender-2003}-style HPSG agree on
    English matrix question inversion: Westergaard's V-to-C
    (`.Int`/`.Pol ∈ stdEnglish`) projects the same surface order that
    HPSG derives from `[INV +]`. Both frameworks could have committed
    otherwise (Westergaard could have ascribed −Int°; HPSG could have
    left matrix-question INV unconstrained), so the agreement is
    non-trivial. -/
theorem westergaard_hpsg_agree_english_matrix_question :
    ForceHead.Int ∈ stdEnglish ∧
    ForceHead.Pol ∈ stdEnglish ∧
    (∀ inv, HPSG.matrixRequiresInvPlus .matrixQuestion inv → inv = .plus) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · intro _ h; exact h rfl

/-- The same agreement on the embedded side: Westergaard records
    Standard English as −Wh° (no V-to-C in embedded questions); HPSG
    records `embeddedRequiresInvMinus`. Both frameworks predict
    subject-first surface order in embedded questions for Standard
    English; Belfast English breaks this on both sides
    (`.Wh ∈ belfastEnglish` per Westergaard; @cite{henry-1995}'s
    "I wonder could he come" per HPSG-style accounts). -/
theorem westergaard_hpsg_agree_english_embedded_question :
    ForceHead.Wh ∉ stdEnglish ∧
    (∀ inv, HPSG.embeddedRequiresInvMinus .embeddedQuestion inv → inv = .minus) := by
  refine ⟨?_, ?_⟩
  · decide
  · intro _ h; exact h rfl

-- ============================================================================
-- § 8  Bridge to GermanicV2.lean
-- ============================================================================

/-! `GermanicV2.lean` proves that German V2 involves head-to-head movement
    of V to C, skipping T (HMC violation). This is the structural
    realization of +Decl° in the V2 profile: verb movement targets the
    Decl° head in the CP domain. -/

/-- German +Decl° is consistent with the V-to-C movement formalized in
    `GermanicV2.lean`. -/
theorem german_decl_v2_bridge :
    ForceHead.Decl ∈ german := by decide

-- ============================================================================
-- § 9  Bridge to Typology
-- ============================================================================

/-! WALS classifies German as having "no dominant order" (`Typology.lean`).
    Westergaard's micro-parameters explain *why*: German has +Decl° (V2 in
    root declaratives) but also +Fin° (V-to-I in embedded clauses,
    yielding verb-final surface order due to SOV base). This split makes
    the "basic" order indeterminate — SVO on the surface in root
    clauses, SOV underlyingly and in embedded clauses. -/

open Phenomena.WordOrder.Typology in
/-- German's "no dominant order" classification in WALS is consistent
    with a profile that has BOTH +Decl° (V2 in roots → surface SVO) AND
    +Fin° (V-to-I in embedded → surface SOV). -/
theorem german_noDominant_explained :
    Fragments.German.typology.wordOrder.basicOrder = .noDominant ∧
    ForceHead.Decl ∈ german ∧
    ForceHead.Fin  ∈ german := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

open Phenomena.WordOrder.Typology in
/-- English is classified as SVO in WALS. Consistent with −Decl°
    (no verb movement in declaratives → surface SVO with SVO base)
    and −Fin° (no V-to-I in embedded → embedded order also SVO). -/
theorem english_svo_explained :
    Fragments.English.typology.wordOrder.basicOrder = .svo ∧
    ForceHead.Decl ∉ stdEnglish ∧
    ForceHead.Fin  ∉ stdEnglish := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 10  Information Structure and "Optional" V2
-- ============================================================================

/-! In Tromsø *wh*-questions with monosyllabic *wh*-words, V2 vs. non-V2
    correlates with the discourse status of the subject:

    - **[−FOC] / given subject** (pronoun) → non-V2 preferred.
      Subject moves to SpecTopP; verb stays low.
    - **[+FOC] / new subject** (full DP) → V2 preferred.
      Subject stays in SpecIP; verb moves to Top° to check [−FOC].

    The book *derives* this from TopP structure (pp. 46–47): given
    subjects carry [−FOC], which triggers movement to SpecTopP, leaving
    Int° empty (verb stays low). New subjects lack [−FOC], so they stay
    in SpecIP and the verb moves to Top°/Int° → V2. The [±FOC] feature
    already exists in `Features.lean` (`foc : Bool → FeatureVal`) but
    is not yet connected to an Agree-based derivation.

    TODO: Replace this stipulative pattern match with a derivation from
    [±FOC] feature checking on subjects + TopP Agree/movement. The
    current version captures the correct *empirical mapping* but does
    not explain *why* the mapping holds — the TopP mechanism does. -/

/-- Preferred V2 status given subject discourse status in Tromsø
    monosyllabic *wh*-questions.

    STIPULATIVE: pattern-matches on discourse status directly.
    The book derives this from [±FOC]/TopP (see § 10 docstring). -/
def tromsøWhV2Preference : DiscourseStatus → V2Status
  | .given   => .impossible  -- given/pronominal subject → non-V2 preferred
  | .new     => .obligatory  -- new/full-DP subject → V2 preferred
  | .focused => .obligatory  -- focused subject → V2 preferred

/-- Given subjects predict non-V2 in Tromsø short *wh*-questions. -/
theorem given_predicts_nonV2 : tromsøWhV2Preference .given = .impossible := rfl

/-- New subjects predict V2 in Tromsø short *wh*-questions. -/
theorem new_predicts_V2 : tromsøWhV2Preference .new = .obligatory := rfl

-- ============================================================================
-- § 11  Economy
-- ============================================================================

/-! @cite{westergaard-2009}'s structural economy (p. 4):

    (9a) Only build as much structure as there is evidence for in the input.
    (9b) Only move elements as far as there is evidence for in the input.

    These principles constrain *children's grammars*: children build
    minimal structure, adding projections only when input evidence forces
    them.

    The corollary below: languages with fewer active micro-parameters
    require less structure to be built. Our own derivation, not a claim
    directly stated in the book. `Profile.activeCount` instances the
    polymorphic counter from `Core/Typology/Profile.lean`. -/

/-- English activates fewer micro-parameters than Standard Norwegian. -/
theorem english_fewer_active :
    stdEnglish.activeCount < stdNorwegian.activeCount := by decide

/-- Nordmøre activates fewer micro-parameters than Standard Norwegian. -/
theorem nordmore_fewer_active :
    nordmoreNorwegian.activeCount < stdNorwegian.activeCount := by decide

end Westergaard2009
