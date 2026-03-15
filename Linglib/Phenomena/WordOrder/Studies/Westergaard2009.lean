import Linglib.Core.Grammar
import Linglib.Phenomena.WordOrder.Typology
import Linglib.Phenomena.WordOrder.SubjectAuxInversion
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic
import Linglib.Theories.Syntax.Minimalism.HeadMovement.GermanicV2
import Linglib.Core.Discourse.InformationStructure
import Linglib.Fragments.Norwegian.V2
import Linglib.Fragments.English.V2
import Linglib.Fragments.German.V2
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
2. **`V2Profile`**: a function `ForceHead → Bool` (theory layer)
3. **Language profiles**: per-language Fragment files
4. **`MicroCue`**: syntactic templates from Ch. 3 §4
5. **Bridge theorems** to SAI data, V2 data, and GermanicV2
6. **Information Structure**: [±FOC] conditioning of "optional" V2

## The Split-ForceP Model

@cite{westergaard-2009} splits @cite{rizzi-1997}'s ForceP into
clause-type-specific projections. All seven heads are in the CP domain
(above FinP). Crucially, the distinctions among Decl°, Int°, Pol°, Excl°,
Imp° are **finer** than @cite{rizzi-1997}'s inventory — they are all
"flavors of Force" that the existing `Cat` enum does not distinguish.

Fin° and Wh° do correspond to existing `Cat` heads (`.Fin` and `.C`
respectively), but the five Force-level heads (Decl°, Int°, Pol°, Excl°,
Imp°) are all at the Force level. Note: @cite{westergaard-2009}'s Pol°
follows @cite{holmberg-2003} and is a CP-domain head for yes/no-questions,
NOT @cite{laka-1990}'s ΣP (which is `Cat.Pol` in linglib at F-value 2).
-/

-- ============================================================================
-- Theory Bridge (before namespace, so V2Data.toProfile is at root level)
-- ============================================================================

open Minimalism (ForceHead V2Profile) in
/-- Map theory-neutral V2 observations to @cite{westergaard-2009}'s
    split-ForceP micro-parameter representation. The mapping:
    - `declV2`   → Decl° (verb movement in declaratives)
    - `whQV2`    → Int°  (verb movement in wh-questions)
    - `ynQV2`    → Pol°  (verb movement in yes/no-questions)
    - `exclV2`   → Excl° (verb movement in exclamatives)
    - `impV2`    → Imp°  (verb movement in imperatives)
    - `embFinV2` → Fin°  (V-to-I in embedded finite clauses)
    - `embQV2`   → Wh°   (verb movement in embedded questions) -/
def V2Data.toProfile (d : V2Data) : V2Profile where
  name := d.name
  verbMovement
    | .Decl => d.declV2  | .Int  => d.whQV2   | .Pol  => d.ynQV2
    | .Excl => d.exclV2  | .Imp  => d.impV2   | .Fin  => d.embFinV2
    | .Wh   => d.embQV2

namespace Phenomena.WordOrder.Studies.Westergaard2009

open Minimalism (ForceHead V2Profile WhElementStatus whBlocksVerbMovement)
open Core.InformationStructure (DiscourseStatus)

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
inductive ClauseType where
  | declarative
  | whQuestion
  | yesNoQuestion
  | exclamative
  | imperative
  | embeddedDecl
  | embeddedQuestion
  deriving DecidableEq, Repr, BEq

/-- V2 status of a clause type in a given language/dialect. -/
inductive V2Status where
  /-- V2 is obligatory -/
  | obligatory
  /-- V2 is impossible (verb stays low or appears finally) -/
  | impossible
  /-- V2 alternates with non-V2, conditioned by other factors -/
  | optional
  deriving DecidableEq, Repr, BEq

/-- A single V2 observation: what happens in a given clause type. -/
structure V2Datum where
  sentence : String
  language : String
  clauseType : ClauseType
  v2Status : V2Status
  description : String := ""
  citation : String := ""
  deriving Repr, BEq

-- ============================================================================
-- § 1  Table 3.1 Verification (all 42 cells)
-- ============================================================================

/-! Table 3.1 (p. 41) has exactly **6** language varieties. Every cell
    (6 × 7 = 42) is verified, so changing a single field in a Fragment
    file breaks exactly one guard. -/

-- Standard Norwegian: + + + − − − −
#guard stdNorwegian.toProfile.verbMovement .Decl == true
#guard stdNorwegian.toProfile.verbMovement .Int  == true
#guard stdNorwegian.toProfile.verbMovement .Pol  == true
#guard stdNorwegian.toProfile.verbMovement .Excl == false
#guard stdNorwegian.toProfile.verbMovement .Imp  == false
#guard stdNorwegian.toProfile.verbMovement .Fin  == false
#guard stdNorwegian.toProfile.verbMovement .Wh   == false

-- Standard English: − + + − − − −
#guard stdEnglish.toProfile.verbMovement .Decl == false
#guard stdEnglish.toProfile.verbMovement .Int  == true
#guard stdEnglish.toProfile.verbMovement .Pol  == true
#guard stdEnglish.toProfile.verbMovement .Excl == false
#guard stdEnglish.toProfile.verbMovement .Imp  == false
#guard stdEnglish.toProfile.verbMovement .Fin  == false
#guard stdEnglish.toProfile.verbMovement .Wh   == false

-- Nordmøre Norwegian: + − + − − − −
#guard nordmoreNorwegian.toProfile.verbMovement .Decl == true
#guard nordmoreNorwegian.toProfile.verbMovement .Int  == false
#guard nordmoreNorwegian.toProfile.verbMovement .Pol  == true
#guard nordmoreNorwegian.toProfile.verbMovement .Excl == false
#guard nordmoreNorwegian.toProfile.verbMovement .Imp  == false
#guard nordmoreNorwegian.toProfile.verbMovement .Fin  == false
#guard nordmoreNorwegian.toProfile.verbMovement .Wh   == false

-- Belfast English: − + + − + − +
#guard belfastEnglish.toProfile.verbMovement .Decl == false
#guard belfastEnglish.toProfile.verbMovement .Int  == true
#guard belfastEnglish.toProfile.verbMovement .Pol  == true
#guard belfastEnglish.toProfile.verbMovement .Excl == false
#guard belfastEnglish.toProfile.verbMovement .Imp  == true
#guard belfastEnglish.toProfile.verbMovement .Fin  == false
#guard belfastEnglish.toProfile.verbMovement .Wh   == true

-- German: + + + − − + −
#guard german.toProfile.verbMovement .Decl == true
#guard german.toProfile.verbMovement .Int  == true
#guard german.toProfile.verbMovement .Pol  == true
#guard german.toProfile.verbMovement .Excl == false
#guard german.toProfile.verbMovement .Imp  == false
#guard german.toProfile.verbMovement .Fin  == true
#guard german.toProfile.verbMovement .Wh   == false

-- Danish: + + + + − − −
#guard danish.toProfile.verbMovement .Decl == true
#guard danish.toProfile.verbMovement .Int  == true
#guard danish.toProfile.verbMovement .Pol  == true
#guard danish.toProfile.verbMovement .Excl == true
#guard danish.toProfile.verbMovement .Imp  == false
#guard danish.toProfile.verbMovement .Fin  == false
#guard danish.toProfile.verbMovement .Wh   == false

-- ============================================================================
-- § 2  Micro-Cues (Ch. 3 §4, Ch. 10 §3)
-- ============================================================================

/-! @cite{westergaard-2009} Ch. 3 §4 introduces the *cues* — the syntactic
    templates in the input that trigger each micro-parameter. A micro-cue
    is a piece of I-language structure that children produce on exposure
    to the relevant input. Ch. 10 §3 (34)–(37) gives the final formulations.

    The distinction from Table 3.1: micro-parameters are the *grammar's*
    settings; micro-cues are the *observable evidence* in the input that
    leads children to set each parameter.

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
  deriving Repr, BEq

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

/-- Whether a cue is expressed (+) in a given language's input.
    Children exposed to a + cue will set the corresponding parameter. -/
def cueExpressed (lang : V2Data) (c : MicroCue) : Bool :=
  lang.toProfile.verbMovement c.target

-- Cue verification (4 cues × selected languages)

-- Standard Norwegian: + for IntP and DeclP cues, − for ExclP and WhP
#guard cueExpressed stdNorwegian cueIntV2  == true
#guard cueExpressed stdNorwegian cueDeclV2 == true
#guard cueExpressed stdNorwegian cueExclV2 == false
#guard cueExpressed stdNorwegian cueWhV2   == false

-- Standard English: + for IntP, − for DeclP, ExclP, WhP
#guard cueExpressed stdEnglish cueIntV2  == true
#guard cueExpressed stdEnglish cueDeclV2 == false
#guard cueExpressed stdEnglish cueExclV2 == false
#guard cueExpressed stdEnglish cueWhV2   == false

-- Nordmøre: − for IntP, + for DeclP, − for ExclP and WhP
#guard cueExpressed nordmoreNorwegian cueIntV2  == false
#guard cueExpressed nordmoreNorwegian cueDeclV2 == true

-- Belfast English: + for IntP and WhP, − for DeclP and ExclP
#guard cueExpressed belfastEnglish cueIntV2  == true
#guard cueExpressed belfastEnglish cueDeclV2 == false
#guard cueExpressed belfastEnglish cueWhV2   == true

-- Danish: + for IntP, DeclP, and ExclP; − for WhP
#guard cueExpressed danish cueIntV2  == true
#guard cueExpressed danish cueDeclV2 == true
#guard cueExpressed danish cueExclV2 == true
#guard cueExpressed danish cueWhV2   == false

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
    citation := "@cite{westergaard-2009} Ch. 2 Table 2.3" }

/-- Yes/no-questions: V2 obligatory. -/
def no_yesno : V2Datum :=
  { sentence := "Snakker dere norsk?"
    language := "Norwegian (Tromsø)"
    clauseType := .yesNoQuestion
    v2Status := .obligatory
    description := "Yes/no-question: V2 obligatory"
    citation := "@cite{westergaard-2009} Ch. 1 (3)" }

/-- Wh-questions with long (polysyllabic) wh-phrases: V2 obligatory. -/
def no_wh_long : V2Datum :=
  { sentence := "Korfor gikk ho?"
    language := "Norwegian (Tromsø)"
    clauseType := .whQuestion
    v2Status := .obligatory
    description := "Wh-question with disyllabic korfor 'why': V2 obligatory"
    citation := "@cite{westergaard-2009} Ch. 2 (40)" }

/-- Wh-questions with short (monosyllabic) wh-words: V2 optional,
    conditioned by information structure. -/
def no_wh_short : V2Datum :=
  { sentence := "Ka legen sa? / Ka sa legen?"
    language := "Norwegian (Tromsø)"
    clauseType := .whQuestion
    v2Status := .optional
    description := "Wh-question with monosyllabic ka 'what': V2/non-V2 depends on subject givenness"
    citation := "@cite{westergaard-2009} Ch. 2 (43)–(45)" }

/-- Exclamatives: non-V2 obligatory. -/
def no_excl : V2Datum :=
  { sentence := "Kor rart han snakke!"
    language := "Norwegian (Tromsø)"
    clauseType := .exclamative
    v2Status := .impossible
    description := "Exclamative: non-V2 obligatory"
    citation := "@cite{westergaard-2009} Ch. 1 (5)" }

/-- Embedded declaratives: non-V2 (mostly). -/
def no_emb_decl : V2Datum :=
  { sentence := "Han sa (at) han ikke kommer"
    language := "Norwegian (Tromsø)"
    clauseType := .embeddedDecl
    v2Status := .impossible
    description := "Embedded declarative: non-V2 (verb below negation)"
    citation := "@cite{westergaard-2009} Ch. 2 (36)" }

-- Cross-Germanic Contrasts

/-- Standard English: no V2 in declaratives (SVO base order). -/
def en_decl : V2Datum :=
  { sentence := "The children have seen this film"
    language := "English"
    clauseType := .declarative
    v2Status := .impossible
    description := "English declarative: no V2 (SVO base order)"
    citation := "@cite{westergaard-2009} Ch. 3 Table 3.1" }

/-- Standard English: V2 in wh-questions (via SAI). -/
def en_wh : V2Datum :=
  { sentence := "What will you wear tonight?"
    language := "English"
    clauseType := .whQuestion
    v2Status := .obligatory
    description := "English wh-question: V2 (subject-auxiliary inversion)"
    citation := "@cite{westergaard-2009} Ch. 3 Table 3.1" }

/-- Belfast English: V2 in embedded questions too. -/
def belfast_emb_q : V2Datum :=
  { sentence := "I wonder could he come"
    language := "English (Belfast)"
    clauseType := .embeddedQuestion
    v2Status := .obligatory
    description := "Belfast English: V2 in embedded questions"
    citation := "@cite{westergaard-2009} Ch. 3 Table 3.1; @cite{henry-1995}" }

/-- Danish: V2 in exclamatives (unlike Norwegian and English). -/
def da_excl : V2Datum :=
  { sentence := "Hvor er han sød!"
    language := "Danish"
    clauseType := .exclamative
    v2Status := .obligatory
    description := "Danish exclamative: V2 (unlike Norwegian/English)"
    citation := "@cite{westergaard-2009} Ch. 2 (19)" }

/-- German root declaratives: V2 obligatory. -/
def de_decl : V2Datum :=
  { sentence := "Diesen Film haben die Kinder gesehen"
    language := "German"
    clauseType := .declarative
    v2Status := .obligatory
    description := "German root declarative: V2"
    citation := "@cite{vikner-1995}" }

/-- German embedded clauses with complementizer: verb-final (no V2).
    The verb raises to I/Fin (hence +Fin° in Table 3.1) but not to C,
    so it appears clause-finally due to SOV base order. -/
def de_emb : V2Datum :=
  { sentence := "... dass die Kinder diesen Film gesehen haben"
    language := "German"
    clauseType := .embeddedDecl
    v2Status := .impossible
    description := "German embedded clause with dass: verb-final (V-to-I only, not V-to-C)"
    citation := "@cite{vikner-1995}" }

-- Empirical Generalizations
#guard no_yesno.v2Status == .obligatory
#guard no_excl.v2Status == .impossible
#guard no_wh_short.v2Status == .optional
#guard en_decl.v2Status == .impossible
#guard en_wh.v2Status == .obligatory
#guard da_excl.v2Status == .obligatory
#guard de_decl.v2Status == .obligatory
#guard de_emb.v2Status == .impossible

-- ============================================================================
-- § 4  Cross-Language Comparison Theorems
-- ============================================================================

/-- Standard Norwegian and Standard English differ only on Decl°.
    This captures the classic observation that English lost V2 in
    declaratives but retained it in questions. -/
theorem no_en_differ_only_on_decl :
    stdNorwegian.toProfile.verbMovement .Int  = stdEnglish.toProfile.verbMovement .Int  ∧
    stdNorwegian.toProfile.verbMovement .Pol  = stdEnglish.toProfile.verbMovement .Pol  ∧
    stdNorwegian.toProfile.verbMovement .Excl = stdEnglish.toProfile.verbMovement .Excl ∧
    stdNorwegian.toProfile.verbMovement .Imp  = stdEnglish.toProfile.verbMovement .Imp  ∧
    stdNorwegian.toProfile.verbMovement .Fin  = stdEnglish.toProfile.verbMovement .Fin  ∧
    stdNorwegian.toProfile.verbMovement .Wh   = stdEnglish.toProfile.verbMovement .Wh   ∧
    stdNorwegian.toProfile.verbMovement .Decl ≠ stdEnglish.toProfile.verbMovement .Decl := by
  decide

/-- Nordmøre Norwegian is the mirror image of English on Decl° vs. Int°:
    Nordmøre has +Decl° −Int°, English has −Decl° +Int°. -/
theorem nordmore_en_mirror_decl_int :
    nordmoreNorwegian.toProfile.verbMovement .Decl = true  ∧
    nordmoreNorwegian.toProfile.verbMovement .Int  = false ∧
    stdEnglish.toProfile.verbMovement .Decl         = false ∧
    stdEnglish.toProfile.verbMovement .Int          = true  := by
  decide

/-- Danish differs from Standard Norwegian only on Excl°. -/
theorem danish_no_differ_only_on_excl :
    danish.toProfile.verbMovement .Decl = stdNorwegian.toProfile.verbMovement .Decl ∧
    danish.toProfile.verbMovement .Int  = stdNorwegian.toProfile.verbMovement .Int  ∧
    danish.toProfile.verbMovement .Pol  = stdNorwegian.toProfile.verbMovement .Pol  ∧
    danish.toProfile.verbMovement .Imp  = stdNorwegian.toProfile.verbMovement .Imp  ∧
    danish.toProfile.verbMovement .Fin  = stdNorwegian.toProfile.verbMovement .Fin  ∧
    danish.toProfile.verbMovement .Wh   = stdNorwegian.toProfile.verbMovement .Wh   ∧
    danish.toProfile.verbMovement .Excl ≠ stdNorwegian.toProfile.verbMovement .Excl := by
  decide

/-- All six Table 3.1 languages agree on +Pol° (V2 in yes/no-questions is
    universal across these Germanic varieties). -/
theorem pol_universal :
    stdNorwegian.toProfile.verbMovement .Pol      = true ∧
    stdEnglish.toProfile.verbMovement .Pol        = true ∧
    nordmoreNorwegian.toProfile.verbMovement .Pol = true ∧
    belfastEnglish.toProfile.verbMovement .Pol    = true ∧
    german.toProfile.verbMovement .Pol            = true ∧
    danish.toProfile.verbMovement .Pol            = true := by
  decide

/-- German is the only Table 3.1 language with +Fin° (V-to-I in
    embedded clauses). -/
theorem fin_only_german :
    german.toProfile.verbMovement .Fin            = true  ∧
    stdNorwegian.toProfile.verbMovement .Fin      = false ∧
    stdEnglish.toProfile.verbMovement .Fin        = false ∧
    nordmoreNorwegian.toProfile.verbMovement .Fin = false ∧
    belfastEnglish.toProfile.verbMovement .Fin    = false ∧
    danish.toProfile.verbMovement .Fin            = false := by
  decide

/-- Active parameter counts form a monotone chain from English (fewest)
    to Danish (most) among the Table 3.1 languages. -/
theorem active_count_ordering :
    stdEnglish.toProfile.activeCount ≤ nordmoreNorwegian.toProfile.activeCount ∧
    nordmoreNorwegian.toProfile.activeCount ≤ stdNorwegian.toProfile.activeCount ∧
    stdNorwegian.toProfile.activeCount ≤ german.toProfile.activeCount ∧
    german.toProfile.activeCount ≤ danish.toProfile.activeCount := by
  native_decide

-- ============================================================================
-- § 5  Wh Head/Phrase Distinction
-- ============================================================================

/-! @cite{westergaard-2009} Ch. 7 argues that monosyllabic wh-words
    are syntactic heads (X°) while polysyllabic wh-constituents are
    phrases (XP). When a wh-head occupies Int°, it blocks verb movement,
    making non-V2 possible. When a wh-phrase is in SpecIntP, Int° is
    free for the verb → V2 obligatory.

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
    tromsøWhWords.filter (·.2.2 ≤ 1) |>.all
      (WhElementStatus.fromSyllableCount ·.2.2 == .head) := by native_decide

/-- All polysyllabic Tromsø wh-words classify as phrases. -/
theorem tromsø_poly_are_phrases :
    tromsøWhWords.filter (·.2.2 > 1) |>.all
      (WhElementStatus.fromSyllableCount ·.2.2 == .phrase) := by native_decide

/-- Head wh-words block verb movement; phrase wh-words do not. -/
theorem wh_blocking :
    whBlocksVerbMovement .head = true ∧
    whBlocksVerbMovement .phrase = false := by decide

-- ============================================================================
-- § 6  Bridge to SAI Data
-- ============================================================================

/-! English SAI (from `SubjectAuxInversion.lean`) is exactly the surface
    reflex of +Int° and +Pol° in the English V2 profile. -/

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English matrix wh-questions require inversion (ex01) and the
    profile marks Int° as + — consistent. -/
theorem english_wh_sai_consistent :
    ex01.inverted = true ∧
    ex01.acceptability = .grammatical ∧
    stdEnglish.toProfile.verbMovement .Int = true := by
  decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English matrix yes/no-questions require inversion (ex04) and the
    profile marks Pol° as + — consistent. -/
theorem english_yn_sai_consistent :
    ex04.inverted = true ∧
    ex04.acceptability = .grammatical ∧
    stdEnglish.toProfile.verbMovement .Pol = true := by
  decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English declaratives lack V2 — consistent with −Decl°. -/
theorem english_decl_no_v2_consistent :
    stdEnglish.toProfile.verbMovement .Decl = false := by decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- Belfast English embedded inversion (ex23, ex24) is consistent with +Wh°. -/
theorem belfast_embedded_inv_consistent :
    ex23.acceptability = .dialectal ∧
    ex24.acceptability = .dialectal ∧
    belfastEnglish.toProfile.verbMovement .Wh = true := by
  decide

-- ============================================================================
-- § 7  Bridge to V2 Data
-- ============================================================================

/-- Norwegian yes/no-questions are obligatorily V2, consistent with +Pol°. -/
theorem no_yesno_consistent :
    no_yesno.v2Status = .obligatory ∧
    stdNorwegian.toProfile.verbMovement .Pol = true := by
  decide

/-- Norwegian exclamatives are non-V2, consistent with −Excl°. -/
theorem no_excl_consistent :
    no_excl.v2Status = .impossible ∧
    stdNorwegian.toProfile.verbMovement .Excl = false := by
  decide

/-- Danish exclamatives are V2, consistent with +Excl°. -/
theorem da_excl_consistent :
    da_excl.v2Status = .obligatory ∧
    danish.toProfile.verbMovement .Excl = true := by
  decide

/-- German embedded clauses are verb-final (no V2), even though German
    has +Fin° (V-to-I). V2 = verb-to-C, which requires +Decl°/+Int° etc.
    Verb-final is consistent with −Wh° (no V-to-C in embedded contexts). -/
theorem de_emb_no_v2 :
    de_emb.v2Status = .impossible ∧
    german.toProfile.verbMovement .Wh = false := by
  decide

-- ============================================================================
-- § 8  Bridge to GermanicV2.lean
-- ============================================================================

/-! `GermanicV2.lean` proves that German V2 involves head-to-head movement
    of V to C, skipping T (HMC violation). This is the structural realization
    of +Decl° in @cite{westergaard-2009}'s profile: verb movement targets
    the Decl° head in the CP domain.

    The bridge: German has +Decl° (our profile) AND the syntactic analysis
    shows V moves to C in root declaratives (GermanicV2). -/

/-- German +Decl° is consistent with the V-to-C movement formalized in
    `GermanicV2.lean`: the verb moves to C (= the Decl° position in
    @cite{westergaard-2009}'s split-ForceP).

    The GermanicV2 file shows:
    - V2 is head-to-head movement (`v2_mover_stays_minimal`)
    - V skips T to reach C (`t_intervenes_in_v2`)
    - The mover was a head in the target (`verb_was_head_in_target`) -/
theorem german_decl_v2_bridge :
    german.toProfile.verbMovement .Decl = true := by decide

-- ============================================================================
-- § 9  Bridge to Typology
-- ============================================================================

/-! WALS classifies German as having "no dominant order" (`Typology.lean`).
    Westergaard's micro-parameters explain *why*: German has +Decl° (V2 in
    root declaratives) but also +Fin° (V-to-I in embedded clauses, yielding
    verb-final surface order due to SOV base). This split makes the "basic"
    order indeterminate — SVO on the surface in root clauses, SOV underlyingly
    and in embedded clauses. -/

open Phenomena.WordOrder.Typology in
/-- German's "no dominant order" classification in WALS is consistent with
    a micro-parameter profile that has BOTH +Decl° (V2 in roots → surface SVO)
    AND +Fin° (V-to-I in embedded → surface SOV). -/
theorem german_noDominant_explained :
    germanV2.basicOrder = .noDominant ∧
    german.toProfile.verbMovement .Decl = true ∧
    german.toProfile.verbMovement .Fin  = true := by decide

open Phenomena.WordOrder.Typology in
/-- English is classified as SVO in WALS. This is consistent with −Decl°
    (no verb movement in declaratives → surface SVO with SVO base order)
    and −Fin° (no V-to-I in embedded clauses → embedded order also SVO). -/
theorem english_svo_explained :
    english.basicOrder = .svo ∧
    stdEnglish.toProfile.verbMovement .Decl = false ∧
    stdEnglish.toProfile.verbMovement .Fin  = false := by decide

-- ============================================================================
-- § 10  Information Structure and "Optional" V2
-- ============================================================================

/-! In Tromsø *wh*-questions with monosyllabic *wh*-words, V2 vs. non-V2
    correlates with the discourse status of the subject:

    - **[−FOC] / given subject** (pronoun) → non-V2 preferred.
      Subject moves to SpecTopP; verb stays low.
    - **[+FOC] / new subject** (full DP) → V2 preferred.
      Subject stays in SpecIP; verb moves to Top° to check [−FOC].

    The book *derives* this from TopP structure (pp. 46–47): given subjects
    carry [−FOC], which triggers movement to SpecTopP, leaving Int° empty
    (verb stays low). New subjects lack [−FOC], so they stay in SpecIP and
    the verb moves to Top°/Int° → V2. The [±FOC] feature already exists in
    `Features.lean` (`foc : Bool → FeatureVal`) but is not yet connected
    to an Agree-based derivation.

    TODO: Replace this stipulative pattern match with a derivation from
    [±FOC] feature checking on subjects + TopP Agree/movement. The
    current version captures the correct *empirical mapping* but does not
    explain *why* the mapping holds — the TopP mechanism does. -/

/-- Preferred V2 status given subject discourse status in Tromsø
    monosyllabic *wh*-questions.

    STIPULATIVE: this pattern-matches on discourse status directly.
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

    These principles constrain *children's grammars*: children build minimal
    structure, adding projections only when input evidence forces them.

    The following theorems derive a corollary: languages with fewer active
    micro-parameters require less structure to be built. This is our own
    formalization of a consequence of (9a), not a claim directly stated in
    the book. -/

/-- English activates fewer micro-parameters than Standard Norwegian. -/
theorem english_fewer_active :
    stdEnglish.toProfile.activeCount < stdNorwegian.toProfile.activeCount := by native_decide

/-- Nordmøre activates fewer micro-parameters than Standard Norwegian. -/
theorem nordmore_fewer_active :
    nordmoreNorwegian.toProfile.activeCount < stdNorwegian.toProfile.activeCount := by native_decide

end Phenomena.WordOrder.Studies.Westergaard2009
