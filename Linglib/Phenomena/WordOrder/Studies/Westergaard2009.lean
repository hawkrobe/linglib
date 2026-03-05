import Linglib.Phenomena.WordOrder.V2
import Linglib.Phenomena.WordOrder.Typology
import Linglib.Phenomena.WordOrder.SubjectAuxInversion
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic
import Linglib.Theories.Syntax.Minimalism.HeadMovement.GermanicV2
import Linglib.Core.Discourse.InformationStructure

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
- **Micro-cues** (Table 3.2): observable input patterns that trigger
  each parameter setting in acquisition

## Formalization

1. **`ForceHead`**: the seven clause-type heads in the split-ForceP model
2. **`V2Profile`**: a function `ForceHead → Bool` — Table 3.1 data
3. **`MicroCue`**: syntactic templates from Table 3.2
4. **Six language profiles** verified against Table 3.1
5. **Bridge theorems** to SAI data, V2 data, and GermanicV2

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

namespace Phenomena.WordOrder.Studies.Westergaard2009

open Minimalism (Cat fValue)
open Core.InformationStructure (DiscourseStatus)
open Phenomena.WordOrder.V2 (ClauseType V2Status)

-- ============================================================================
-- § 1  ForceHead and V2 Profiles (Table 3.1, p. 41)
-- ============================================================================

/-- The seven clause-type heads in @cite{westergaard-2009}'s split-ForceP.
    Each represents a possible target for verb movement.

    These are all in the CP domain (at or above FinP). The five root-clause
    heads (Decl, Int, Pol, Excl, Imp) are all "flavors of Force" —
    finer-grained than @cite{rizzi-1997}'s single Force head. -/
inductive ForceHead where
  | Decl   -- declaratives (DeclP)
  | Int    -- wh-questions (IntP)
  | Pol    -- yes/no-questions (PolP, @cite{holmberg-2003})
  | Excl   -- exclamatives (ExclP)
  | Imp    -- imperatives (ImpP)
  | Fin    -- embedded clauses (FinP = V-to-I)
  | Wh     -- embedded questions (WhP)
  deriving DecidableEq, Repr, BEq

/-- Whether a ForceHead is a root-clause head (in the Force domain)
    or a lower/embedded head. -/
def ForceHead.isRootClause : ForceHead → Bool
  | .Decl | .Int | .Pol | .Excl | .Imp => true
  | .Fin  | .Wh                        => false

/-- A V2 profile: for each clause-type head, whether verb movement
    to that head is required (+) or absent (−) in a given language/dialect.

    This is the formalization of **Table 3.1** (p. 41) — the
    *micro-parameter* settings, not the micro-cues (input evidence).
    For cues, see `MicroCue` below. -/
structure V2Profile where
  name : String
  verbMovement : ForceHead → Bool

/-- Count how many heads trigger verb movement in a profile. -/
def V2Profile.activeCount (p : V2Profile) : Nat :=
  [ForceHead.Decl, .Int, .Pol, .Excl, .Imp, .Fin, .Wh].countP p.verbMovement

-- ============================================================================
-- § 2  Language Profiles (Table 3.1, p. 41)
-- ============================================================================

/-- Standard Norwegian: +Decl°, +Int°, +Pol°, −Excl°, −Imp°, −Fin°, −Wh°. -/
def stdNorwegian : V2Profile where
  name := "Standard Norwegian"
  verbMovement
    | .Decl => true  | .Int  => true  | .Pol  => true
    | .Excl => false | .Imp  => false | .Fin  => false | .Wh => false

/-- Standard English: −Decl°, +Int°, +Pol°, −Excl°, −Imp°, −Fin°, −Wh°. -/
def stdEnglish : V2Profile where
  name := "Standard English"
  verbMovement
    | .Decl => false | .Int  => true  | .Pol  => true
    | .Excl => false | .Imp  => false | .Fin  => false | .Wh => false

/-- Nordmøre Norwegian: +Decl°, −Int°, +Pol°, −Excl°, −Imp°, −Fin°, −Wh°. -/
def nordmoreNorwegian : V2Profile where
  name := "Nordmøre Norwegian"
  verbMovement
    | .Decl => true  | .Int  => false | .Pol  => true
    | .Excl => false | .Imp  => false | .Fin  => false | .Wh => false

/-- Belfast English: −Decl°, +Int°, +Pol°, −Excl°, +Imp°, −Fin°, +Wh°. -/
def belfastEnglish : V2Profile where
  name := "Belfast English"
  verbMovement
    | .Decl => false | .Int  => true  | .Pol  => true
    | .Excl => false | .Imp  => true  | .Fin  => false | .Wh => true

/-- German: +Decl°, +Int°, +Pol°, −Excl°, −Imp°, +Fin°, −Wh°. -/
def german : V2Profile where
  name := "German"
  verbMovement
    | .Decl => true  | .Int  => true  | .Pol  => true
    | .Excl => false | .Imp  => false | .Fin  => true  | .Wh => false

/-- Danish: +Decl°, +Int°, +Pol°, +Excl°, −Imp°, −Fin°, −Wh°. -/
def danish : V2Profile where
  name := "Danish"
  verbMovement
    | .Decl => true  | .Int  => true  | .Pol  => true
    | .Excl => true  | .Imp  => false | .Fin  => false | .Wh => false

-- ============================================================================
-- § 3  Complete Table 3.1 Verification (all 42 cells)
-- ============================================================================

/-! Every cell of Table 3.1 is verified, so changing a single field
    breaks exactly one guard. -/

-- Standard Norwegian: + + + − − − −
#guard stdNorwegian.verbMovement .Decl == true
#guard stdNorwegian.verbMovement .Int  == true
#guard stdNorwegian.verbMovement .Pol  == true
#guard stdNorwegian.verbMovement .Excl == false
#guard stdNorwegian.verbMovement .Imp  == false
#guard stdNorwegian.verbMovement .Fin  == false
#guard stdNorwegian.verbMovement .Wh   == false

-- Standard English: − + + − − − −
#guard stdEnglish.verbMovement .Decl == false
#guard stdEnglish.verbMovement .Int  == true
#guard stdEnglish.verbMovement .Pol  == true
#guard stdEnglish.verbMovement .Excl == false
#guard stdEnglish.verbMovement .Imp  == false
#guard stdEnglish.verbMovement .Fin  == false
#guard stdEnglish.verbMovement .Wh   == false

-- Nordmøre Norwegian: + − + − − − −
#guard nordmoreNorwegian.verbMovement .Decl == true
#guard nordmoreNorwegian.verbMovement .Int  == false
#guard nordmoreNorwegian.verbMovement .Pol  == true
#guard nordmoreNorwegian.verbMovement .Excl == false
#guard nordmoreNorwegian.verbMovement .Imp  == false
#guard nordmoreNorwegian.verbMovement .Fin  == false
#guard nordmoreNorwegian.verbMovement .Wh   == false

-- Belfast English: − + + − + − +
#guard belfastEnglish.verbMovement .Decl == false
#guard belfastEnglish.verbMovement .Int  == true
#guard belfastEnglish.verbMovement .Pol  == true
#guard belfastEnglish.verbMovement .Excl == false
#guard belfastEnglish.verbMovement .Imp  == true
#guard belfastEnglish.verbMovement .Fin  == false
#guard belfastEnglish.verbMovement .Wh   == true

-- German: + + + − − + −
#guard german.verbMovement .Decl == true
#guard german.verbMovement .Int  == true
#guard german.verbMovement .Pol  == true
#guard german.verbMovement .Excl == false
#guard german.verbMovement .Imp  == false
#guard german.verbMovement .Fin  == true
#guard german.verbMovement .Wh   == false

-- Danish: + + + + − − −
#guard danish.verbMovement .Decl == true
#guard danish.verbMovement .Int  == true
#guard danish.verbMovement .Pol  == true
#guard danish.verbMovement .Excl == true
#guard danish.verbMovement .Imp  == false
#guard danish.verbMovement .Fin  == false
#guard danish.verbMovement .Wh   == false

-- ============================================================================
-- § 4  Micro-Cues (Table 3.2, p. 56)
-- ============================================================================

/-! Table 3.2 formalizes the *cues* — the syntactic templates in the input
    that trigger each micro-parameter. A micro-cue is a piece of I-language
    structure that children produce on exposure to the relevant input.

    The distinction from Table 3.1: micro-parameters are the *grammar's*
    settings; micro-cues are the *observable evidence* in the input that
    leads children to set each parameter.

    Notation (from Westergaard Ch. 3 §4):
    - IntP[wh Int°V] = wh-element in SpecIntP, finite verb in Int° head
    - DeclP[XP Decl°V] = non-subject XP in SpecDeclP, verb in Decl°
    - ExclP[wh Excl°V] = wh-exclamative with verb in Excl°
    - WhP[wh Wh°V] = embedded question with verb in Wh° -/

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

/-- Cue for non-V2 in embedded declaratives. -/
def cueFinNonV2 : MicroCue :=
  { target := .Fin
    template := "IP[XP ... VP[V]]"
    description := "Embedded declarative with verb remaining in VP" }

/-- Table 3.2: which cues are expressed (+) in each language's input.
    Children exposed to a + cue will set the corresponding parameter. -/
def cueExpressed (lang : V2Profile) (c : MicroCue) : Bool :=
  lang.verbMovement c.target

-- Table 3.2 verification (4 cues × 5 languages)

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
-- § 5  Cross-Language Comparison Theorems
-- ============================================================================

/-- Standard Norwegian and Standard English differ only on Decl°.
    This captures the classic observation that English lost V2 in
    declaratives but retained it in questions. -/
theorem no_en_differ_only_on_decl :
    stdNorwegian.verbMovement .Int  = stdEnglish.verbMovement .Int  ∧
    stdNorwegian.verbMovement .Pol  = stdEnglish.verbMovement .Pol  ∧
    stdNorwegian.verbMovement .Excl = stdEnglish.verbMovement .Excl ∧
    stdNorwegian.verbMovement .Imp  = stdEnglish.verbMovement .Imp  ∧
    stdNorwegian.verbMovement .Fin  = stdEnglish.verbMovement .Fin  ∧
    stdNorwegian.verbMovement .Wh   = stdEnglish.verbMovement .Wh   ∧
    stdNorwegian.verbMovement .Decl ≠ stdEnglish.verbMovement .Decl := by
  decide

/-- Nordmøre Norwegian is the mirror image of English on Decl° vs. Int°:
    Nordmøre has +Decl° −Int°, English has −Decl° +Int°. -/
theorem nordmore_en_mirror_decl_int :
    nordmoreNorwegian.verbMovement .Decl = true  ∧
    nordmoreNorwegian.verbMovement .Int  = false ∧
    stdEnglish.verbMovement .Decl         = false ∧
    stdEnglish.verbMovement .Int          = true  := by
  decide

/-- Danish differs from Standard Norwegian only on Excl°. -/
theorem danish_no_differ_only_on_excl :
    danish.verbMovement .Decl = stdNorwegian.verbMovement .Decl ∧
    danish.verbMovement .Int  = stdNorwegian.verbMovement .Int  ∧
    danish.verbMovement .Pol  = stdNorwegian.verbMovement .Pol  ∧
    danish.verbMovement .Imp  = stdNorwegian.verbMovement .Imp  ∧
    danish.verbMovement .Fin  = stdNorwegian.verbMovement .Fin  ∧
    danish.verbMovement .Wh   = stdNorwegian.verbMovement .Wh   ∧
    danish.verbMovement .Excl ≠ stdNorwegian.verbMovement .Excl := by
  decide

/-- All six languages agree on +Pol° (V2 in yes/no-questions is universal
    across these Germanic varieties). -/
theorem pol_universal :
    stdNorwegian.verbMovement .Pol      = true ∧
    stdEnglish.verbMovement .Pol        = true ∧
    nordmoreNorwegian.verbMovement .Pol = true ∧
    belfastEnglish.verbMovement .Pol    = true ∧
    german.verbMovement .Pol            = true ∧
    danish.verbMovement .Pol            = true := by
  decide

/-- German is the only language with +Fin° (V-to-I in embedded clauses). -/
theorem german_unique_fin :
    german.verbMovement .Fin            = true  ∧
    stdNorwegian.verbMovement .Fin      = false ∧
    stdEnglish.verbMovement .Fin        = false ∧
    nordmoreNorwegian.verbMovement .Fin = false ∧
    belfastEnglish.verbMovement .Fin    = false ∧
    danish.verbMovement .Fin            = false := by
  decide

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
    stdEnglish.verbMovement .Int = true := by
  decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English matrix yes/no-questions require inversion (ex04) and the
    profile marks Pol° as + — consistent. -/
theorem english_yn_sai_consistent :
    ex04.inverted = true ∧
    ex04.acceptability = .grammatical ∧
    stdEnglish.verbMovement .Pol = true := by
  decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- English declaratives lack V2 — consistent with −Decl°. -/
theorem english_decl_no_v2_consistent :
    stdEnglish.verbMovement .Decl = false := by decide

open Phenomena.WordOrder.SubjectAuxInversion in
/-- Belfast English embedded inversion (ex23, ex24) is consistent with +Wh°. -/
theorem belfast_embedded_inv_consistent :
    ex23.acceptability = .dialectal ∧
    ex24.acceptability = .dialectal ∧
    belfastEnglish.verbMovement .Wh = true := by
  decide

-- ============================================================================
-- § 7  Bridge to V2 Data
-- ============================================================================

open Phenomena.WordOrder.V2 in
/-- Norwegian yes/no-questions are obligatorily V2, consistent with +Pol°. -/
theorem no_yesno_consistent :
    no_yesno.v2Status = .obligatory ∧
    stdNorwegian.verbMovement .Pol = true := by
  decide

open Phenomena.WordOrder.V2 in
/-- Norwegian exclamatives are non-V2, consistent with −Excl°. -/
theorem no_excl_consistent :
    no_excl.v2Status = .impossible ∧
    stdNorwegian.verbMovement .Excl = false := by
  decide

open Phenomena.WordOrder.V2 in
/-- Danish exclamatives are V2, consistent with +Excl°. -/
theorem da_excl_consistent :
    da_excl.v2Status = .obligatory ∧
    danish.verbMovement .Excl = true := by
  decide

open Phenomena.WordOrder.V2 in
/-- German embedded clauses are verb-final (no V2), even though German
    has +Fin° (V-to-I). V2 = verb-to-C, which requires +Decl°/+Int° etc.
    Verb-final is consistent with −Wh° (no V-to-C in embedded contexts). -/
theorem de_emb_no_v2 :
    de_emb.v2Status = .impossible ∧
    german.verbMovement .Wh = false := by
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
    german.verbMovement .Decl = true := by decide

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
    german.verbMovement .Decl = true ∧
    german.verbMovement .Fin  = true := by decide

open Phenomena.WordOrder.Typology in
/-- English is classified as SVO in WALS. This is consistent with −Decl°
    (no verb movement in declaratives → surface SVO with SVO base order)
    and −Fin° (no V-to-I in embedded clauses → embedded order also SVO). -/
theorem english_svo_explained :
    english.basicOrder = .svo ∧
    stdEnglish.verbMovement .Decl = false ∧
    stdEnglish.verbMovement .Fin  = false := by decide

-- ============================================================================
-- § 10  Information Structure and "Optional" V2
-- ============================================================================

/-! In Tromsø *wh*-questions with monosyllabic *wh*-words, V2 vs. non-V2
    correlates with the discourse status of the subject:

    - **[−FOC] / given subject** (pronoun) → non-V2 preferred.
      Subject moves to SpecTopP; verb stays low.
    - **[+FOC] / new subject** (full DP) → V2 preferred.
      Subject stays in SpecIP; verb moves to Top° to check [−FOC].

    This is formalized as a function from `DiscourseStatus` to the
    *preferred* word order. These are the grammar's predictions for each
    discourse context; the overall clause type is "optional" (see V2.lean
    `no_wh_short`) with information structure resolving the choice. -/

/-- Preferred V2 status given subject discourse status in Tromsø
    monosyllabic *wh*-questions. -/
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
    stdEnglish.activeCount < stdNorwegian.activeCount := by native_decide

/-- Nordmøre activates fewer micro-parameters than Standard Norwegian. -/
theorem nordmore_fewer_active :
    nordmoreNorwegian.activeCount < stdNorwegian.activeCount := by native_decide

end Phenomena.WordOrder.Studies.Westergaard2009
