import Linglib.Theories.Phonology.Constraints

/-!
# English t/d-Deletion: Cross-Dialectal Data
@cite{coetzee-pater-2011}

Cross-dialectal deletion rates for word-final t/d in English consonant
clusters (e.g. *west* → *wes*), from @cite{coetzee-pater-2011} table (10).
Per-dialect data sources (footnote 3): AAVE (Fasold 1972), Chicano
(Santa Ana 1992), Jamaican (Patrick 1992), Trinidad (Kang 1994),
Tejano (Bayley 1995).

## External context

The key conditioning factor is the **following segment** — what comes after
the word-final cluster:

- **Pre-vocalic** (*west end*): t/d cues are maximally recoverable
- **Pre-pausal** (*west*): partial cue availability (release only)
- **Pre-consonantal** (*west side*): minimal cue availability

The cross-dialectal generalization is that deletion rate follows:
  pre-C ≥ pre-pause ≥ pre-V

with the inequality being strict in most dialects.

## Dialects

Five dialects from the sociolinguistic literature, each with distinct
absolute rates but obeying the pre-C ≥ pre-pause ≥ pre-V ordering.
Chicano English is the sole exception: it has pre-V > pre-pause
(@cite{coetzee-pater-2011} table 10, p. 410).
-/

namespace Fragments.English.TDDeletion

-- ============================================================================
-- § 1: Types
-- ============================================================================

/-- External phonological context following the word-final cluster. -/
inductive Context where
  | preV   -- pre-vocalic (*west end*)
  | pause  -- pre-pausal (*west*)
  | preC   -- pre-consonantal (*west side*)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- English dialects with t/d-deletion data. -/
inductive Dialect where
  | aave      -- African American Vernacular English (Fasold 1972; Washington, DC)
  | chicano   -- Chicano English (Santa Ana 1992)
  | jamaican  -- Jamaican English (Patrick 1992)
  | trinidad  -- Trinidadian English (Kang 1994)
  | tejano    -- Tejano English (Bayley 1995)
  deriving DecidableEq, BEq, Repr, Inhabited

/-- Observed deletion rate as a percentage (integer).
    From @cite{coetzee-pater-2011} table (10), p. 410. -/
def deletionRate : Dialect → Context → Nat
  | .aave,    .preV => 29 | .aave,    .pause => 73 | .aave,    .preC => 76
  | .chicano, .preV => 45 | .chicano, .pause => 37 | .chicano, .preC => 62
  | .jamaican,.preV => 63 | .jamaican,.pause => 71 | .jamaican,.preC => 85
  | .trinidad,.preV => 21 | .trinidad,.pause => 31 | .trinidad,.preC => 81
  | .tejano,  .preV => 25 | .tejano,  .pause => 46 | .tejano,  .preC => 62

/-- All dialects. -/
def allDialects : List Dialect := [.aave, .chicano, .jamaican, .trinidad, .tejano]

/-- All contexts. -/
def allContexts : List Context := [.preV, .pause, .preC]

-- ============================================================================
-- § 2: Cross-Dialectal Generalization
-- ============================================================================

/-- Pre-consonantal deletion ≥ pre-vocalic in every dialect. -/
theorem preC_ge_preV (d : Dialect) :
    deletionRate d .preC ≥ deletionRate d .preV := by
  cases d <;> native_decide

/-- Pre-consonantal deletion ≥ pre-pausal in every dialect except Chicano. -/
theorem preC_ge_pause_non_chicano (d : Dialect) (h : d ≠ .chicano) :
    deletionRate d .preC ≥ deletionRate d .pause := by
  cases d <;> simp_all <;> native_decide

/-- Chicano is exceptional: pre-vocalic > pre-pausal. -/
theorem chicano_preV_gt_pause :
    deletionRate .chicano .preV > deletionRate .chicano .pause := by
  native_decide

/-- In all non-Chicano dialects, pre-pausal ≥ pre-vocalic. -/
theorem pause_ge_preV_non_chicano (d : Dialect) (h : d ≠ .chicano) :
    deletionRate d .pause ≥ deletionRate d .preV := by
  cases d <;> simp_all <;> native_decide

-- ============================================================================
-- § 3: Morphological Conditioning Data
-- ============================================================================

/-- Morphological status of the word-final t/d.
    @cite{coetzee-pater-2011} table (7), p. 407. -/
inductive MorphStatus where
  | regularPast   -- *missed* (past tense suffix)
  | semiWeakPast  -- *kept* (semi-weak past)
  | monomorpheme  -- *mist* (monomorphemic)
  deriving DecidableEq, BEq, Repr

/-- Dialect labels for table (7) morphological data.
    Note: table (7) uses different dialects than table (10) — Philadelphia
    English replaces AAVE; Jamaican and Trinidad have no morph data. -/
inductive MorphDialect where
  | philadelphia  -- Philadelphia English (Guy 1991b)
  | chicano       -- Chicano English (Santa Ana 1992)
  | tejano        -- Tejano English (Bayley 1995)
  deriving DecidableEq, BEq, Repr

/-- Deletion rate by morphological status and dialect (percentages).
    From @cite{coetzee-pater-2011} table (7). -/
def morphDeletionRate : MorphDialect → MorphStatus → Nat
  | .philadelphia, .regularPast => 17 | .philadelphia, .semiWeakPast => 34
  | .philadelphia, .monomorpheme => 38
  | .chicano,      .regularPast => 26 | .chicano,      .semiWeakPast => 41
  | .chicano,      .monomorpheme => 58
  | .tejano,       .regularPast => 24 | .tejano,       .semiWeakPast => 34
  | .tejano,       .monomorpheme => 56

/-- Monomorpheme deletion ≥ regular past in every dialect with data.
    This is the morphological generalization from §3.1. -/
theorem mono_ge_regular (d : MorphDialect) :
    morphDeletionRate d .monomorpheme ≥ morphDeletionRate d .regularPast := by
  cases d <;> native_decide

/-- Semi-weak past ≥ regular past in every dialect with data.
    This captures the three-way morphological gradient from §3.1. -/
theorem semiWeak_ge_regular (d : MorphDialect) :
    morphDeletionRate d .semiWeakPast ≥ morphDeletionRate d .regularPast := by
  cases d <;> native_decide

end Fragments.English.TDDeletion
