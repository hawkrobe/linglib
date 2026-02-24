/-!
# Ozaki (2025) — Japanese Accusative/Ablative Alternation: Data

Empirical data from Ozaki (2025, CLS 61) on Japanese departure verbs
that alternate between accusative *-o* and ablative *kara* marking
on the source argument.

## Key Empirical Facts

1. **Alternation**: Departure verbs like *hanareru* 'leave' and *deru*
   'exit' allow both ACC and ABL on the source:
   - "Taro-ga Tokyo-**o** hanareta" (ACC)
   - "Taro-ga Tokyo-**kara** hanareta" (ABL)

2. **Argumenthood of source**: The source behaves as an argument regardless
   of case — it can undergo VP ellipsis and long-distance scrambling.

3. **Unaccusativity**: These verbs are unaccusative:
   - Only indirect passive (*-rare*), no direct passive (*-niyotte*)
   - *Nani-o* wh-adjunct test patterns with unaccusatives

## Theory-Neutral

This file contains no theoretical commitments. See Bridge.lean for
connection to dependent case theory and Minimalist syntax.

## References

- Ozaki, S. (2025). Dependent case in Japanese accusative/ablative
  alternation verbs. *CLS 61*.
-/

namespace Phenomena.Case.Ozaki2025.Data

-- ============================================================================
-- § 1: Data Types
-- ============================================================================

/-- Case marking on the source argument of alternation verbs. -/
inductive CaseMarking where
  | accusative   -- *-o*
  | ablative     -- *kara*
  | nominative   -- *-ga*
  | dative       -- *-ni*
  deriving DecidableEq, BEq, Repr

/-- Types of passive in Japanese. -/
inductive PassiveType where
  | direct    -- *-niyotte* agent, agentive verbs only
  | indirect  -- *-rare* adversative, available for unaccusatives
  deriving DecidableEq, BEq, Repr

/-- Diagnostics for argumenthood (vs. adjuncthood). -/
inductive ArgumenthoodDiagnostic where
  | ellipsis                -- VP ellipsis includes the constituent
  | longDistanceScrambling  -- Constituent can scramble long-distance
  deriving DecidableEq, BEq, Repr

/-- Diagnostics for unaccusativity. -/
inductive UnaccusativityDiagnostic where
  | passivization   -- Only indirect passive available
  | naniOWhAdjunct  -- *nani-o* wh-adjunct test: blocked = unaccusative
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Data Structures
-- ============================================================================

/-- A single case alternation datum: a verb form with a source argument
    in a particular case, plus grammaticality. -/
structure AlternationDatum where
  verb : String
  sourceCase : CaseMarking
  grammatical : Bool
  sentence : String
  exampleNum : String
  deriving DecidableEq, BEq, Repr

/-- An unaccusativity diagnostic datum. -/
structure UnaccusativityDatum where
  verb : String
  diagnostic : UnaccusativityDiagnostic
  passiveType : Option PassiveType
  grammatical : Bool
  sentence : String
  exampleNum : String
  deriving DecidableEq, BEq, Repr

/-- An argumenthood diagnostic datum. -/
structure ArgumenthoodDatum where
  verb : String
  sourceCase : CaseMarking
  diagnostic : ArgumenthoodDiagnostic
  grammatical : Bool
  sentence : String
  exampleNum : String
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 3: Alternation Data
-- ============================================================================

/-! ### *hanareru* 'leave' — ACC/ABL alternation (ex. 1) -/

def hanareru_acc : AlternationDatum where
  verb := "hanareru"
  sourceCase := .accusative
  grammatical := true
  sentence := "Taro-ga Tokyo-o hanareta"
  exampleNum := "1a"

def hanareru_abl : AlternationDatum where
  verb := "hanareru"
  sourceCase := .ablative
  grammatical := true
  sentence := "Taro-ga Tokyo-kara hanareta"
  exampleNum := "1b"

/-! ### *deru* 'exit' — ACC/ABL alternation (ex. 9) -/

def deru_acc : AlternationDatum where
  verb := "deru"
  sourceCase := .accusative
  grammatical := true
  sentence := "Taro-ga heya-o deta"
  exampleNum := "9a"

def deru_abl : AlternationDatum where
  verb := "deru"
  sourceCase := .ablative
  grammatical := true
  sentence := "Taro-ga heya-kara deta"
  exampleNum := "9b"

def alternationData : List AlternationDatum :=
  [hanareru_acc, hanareru_abl, deru_acc, deru_abl]

-- ============================================================================
-- § 4: Argumenthood Data
-- ============================================================================

/-! ### VP ellipsis — source elides as argument (ex. 9–10) -/

def deru_ellipsis_acc : ArgumenthoodDatum where
  verb := "deru"
  sourceCase := .accusative
  diagnostic := .ellipsis
  grammatical := true
  sentence := "Taro-ga heya-o deta. Hanako-mo soo shita."
  exampleNum := "9"

def deru_ellipsis_abl : ArgumenthoodDatum where
  verb := "deru"
  sourceCase := .ablative
  diagnostic := .ellipsis
  grammatical := true
  sentence := "Taro-ga heya-kara deta. Hanako-mo soo shita."
  exampleNum := "10"

/-! ### Long-distance scrambling — source scrambles freely (ex. 13) -/

def deru_scrambling_acc : ArgumenthoodDatum where
  verb := "deru"
  sourceCase := .accusative
  diagnostic := .longDistanceScrambling
  grammatical := true
  sentence := "heya-o Hanako-ga [Taro-ga __ deta to] omotta"
  exampleNum := "13a"

def deru_scrambling_abl : ArgumenthoodDatum where
  verb := "deru"
  sourceCase := .ablative
  diagnostic := .longDistanceScrambling
  grammatical := true
  sentence := "heya-kara Hanako-ga [Taro-ga __ deta to] omotta"
  exampleNum := "13b"

def argumenthoodData : List ArgumenthoodDatum :=
  [deru_ellipsis_acc, deru_ellipsis_abl, deru_scrambling_acc, deru_scrambling_abl]

-- ============================================================================
-- § 5: Unaccusativity Data
-- ============================================================================

/-! ### Passive — only indirect passive available (ex. 14, 20) -/

def hanareru_indirect_passive : UnaccusativityDatum where
  verb := "hanareru"
  diagnostic := .passivization
  passiveType := some .indirect
  grammatical := true
  sentence := "Hanako-ga Taro-ni hanare-rare-ta"
  exampleNum := "14"

def hanareru_direct_passive : UnaccusativityDatum where
  verb := "hanareru"
  diagnostic := .passivization
  passiveType := some .direct
  grammatical := false
  sentence := "*Tokyo-ga Taro-niyotte hanare-rare-ta"
  exampleNum := "20"

/-! ### *nani-o* wh-adjunct — blocked with unaccusatives (ex. 26) -/

def hanareru_nanio : UnaccusativityDatum where
  verb := "hanareru"
  diagnostic := .naniOWhAdjunct
  passiveType := none
  grammatical := false
  sentence := "*Taro-ga nani-o Tokyo-o hanareta no"
  exampleNum := "26"

def unaccusativityData : List UnaccusativityDatum :=
  [hanareru_indirect_passive, hanareru_direct_passive, hanareru_nanio]

-- ============================================================================
-- § 6: Verification Theorems
-- ============================================================================

/-- Both ACC and ABL variants are grammatical for alternation verbs. -/
theorem both_variants_grammatical :
    alternationData.all (·.grammatical) = true := by native_decide

/-- All argumenthood diagnostics succeed regardless of case marking. -/
theorem argumenthood_regardless_of_case :
    argumenthoodData.all (·.grammatical) = true := by native_decide

/-- Direct passive is ungrammatical (hallmark of unaccusativity). -/
theorem direct_passive_blocked :
    hanareru_direct_passive.grammatical = false := rfl

/-- Indirect passive is grammatical (expected for unaccusatives). -/
theorem indirect_passive_ok :
    hanareru_indirect_passive.grammatical = true := rfl

/-- *Nani-o* is blocked — patterns with unaccusatives, not transitives. -/
theorem nanio_blocked :
    hanareru_nanio.grammatical = false := rfl

/-- Four alternation data points total. -/
theorem alternation_count : alternationData.length = 4 := rfl

/-- Four argumenthood data points total. -/
theorem argumenthood_count : argumenthoodData.length = 4 := rfl

/-- Three unaccusativity data points total. -/
theorem unaccusativity_count : unaccusativityData.length = 3 := rfl

end Phenomena.Case.Ozaki2025.Data
