import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Fragments.English.TemporalExpressions

/-!
# Serbian Temporal Connectives Fragment
@cite{rett-2020}

Cross-linguistic data on Serbian *pre* ('before') and *posle* ('after')
showing overt viewpoint aspect morphology (PFV/IMPF) in embedded temporal
clauses.

Serbian provides direct morphological evidence for @cite{rett-2020}'s coercion
account: the PFV/IMPF distinction on the embedded verb overtly marks what
English leaves covert (COMPLET/INCHOAT).

- **PFV** (perfective) in *pre*-clauses: yields ≺ final reading
  (bounded/telic, like English COMPLET coercion)
- **IMPF** (imperfective) in *pre*-clauses: yields ≺ initial reading
  (unbounded/atelic, the default)

This parallels the Tagalog PFV.NEUT/AIA distinction (see
`Fragments.Tagalog.TemporalConnectives`) but uses the standard
PFV/IMPF opposition rather than Tagalog's finer-grained system.

-/

namespace Fragments.Slavic.Serbian.TemporalConnectives

open Semantics.Tense.Aspect.Core
open Fragments.English.TemporalExpressions (Reading TemporalExprEntry ComplementType)

-- ============================================================================
-- § 1: Aspect–Reading Mapping
-- ============================================================================

/-- A Serbian temporal clause's reading is determined by the overt viewpoint
    aspect on the embedded verb. Reuses Tagalog's structure type since the
    pattern is the same: overt aspect → temporal reading. -/
structure AspectReadingEntry where
  /-- Connective form (Serbian) -/
  connective : String
  /-- Description of the aspect form -/
  aspectLabel : String
  /-- Viewpoint aspect category -/
  aspect : ViewpointAspectB
  /-- Whether the aspect forces a bounded (telic/culminating) reading -/
  culminating : Bool
  /-- Resulting reading of the temporal clause -/
  reading : Reading
  deriving Repr, BEq

-- ============================================================================
-- § 2: *pre* ('before') entries
-- ============================================================================

/-- *pre* + IMPF → before-start (≺ initial).
    Imperfective in *pre*-clauses yields the default initial-point reading:
    the main event precedes the onset of the unbounded embedded event.
    This is the unmarked/default reading, parallel to English *before* with
    an atelic complement and Tagalog *bago* + PFV.NEUT. -/
def pre_impf : AspectReadingEntry :=
  { connective := "pre"
  , aspectLabel := "IMPF"
  , aspect := .imperfective
  , culminating := false
  , reading := .beforeStart }

/-- *pre* + PFV → before-finish (≺ final).
    Perfective in *pre*-clauses forces the bounded/coerced final-point reading:
    the main event precedes the culmination of the embedded event.
    This is the overt realization of English COMPLET, parallel to
    Tagalog *bago* + AIA. -/
def pre_pfv : AspectReadingEntry :=
  { connective := "pre"
  , aspectLabel := "PFV"
  , aspect := .perfective
  , culminating := true
  , reading := .beforeFinish }

-- ============================================================================
-- § 3: *posle* ('after') entries
-- ============================================================================

/-- *posle* + PFV → after-finish (≻ final).
    Perfective in *posle*-clauses yields the default final-point reading:
    the main event follows the culmination of the embedded event.
    This is the unmarked reading for *after*. -/
def posle_pfv : AspectReadingEntry :=
  { connective := "posle"
  , aspectLabel := "PFV"
  , aspect := .perfective
  , culminating := true
  , reading := .afterFinish }

/-- *posle* + IMPF → after-start (≻ initial).
    Imperfective in *posle*-clauses forces the coerced initial-point reading:
    the main event follows the onset of the unbounded embedded event.
    This is the overt realization of English INCHOAT. -/
def posle_impf : AspectReadingEntry :=
  { connective := "posle"
  , aspectLabel := "IMPF"
  , aspect := .imperfective
  , culminating := false
  , reading := .afterStart }

-- ============================================================================
-- § 4: Connective Entries
-- ============================================================================

/-- Serbian *pre* ('before'): licenses NPIs, non-veridical.
    Mirrors English *before* on all semantic properties. -/
def pre : TemporalExprEntry :=
  { form := "pre"
  , complementType := .clausal
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := false
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Serbian *posle* ('after'): does not license NPIs, veridical.
    Mirrors English *after* on all semantic properties. -/
def posle : TemporalExprEntry :=
  { form := "posle"
  , complementType := .clausal
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- Same connective (*pre*), but different aspect → different temporal reading. -/
theorem pre_aspect_determines_reading :
    pre_impf.connective = pre_pfv.connective ∧
    pre_impf.reading ≠ pre_pfv.reading := by
  exact ⟨rfl, by decide⟩

/-- Same connective (*posle*), but different aspect → different temporal reading. -/
theorem posle_aspect_determines_reading :
    posle_pfv.connective = posle_impf.connective ∧
    posle_pfv.reading ≠ posle_impf.reading := by
  exact ⟨rfl, by decide⟩

/-- The aspect–reading mapping is symmetric across connectives:
    PFV gives bounded (culminating) readings for both *pre* and *posle*;
    IMPF gives unbounded (non-culminating) readings for both. -/
theorem aspect_reading_symmetry :
    (pre_pfv.culminating = true ∧ posle_pfv.culminating = true) ∧
    (pre_impf.culminating = false ∧ posle_impf.culminating = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The veridicality asymmetry holds cross-linguistically:
    *pre* is non-veridical, *posle* is veridical. -/
theorem veridicality_asymmetry :
    pre.complementVeridical = false ∧ posle.complementVeridical = true :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Cross-Linguistic Agreement
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Serbian *pre* and English *before* agree on all semantic properties. -/
theorem pre_matches_before :
    pre.order = before_.order ∧
    pre.licensesNPI = before_.licensesNPI ∧
    pre.defaultReading = before_.defaultReading ∧
    pre.coercedReading = before_.coercedReading ∧
    pre.complementVeridical = before_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Serbian *posle* and English *after* agree on all semantic properties. -/
theorem posle_matches_after :
    posle.order = after_.order ∧
    posle.licensesNPI = after_.licensesNPI ∧
    posle.defaultReading = after_.defaultReading ∧
    posle.coercedReading = after_.coercedReading ∧
    posle.complementVeridical = after_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Fragments.Slavic.Serbian.TemporalConnectives
