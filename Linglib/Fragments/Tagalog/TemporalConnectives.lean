import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect
import Linglib.Fragments.English.TemporalExpressions

/-!
# Tagalog Temporal Connectives Fragment
@cite{dell-1983} @cite{rett-2020}

Cross-linguistic data on Tagalog *bago* ('before') and *pagkatapos* ('after')
showing overt morphological marking of the aspectual coercion that English
leaves covert.

Tagalog distinguishes two perfective aspects in embedded temporal clauses:
- **PFV.NEUT** (neutral, non-culminating perfective): yields start-point reading
- **AIA** (ability-and-involuntary-action, culminating perfective): yields
  finish-point reading

This morphological evidence supports @cite{rett-2020}'s ambiguity analysis:
the covert INCHOAT/COMPLET operators posited for English correspond to
overt aspect markers in Tagalog.

-/

namespace Fragments.Tagalog.TemporalConnectives

open Semantics.Lexical.Verb.ViewpointAspect
open Fragments.English.TemporalExpressions (Reading TemporalExprEntry ComplementType)

-- ============================================================================
-- § 1: Tagalog Aspect–Reading Mapping
-- ============================================================================

/-- A Tagalog temporal clause's reading is determined by the overt aspect marking
    on the embedded verb. This structure pairs the morphological form with its
    resulting temporal interpretation. -/
structure AspectReadingEntry where
  /-- Connective form (Tagalog) -/
  connective : String
  /-- Description of the aspect form -/
  aspectLabel : String
  /-- Viewpoint aspect category -/
  aspect : ViewpointAspectB
  /-- Whether this is the culminating (AIA) or non-culminating (NEUT) variant -/
  culminating : Bool
  /-- Resulting reading of the temporal clause -/
  reading : Reading
  deriving Repr, BEq

-- ============================================================================
-- § 2: *bago* ('before') Entries (Rett 2020, ex. 12; Dell 1983)
-- ============================================================================

/-- *bago* + PFV.NEUT → before-start (≺ initial).
    @cite{rett-2020} ex. (12a): "She left before he swept the floor" with neutral
    perfective yields the default initial-point reading. -/
def bago_neut : AspectReadingEntry :=
  { connective := "bago"
  , aspectLabel := "PFV.NEUT"
  , aspect := .perfective
  , culminating := false
  , reading := .beforeStart }

/-- *bago* + AIA → before-finish (≺ final).
    @cite{rett-2020} ex. (12b): "She left before he swept the floor" with AIA
    (ability-and-involuntary-action) yields the coerced final-point reading.
    AIA is the morphological realization of COMPLET. -/
def bago_aia : AspectReadingEntry :=
  { connective := "bago"
  , aspectLabel := "AIA"
  , aspect := .perfective
  , culminating := true
  , reading := .beforeFinish }

-- ============================================================================
-- § 3: *pagkatapos* ('after') Entries
-- ============================================================================

/-- *pagkatapos* + PFV.NEUT → after-start (≻ initial).
    Non-culminating perfective with *after* yields the coerced initial-point
    reading: the main event follows the onset of the embedded event.
    PFV.NEUT is the morphological realization of INCHOAT. -/
def pagkatapos_neut : AspectReadingEntry :=
  { connective := "pagkatapos"
  , aspectLabel := "PFV.NEUT"
  , aspect := .perfective
  , culminating := false
  , reading := .afterStart }

/-- *pagkatapos* + AIA → after-finish (≻ final).
    Culminating perfective with *after* yields the default final-point reading:
    the main event follows the culmination of the embedded event. -/
def pagkatapos_aia : AspectReadingEntry :=
  { connective := "pagkatapos"
  , aspectLabel := "AIA"
  , aspect := .perfective
  , culminating := true
  , reading := .afterFinish }

-- ============================================================================
-- § 4: Connective Entries
-- ============================================================================

/-- Tagalog *bago* ('before'): licenses NPIs, non-veridical.
    Mirrors English *before* on all semantic properties. -/
def bago : TemporalExprEntry :=
  { form := "bago"
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

/-- Tagalog *pagkatapos* ('after'): does not license NPIs, veridical.
    Mirrors English *after* on all semantic properties. -/
def pagkatapos : TemporalExprEntry :=
  { form := "pagkatapos"
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

/-- Same connective (*bago*), same viewpoint aspect (perfective), but different
    culmination marking → different temporal reading. -/
theorem same_connective_different_reading :
    bago_neut.connective = bago_aia.connective ∧
    bago_neut.reading ≠ bago_aia.reading := by
  exact ⟨rfl, by decide⟩

/-- The culminating variant (AIA) yields the final-point reading,
    the non-culminating variant (NEUT) yields the initial-point reading. -/
theorem culmination_determines_reading :
    (bago_aia.culminating = true ∧ bago_aia.reading = .beforeFinish) ∧
    (bago_neut.culminating = false ∧ bago_neut.reading = .beforeStart) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Same connective (*pagkatapos*), same viewpoint aspect (perfective), but
    different culmination marking → different temporal reading. -/
theorem pagkatapos_different_reading :
    pagkatapos_neut.connective = pagkatapos_aia.connective ∧
    pagkatapos_neut.reading ≠ pagkatapos_aia.reading := by
  exact ⟨rfl, by decide⟩

/-- The culmination→reading mapping is consistent across connectives:
    culminating = finish-point, non-culminating = start-point. -/
theorem culmination_symmetry :
    (bago_aia.culminating = true ∧ pagkatapos_aia.culminating = true) ∧
    (bago_neut.culminating = false ∧ pagkatapos_neut.culminating = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- The veridicality asymmetry holds: *bago* is non-veridical, *pagkatapos*
    is veridical. -/
theorem veridicality_asymmetry :
    bago.complementVeridical = false ∧ pagkatapos.complementVeridical = true :=
  ⟨rfl, rfl⟩

/-- The NPI asymmetry holds: *bago* licenses NPIs, *pagkatapos* does not. -/
theorem npi_asymmetry :
    bago.licensesNPI = true ∧ pagkatapos.licensesNPI = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 6: Cross-Linguistic Agreement
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Tagalog *bago* and English *before* agree on all semantic properties. -/
theorem bago_matches_before :
    bago.order = before_.order ∧
    bago.licensesNPI = before_.licensesNPI ∧
    bago.defaultReading = before_.defaultReading ∧
    bago.coercedReading = before_.coercedReading ∧
    bago.complementVeridical = before_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Tagalog *pagkatapos* and English *after* agree on all semantic properties. -/
theorem pagkatapos_matches_after :
    pagkatapos.order = after_.order ∧
    pagkatapos.licensesNPI = after_.licensesNPI ∧
    pagkatapos.defaultReading = after_.defaultReading ∧
    pagkatapos.coercedReading = after_.coercedReading ∧
    pagkatapos.complementVeridical = after_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Fragments.Tagalog.TemporalConnectives
