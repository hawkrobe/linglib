import Linglib.Theories.TruthConditional.Verb.ViewpointAspect
import Linglib.Fragments.English.TemporalExpressions

/-!
# Tagalog Temporal Connectives Fragment

Cross-linguistic data on Tagalog *bago* ('before') showing overt morphological
marking of the aspectual coercion that English leaves covert.

Tagalog distinguishes two perfective aspects in embedded temporal clauses:
- **PFV.NEUT** (neutral, non-culminating perfective): yields ≺ initial reading
- **AIA** (ability-and-involuntary-action, culminating perfective): yields ≺ final reading

This morphological evidence supports Rett's (2020) ambiguity analysis:
the covert INCHOAT/COMPLET operators posited for English correspond to
overt aspect markers in Tagalog.

## References

- Dell, F. (1983). An aspectual distinction in Tagalog. *Oceanic Linguistics* 22/23.
- Rett, J. (2020). Eliminating EARLIEST. *Sinn und Bedeutung* 24, §2.4.
-/

namespace Fragments.Tagalog.TemporalConnectives

open TruthConditional.Verb.ViewpointAspect
open Fragments.English.TemporalExpressions (Reading)

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
-- § 2: Entries (Rett 2020, ex. 12; Dell 1983)
-- ============================================================================

/-- *bago* + PFV.NEUT → before-start (≺ initial).
    Rett (2020) ex. (12a): "She left before he swept the floor" with neutral
    perfective yields the default initial-point reading. -/
def bago_neut : AspectReadingEntry :=
  { connective := "bago"
  , aspectLabel := "PFV.NEUT"
  , aspect := .perfective
  , culminating := false
  , reading := .beforeStart }

/-- *bago* + AIA → before-finish (≺ final).
    Rett (2020) ex. (12b): "She left before he swept the floor" with AIA
    (ability-and-involuntary-action) yields the coerced final-point reading.
    AIA is the morphological realization of COMPLET. -/
def bago_aia : AspectReadingEntry :=
  { connective := "bago"
  , aspectLabel := "AIA"
  , aspect := .perfective
  , culminating := true
  , reading := .beforeFinish }

-- ============================================================================
-- § 3: Verification
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

end Fragments.Tagalog.TemporalConnectives
