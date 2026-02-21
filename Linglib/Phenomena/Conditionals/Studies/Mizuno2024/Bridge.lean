import Linglib.Phenomena.Conditionals.Studies.Mizuno2024.Data
import Linglib.Theories.Semantics.Conditionals.Anderson

/-!
# Mizuno (2024) — Bridge @cite{mizuno-2024}

Connects the crosslinguistic data from Mizuno (2024) to the Anderson
conditional strategy typology in `Semantics.Conditionals.Anderson`.

## Bridge Structure

1. **Strategy classification**: per-datum verification that each language's
   felicitous form matches the predicted marking strategy.
2. **ExclF connection**: X-marking produces ExclF, O-marking does not —
   verified against the strategy properties.
3. **FLV correlation**: per-language verification that Anderson X-marking
   availability co-varies with FLV X-marking availability.
-/

namespace Phenomena.Conditionals.Studies.Mizuno2024.Bridge

open Semantics.Conditionals.Anderson (MarkingStrategy)

-- ════════════════════════════════════════════════════════════════
-- § Strategy Classification
-- ════════════════════════════════════════════════════════════════

/-- English uses X-marking for Anderson conditionals. -/
def english_strategy : MarkingStrategy := .xMarking

/-- Japanese uses O-marking for Anderson conditionals. -/
def japanese_strategy : MarkingStrategy := .oMarking

/-- Mandarin uses O-marking for Anderson conditionals. -/
def mandarin_strategy : MarkingStrategy := .oMarking

-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Marking Verification
-- ════════════════════════════════════════════════════════════════

/-- English X-marking datum has X-marking. -/
theorem english_xMarking_has_xMarking :
    english_xMarking.hasXMarking = true := rfl

/-- English O-marking datum lacks X-marking. -/
theorem english_oMarking_no_xMarking :
    english_oMarking.hasXMarking = false := rfl

/-- Japanese O-marking datum lacks X-marking. -/
theorem japanese_oMarking_no_xMarking :
    japanese_oMarking.hasXMarking = false := rfl

/-- Japanese X-marking datum has X-marking. -/
theorem japanese_xMarking_has_xMarking :
    japanese_xMarking.hasXMarking = true := rfl

/-- Mandarin O-marking datum lacks X-marking. -/
theorem mandarin_oMarking_no_xMarking :
    mandarin_oMarking.hasXMarking = false := rfl

/-- Mandarin X-marking datum has X-marking. -/
theorem mandarin_xMarking_has_xMarking :
    mandarin_xMarking.hasXMarking = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § Strategy–Datum Agreement
-- ════════════════════════════════════════════════════════════════

/-- English: the X-marking strategy predicts X-marking. -/
theorem english_strategy_xMarking :
    english_strategy.hasXMarking = english_xMarking.hasXMarking := rfl

/-- Japanese: the O-marking strategy predicts no X-marking. -/
theorem japanese_strategy_no_xMarking :
    japanese_strategy.hasXMarking = japanese_oMarking.hasXMarking := rfl

/-- Mandarin: the O-marking strategy predicts no X-marking. -/
theorem mandarin_strategy_no_xMarking :
    mandarin_strategy.hasXMarking = mandarin_oMarking.hasXMarking := rfl

-- ════════════════════════════════════════════════════════════════
-- § ExclF Connection
-- ════════════════════════════════════════════════════════════════

/-- English X-marking strategy produces ExclF (modal world exclusion). -/
theorem english_produces_exclF :
    english_strategy.producesExclF = true := rfl

/-- Japanese O-marking strategy does not produce ExclF. -/
theorem japanese_no_exclF :
    japanese_strategy.producesExclF = false := rfl

/-- Mandarin O-marking strategy does not produce ExclF. -/
theorem mandarin_no_exclF :
    mandarin_strategy.producesExclF = false := rfl

/-- English X-marking requires "actually" to recover the actual world. -/
theorem english_requires_actually :
    english_strategy.requiresActuallyOperator = true := rfl

/-- Japanese O-marking does not require "actually". -/
theorem japanese_no_actually_required :
    japanese_strategy.requiresActuallyOperator = false := rfl

-- ════════════════════════════════════════════════════════════════
-- § FLV Correlation Verification
-- ════════════════════════════════════════════════════════════════

/-- English: X-marking for Anderson ↔ X-marking for FLV. -/
theorem english_flv_correlation :
    english_strategy.flvXMarkingAvailable = english_flv.xMarkingAvailable := rfl

/-- Japanese: no X-marking for Anderson ↔ no X-marking for FLV. -/
theorem japanese_flv_correlation :
    japanese_strategy.flvXMarkingAvailable = japanese_flv.xMarkingAvailable := rfl

/-- Mandarin: no X-marking for Anderson ↔ no X-marking for FLV. -/
theorem mandarin_flv_correlation :
    mandarin_strategy.flvXMarkingAvailable = mandarin_flv.xMarkingAvailable := rfl

end Phenomena.Conditionals.Studies.Mizuno2024.Bridge
