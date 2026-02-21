import Linglib.Phenomena.Conditionals.Studies.Mizuno2024.Data
import Linglib.Theories.Semantics.Conditionals.Anderson

/-!
# Mizuno (2024) — Bridge @cite{mizuno-2024}

Connects the crosslinguistic data from Mizuno (2024) to the Anderson
conditional strategy typology in `Semantics.Conditionals.Anderson`.

## Bridge Structure

1. **Strategy classification**: per-language assignment of `MarkingStrategy`,
   expressing which strategy each language uses for Anderson conditionals.
   These are empirical facts about languages, expressed using theoretical
   vocabulary — the reason they live in Bridge rather than Data.
2. **Per-datum verification**: each datum's `hasXMarking` agrees with its
   language's strategy assignment.
3. **FLV correlation**: per-language verification that Anderson X-marking
   availability co-varies with FLV X-marking availability.
-/

namespace Phenomena.Conditionals.Studies.Mizuno2024.Bridge

open Semantics.Conditionals.Anderson (MarkingStrategy)

-- ════════════════════════════════════════════════════════════════
-- § Per-Language Strategy Classification
-- ════════════════════════════════════════════════════════════════

/-- English uses X-marking for Anderson conditionals:
    X-marking is felicitous (ex. 1), O-marking is not (ex. 2–3). -/
def english_strategy : MarkingStrategy := .xMarking

/-- Japanese uses O-marking for Anderson conditionals:
    O-marking is felicitous (ex. 4a), X-marking is not (ex. 4b). -/
def japanese_strategy : MarkingStrategy := .oMarking

/-- Mandarin uses O-marking for Anderson conditionals:
    O-marking is felicitous (ex. 13a without le), X-marking is not
    (ex. 13a with le). -/
def mandarin_strategy : MarkingStrategy := .oMarking

-- ════════════════════════════════════════════════════════════════
-- § Strategy–Datum Agreement
-- ════════════════════════════════════════════════════════════════

/-- English: strategy predicts X-marking = felicitous datum's marking. -/
theorem english_strategy_matches :
    english_strategy.hasXMarking = english_xMarking.hasXMarking := rfl

/-- Japanese: strategy predicts no X-marking = felicitous datum's marking. -/
theorem japanese_strategy_matches :
    japanese_strategy.hasXMarking = japanese_oMarking.hasXMarking := rfl

/-- Mandarin: strategy predicts no X-marking = felicitous datum's marking. -/
theorem mandarin_strategy_matches :
    mandarin_strategy.hasXMarking = mandarin_oMarking.hasXMarking := rfl

-- ════════════════════════════════════════════════════════════════
-- § Per-Datum Marking Verification
-- ════════════════════════════════════════════════════════════════

theorem english_xMarking_has_xMarking :
    english_xMarking.hasXMarking = true := rfl

theorem english_oMarking_no_xMarking :
    english_oMarking.hasXMarking = false := rfl

theorem japanese_oMarking_no_xMarking :
    japanese_oMarking.hasXMarking = false := rfl

theorem japanese_xMarking_has_xMarking :
    japanese_xMarking.hasXMarking = true := rfl

theorem mandarin_oMarking_no_xMarking :
    mandarin_oMarking.hasXMarking = false := rfl

theorem mandarin_xMarking_has_xMarking :
    mandarin_xMarking.hasXMarking = true := rfl

-- ════════════════════════════════════════════════════════════════
-- § FLV Correlation Verification
-- ════════════════════════════════════════════════════════════════

/-- English: X-marking for Anderson ↔ X-marking for FLV. -/
theorem english_flv_correlation :
    english_strategy.hasXMarking = english_flv.xMarkingAvailable := rfl

/-- Japanese: no X-marking for Anderson ↔ no X-marking for FLV. -/
theorem japanese_flv_correlation :
    japanese_strategy.hasXMarking = japanese_flv.xMarkingAvailable := rfl

/-- Mandarin: no X-marking for Anderson ↔ no X-marking for FLV. -/
theorem mandarin_flv_correlation :
    mandarin_strategy.hasXMarking = mandarin_flv.xMarkingAvailable := rfl

end Phenomena.Conditionals.Studies.Mizuno2024.Bridge
