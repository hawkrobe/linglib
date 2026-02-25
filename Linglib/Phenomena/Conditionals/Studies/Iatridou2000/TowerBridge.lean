import Linglib.Phenomena.Conditionals.Studies.Iatridou2000.Data
import Linglib.Theories.Semantics.Conditionals.Iatridou
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

/-!
# Iatridou (2000) — ContextTower Bridge @cite{iatridou-2000}

End-to-end derivation chain connecting the ContextTower infrastructure to
the counterfactual morphology data in Iatridou (2000). The core insight:
ExclF (the Exclusion Feature) is literally `origin ≠ innermost` on the
tower, and `subjShift` / `temporalShift` produce ExclFs.

## Derivation Chain

```
Core.Context.Tower (ContextTower, push, origin, innermost)
    ↓
Core.Context.Shifts (temporalShift, subjShift from Mood.Basic)
    ↓
Theories.Semantics.Conditionals.Iatridou (ExclF, CounterfactualType)
    ↓
This file: tower depth matches pastLayers in the morphological data
    ↓
Phenomena.Conditionals.Studies.Iatridou2000.Data (english_pastCF, etc.)
```

## Key Results

1. **1 past layer = 1 shift = depth 1**: FLV and PresCF
2. **2 past layers = 2 shifts = depth 2**: PastCF
3. **subjShift produces modal ExclF**: counterfactual world ≠ actual world
4. **temporalShift produces temporal ExclF**: topic time ≠ speech time
5. **Origin stability**: the actual context is preserved at arbitrary depth

## References

- Iatridou, S. (2000). The grammatical ingredients of counterfactuality.
  *Linguistic Inquiry* 31(2): 231–270.
-/

namespace Phenomena.Conditionals.Studies.Iatridou2000.TowerBridge

open Core.Context
open Semantics.Conditionals.Iatridou
open Semantics.Mood (subjShift)

-- ============================================================================
-- § Tower Contexts
-- ============================================================================

/-- A counterfactual context with distinguishable worlds and times.
    Position is Unit (irrelevant for counterfactual semantics). -/
abbrev CFCtx := KContext Bool Unit Unit ℤ

/-- The actual context: world = true (actual), time = 0 (now). -/
def actualCtx : CFCtx :=
  { world := true, agent := (), addressee := (), time := 0, position := () }

/-- Root tower: the actual speech-act context, depth 0. -/
def actualTower : ContextTower CFCtx := ContextTower.root actualCtx

-- ============================================================================
-- § FLV / PresCF: 1 Modal ExclF = Depth 1
-- ============================================================================

/-- FLV/PresCF: one subjunctive shift to a counterfactual world.
    The counterfactual world (false) differs from the actual world (true). -/
def presCFTower : ContextTower CFCtx :=
  actualTower.push (subjShift false 0)

/-- The tower has depth 1 — matching 1 past morpheme layer. -/
theorem presCF_depth : presCFTower.depth = 1 := rfl

/-- Modal ExclF holds: counterfactual world ≠ actual world. -/
theorem presCF_modal_exclF :
    ExclF .modal presCFTower := by
  unfold ExclF presCFTower actualTower actualCtx subjShift; decide

/-- Temporal ExclF does NOT hold: time is unchanged (0 = 0). -/
theorem presCF_no_temporal_exclF :
    ¬ ExclF .temporal presCFTower := by
  unfold ExclF presCFTower actualTower actualCtx subjShift; decide

/-- Tower depth (1) matches English FLV past layers (1). -/
theorem flv_tower_depth_matches_data :
    presCFTower.depth = english_flv.pastLayers := rfl

/-- Tower depth (1) matches English PresCF past layers (1). -/
theorem presCF_tower_depth_matches_data :
    presCFTower.depth = english_presCF.pastLayers := rfl

-- ============================================================================
-- § PastCF: 2 ExclFs = Depth 2
-- ============================================================================

/-- PastCF: two shifts — one modal (subjunctive, world shift) and one
    temporal (additional past layer, time shift to -5).

    The two shifts produce a tower of depth 2 with both modal and temporal
    ExclF active. This is why PastCF has two layers of past morphology. -/
def pastCFTower : ContextTower CFCtx :=
  presCFTower.push (temporalShift (-5))

/-- Tower depth is 2 — matching 2 past morpheme layers. -/
theorem pastCF_depth : pastCFTower.depth = 2 := rfl

/-- Modal ExclF holds: counterfactual world ≠ actual world.
    The modal shift from presCFTower propagates through. -/
theorem pastCF_modal_exclF :
    ExclF .modal pastCFTower := by
  unfold ExclF pastCFTower presCFTower actualTower actualCtx subjShift; decide

/-- Temporal ExclF holds: shifted time (-5) ≠ speech time (0). -/
theorem pastCF_temporal_exclF :
    ExclF .temporal pastCFTower := by
  unfold ExclF pastCFTower presCFTower actualTower actualCtx subjShift temporalShift; decide

/-- Tower depth (2) matches English PastCF past layers (2). -/
theorem pastCF_tower_depth_matches_data :
    pastCFTower.depth = english_pastCF.pastLayers := rfl

/-- Tower depth (2) matches Greek PastCF past layers (2). -/
theorem pastCF_tower_depth_matches_greek :
    pastCFTower.depth = greek_pastCF.pastLayers := rfl

-- ============================================================================
-- § Origin Stability in Counterfactuals
-- ============================================================================

/-- Even in a PastCF tower (depth 2), the origin context is preserved.
    The actual world and speech time are always accessible at depth 0. -/
theorem pastCF_origin_preserved :
    pastCFTower.origin = actualCtx := rfl

end Phenomena.Conditionals.Studies.Iatridou2000.TowerBridge
