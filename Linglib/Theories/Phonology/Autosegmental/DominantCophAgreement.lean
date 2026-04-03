import Linglib.Theories.Phonology.Autosegmental.BasemapCorrespondence
import Linglib.Theories.Phonology.CophonologyTheory

/-!
# Dominant Cophonology ↔ Tonal Overwrite Agreement
@cite{rolle-2018}

This file proves the **general agreement** between the two parallel
formalisms for dominant grammatical tone in @cite{rolle-2018}:

1. **Direct**: `tonalOverwrite` — a functional operation replacing tones
2. **Constraint-based**: `cophonologicalEval` — OT evaluation under a
   morpheme-specific subranking that promotes MxBM-C (basemap faithfulness)

The key insight is that when MxBM-C is the top-ranked constraint (via
cophonological subranking), OT evaluation necessarily selects
basemap-faithful candidates — which are exactly the `tonalOverwrite`
outputs. The per-tableau agreement theorems in study files (e.g.,
`AkinboFwangwar2026.t24_winner_agrees_with_deriveVerb`) are instances
of this general result.

## Proof structure

```
optimal_zero_first (OT.lean)
   "if any candidate has 0 violations on the top constraint,
    every optimal candidate does too"
         ↓
dominant_coph_selects_basemap_faithful
   "when MxBM-C is in the subranking, every optimal candidate
    has extractTier c = basemapTier"
         ↓
dominant_coph_agrees_with_tonalOverwrite
   "every optimal candidate under the dominant cophonology agrees
    with tonalOverwrite — the two formalisms are equivalent"
```
-/

namespace Theories.Phonology.Autosegmental.DominantCophAgreement

open Theories.Phonology.Autosegmental.GrammaticalTone
open Theories.Phonology.Autosegmental.RegisterTier (ToneFeature)
open Theories.Phonology.Autosegmental.BasemapCorrespondence
open Theories.Phonology.CophonologyTheory (mergeRanking cophonologicalEval)
open Core.OT (NamedConstraint buildTableau optimal_zero_first)
open Core.ConstraintEvaluation (OTTableau optimal_subset)

-- ============================================================================
-- § 1: Dominant Cophonology Selects Basemap-Faithful Candidates
-- ============================================================================

/-- **The general agreement theorem**: when MxBM-C (basemap faithfulness)
    is in the cophonological subranking, every OT-optimal candidate is
    basemap-faithful — its tonal tier exactly matches the basemap output.

    This is the mathematical core of @cite{rolle-2018} Ch 5: dominant GT
    is not a special rule but a consequence of promoting a faithfulness
    constraint. The constraint forces the matrix output to correspond to
    the basemap output, which is independent of the target's underlying
    tones (`basemapOutput_tone_independent_whole`). -/
theorem dominant_coph_selects_basemap_faithful
    {C : Type}
    (basemapTier : List ToneFeature)
    (extractTier : C → List ToneFeature)
    (defaultRanking : List (NamedConstraint C))
    (candidates : List C) (h : candidates ≠ [])
    (hLen : ∀ c ∈ candidates, (extractTier c).length = basemapTier.length)
    (hFaithful : ∃ c ∈ candidates, extractTier c = basemapTier)
    : let mxbmc := mkBasemapConstraint basemapTier extractTier
      ∀ c ∈ cophonologicalEval defaultRanking [mxbmc] candidates h,
        extractTier c = basemapTier := by
  intro mxbmc c hc
  -- Step 1: Unfold cophonologicalEval — the effective ranking starts with mxbmc
  simp only [cophonologicalEval, mergeRanking] at hc
  -- Step 2: The faithful candidate has 0 MxBM-C violations
  have hExists : ∃ c₀ ∈ candidates, mxbmc.eval c₀ = 0 := by
    obtain ⟨c₀, hc₀_mem, hc₀_eq⟩ := hFaithful
    exact ⟨c₀, hc₀_mem, by simp [mxbmc, mkBasemapConstraint, hc₀_eq,
      basemapViolations_self_eq_zero]⟩
  -- Step 3: By optimal_zero_first, every optimal candidate has 0 violations
  have hZero := optimal_zero_first candidates mxbmc _ h hExists c hc
  -- Step 4: 0 violations implies extractTier c = basemapTier
  simp only [mxbmc, mkBasemapConstraint] at hZero
  exact basemapViolations_eq_zero_imp (extractTier c) basemapTier
    (hLen c (optimal_subset _ c hc)) hZero

-- ============================================================================
-- § 2: Agreement with tonalOverwrite
-- ============================================================================

/-- **Dominant cophonology agrees with tonalOverwrite**: for whole-word
    single-tone replacement, OT evaluation under the dominant cophonology
    selects candidates whose tonal tier matches the direct `tonalOverwrite`
    operation.

    This connects the two formalisms of dominant GT:
    1. **Direct** (`tonalOverwrite`): replaces all tones with the melody
    2. **Constraint-based** (`cophonologicalEval` with MxBM-C): selects
       candidates faithful to the basemap output

    The connection goes through `tonalOverwrite_basemap_faithful`:
    the tonalOverwrite output equals the basemap output, and
    `dominant_coph_selects_basemap_faithful` ensures the OT evaluation
    selects exactly the basemap-faithful candidates. -/
theorem dominant_coph_agrees_with_tonalOverwrite
    {S C : Type} [DecidableEq S] [BEq S] [Repr S]
    (host : List (TBU S)) (t defaultTone : ToneFeature)
    (extractTier : C → List ToneFeature)
    (defaultRanking : List (NamedConstraint C))
    (candidates : List C) (h : candidates ≠ [])
    (hLen : ∀ c ∈ candidates,
      (extractTier c).length =
        (tonalTier (basemapOutput host ⟨"", [t], .whole⟩ defaultTone)).length)
    (hFaithful : ∃ c ∈ candidates,
      extractTier c = tonalTier (basemapOutput host ⟨"", [t], .whole⟩ defaultTone))
    : let spec : Spec := ⟨"", [t], .whole⟩
      let baseTier := tonalTier (basemapOutput host spec defaultTone)
      let mxbmc := mkBasemapConstraint baseTier extractTier
      ∀ c ∈ cophonologicalEval defaultRanking [mxbmc] candidates h,
        extractTier c = tonalTier (tonalOverwrite host spec) := by
  intro spec baseTier mxbmc c hc
  have hFaith := dominant_coph_selects_basemap_faithful
    baseTier extractTier defaultRanking candidates h hLen hFaithful c hc
  rw [hFaith]
  exact (tonalOverwrite_basemap_faithful host t defaultTone).symm

end Theories.Phonology.Autosegmental.DominantCophAgreement
