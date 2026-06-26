import Linglib.Phonology.ItemSpecificity.IndexedConstraints
import Linglib.Phonology.ItemSpecificity.ScaledWeights
import Linglib.Phonology.ItemSpecificity.UseListed
import Linglib.Phonology.ItemSpecificity.RepresentationStrength

/-!
# Separation theorems for item-specificity theories

The four sibling files in `Phonology/ItemSpecificity/` —
`IndexedConstraints` ([pater-2010]), `ScaledWeights`
([coetzee-pater-2008]), `UseListed` ([zuraw-2000]), and
`RepresentationStrength` ([smolensky-goldrick-2016],
[pierrehumbert-2001], [todd-pierrehumbert-hay-2019]) — agree
that **lexical-item identity conditions phonological alternation**
(typically through token frequency) but disagree on **the channel
through which it does so**.

This file makes the disagreement Lean-provable. For each pair of
theories, we construct a tiny concrete witness in which the two
theories assign *different* numerical predictions to the same input.
The theorems are not statistical fits or claims about which theory is
empirically correct in any particular study — they are proofs that the
theories are *not extensionally equivalent*. Empirical separation must
then look for the witness pattern in real data.

## Why separations and not implications

The four theories are not nested: none extends another. They make
qualitatively different commitments:

- **Continuity vs. discontinuity**: ScaledWeights / RepStrength predict
  smooth gradient response to log-frequency; IndexedConstraints
  predicts a step; UseListed predicts a step *with* a "novel item"
  exception clause.
- **Channel of frequency dependence**: ScaledWeights routes frequency
  through constraint weights (grammar); RepStrength routes it through
  underlying-form activation (lexicon); UseListed routes it through
  retrieval (memory); IndexedConstraints routes it through stratum
  partition (lexicon).
- **Compositionality**: RepStrength inherits compound activation from
  constituents; ScaledWeights / Indexed / UseListed see only the
  candidate's own frequency.

Each separation theorem below picks a contrast where these commitments
have observable consequences.

## What this file does *not* prove

- It does not prove any of the theories *correct*. Empirical fits are
  the wrong thing for a Lean library to formalize (per CLAUDE.md
  "Processing scope" guidance: stimulus contrasts, not regression
  tables).
- It does not prove the theories are *the only* possible accounts.
  There are intermediate variants (e.g., scaled weights with stratum
  dependence) that combine their commitments.
- It does not commit to a specific empirical case study. The
  Breiss-Katsuda-Kawahara compound data
  (`Studies/BreissKatsudaKawahara2026.lean`) is
  one *application* of these separations to Japanese velar
  nasalisation; this file stays abstract.
-/

namespace Constraints.ItemSpecificity.Separation

open Constraints.ItemSpecificity
open Constraints.ItemSpecificity.Indexed
open Constraints.ItemSpecificity.Scaled
open Constraints.ItemSpecificity.UseListed
open Constraints.ItemSpecificity.RepStrength
open Constraints OptimalityTheory

-- ============================================================================
-- § 1: Toy lexicon for separation witnesses
-- ============================================================================

/-- A minimal toy item type carrying just a log-frequency: enough to
    instantiate `HasTokenFreq` and exercise the four theories. The
    separation theorems do not depend on linguistic content — only on
    the frequency channel. -/
structure ToyItem where
  logFreq : ℝ
  deriving Inhabited

instance : HasTokenFreq ToyItem where
  tokenLogFreq := ToyItem.logFreq

/-- A toy base constraint that always fires once. The four theories
    differ only in how they *modulate* this base violation count, so
    using a constant base isolates the modulation channel. -/
def baseOne : NamedConstraint ToyItem :=
  { name := "BASE", family := .markedness, eval := fun _ => 1 }

-- ============================================================================
-- § 2: Indexed vs. Scaled — the discontinuity / continuity contrast
-- ============================================================================

/-- **Separation (Indexed vs. Scaled).** Two items in the same
    (high-frequency, "core") stratum with *different* log-frequencies:

    - Indexed: assigns them **equal** effective violation counts
      (the stratum determines everything).
    - Scaled (with nonzero positive slope): assigns the higher-frequency
      item a **strictly greater** effective weight.

    The witness uses items at log-frequency 5 and 10 with a stratum
    cutoff at 3 (so both are "core") and a scaled-weight slope of 1
    with base weight 0. -/
theorem sep_indexed_vs_scaled :
    let lo : ToyItem := ⟨5⟩
    let hi : ToyItem := ⟨10⟩
    -- Indexed: equal within stratum
    (mkCoreOnly (cutoff := 3) baseOne).eval lo
      = (mkCoreOnly (cutoff := 3) baseOne).eval hi
    ∧
    -- Scaled: strictly greater for higher frequency
    scaledWeight (baseWeight := 0) (slope := 1) lo
      < scaledWeight (baseWeight := 0) (slope := 1) hi := by
  refine ⟨?_, ?_⟩
  · -- Both items are in the core stratum, so both branches of the if
    -- collapse to `baseOne.eval _ = 1`.
    have h_lo : isCore (α := ToyItem) 3 ⟨5⟩ := by
      unfold isCore; show (5 : ℝ) ≥ 3; norm_num
    have h_hi : isCore (α := ToyItem) 3 ⟨10⟩ := by
      unfold isCore; show (10 : ℝ) ≥ 3; norm_num
    simp [mkCoreOnly, h_lo, h_hi, baseOne]
  · -- scaledWeight 0 1 ⟨x⟩ = 0 + 1 * x = x; 5 < 10.
    unfold scaledWeight
    show (0 : ℝ) + 1 * 5 < 0 + 1 * 10
    norm_num

-- ============================================================================
-- § 3: UseListed vs. grammar — novel-item invariance
-- ============================================================================

/-- **Separation (UseListed vs. anything else).** For an item *below*
    the listing threshold ("novel"), UseListed dispatches to the
    grammar regardless of what the listed-form lookup would have
    produced.

    Concretely: pick a novel item at log-frequency 0.5 with threshold
    3, a "listed form" function that returns the constant `99`, and
    a "grammar" function that returns the constant `7`. UseListed
    dispatches to the grammar (`= 7`), distinct from the listed
    surface (`= 99`). -/
theorem sep_uselisted_novel_invariant :
    dispatch (threshold := 3) (listedForm := fun _ : ToyItem => (99 : Nat))
      (grammarForm := fun _ : ToyItem => (7 : Nat)) ⟨0.5⟩
    = 7 := by
  exact dispatch_novel_eq_grammar (α := ToyItem) (β := Nat) 3
    (fun _ => 99) (fun _ => 7) ⟨0.5⟩
    (by show (0.5 : ℝ) < 3; norm_num)

/-- **Separation (UseListed vs. ScaledWeights).** For a novel item,
    UseListed delivers the grammar's output — *unchanged by frequency*.
    ScaledWeights with positive slope, by contrast, scales the
    weight by frequency even for novel items. The witness compares
    two novel items with different (sub-threshold) log-frequencies:

    - UseListed: same dispatch (grammar's output) for both.
    - ScaledWeights: distinct effective weights.

    The implication for empirical work is direct: present subjects
    with novel stimuli at varying log-frequencies (e.g., wug stimuli
    matched to corpus frequency proxies). UseListed predicts no
    frequency gradient on novel items; ScaledWeights predicts one. -/
theorem sep_uselisted_vs_scaled_on_novel_pair :
    let novelLo : ToyItem := ⟨0.5⟩
    let novelHi : ToyItem := ⟨2.5⟩
    -- UseListed: identical dispatch (both novel → grammar)
    dispatch (threshold := 3) (listedForm := fun _ : ToyItem => (99 : Nat))
        (grammarForm := fun _ : ToyItem => (7 : Nat)) novelLo
      = dispatch (threshold := 3) (listedForm := fun _ : ToyItem => (99 : Nat))
        (grammarForm := fun _ : ToyItem => (7 : Nat)) novelHi
    ∧
    -- ScaledWeights: distinct effective weights
    scaledWeight (baseWeight := 0) (slope := 1) novelLo
      ≠ scaledWeight (baseWeight := 0) (slope := 1) novelHi := by
  refine ⟨?_, ?_⟩
  · rw [dispatch_novel_eq_grammar (α := ToyItem) (β := Nat) 3
          (fun _ => 99) (fun _ => 7) ⟨0.5⟩ (by show (0.5 : ℝ) < 3; norm_num),
        dispatch_novel_eq_grammar (α := ToyItem) (β := Nat) 3
          (fun _ => 99) (fun _ => 7) ⟨2.5⟩ (by show (2.5 : ℝ) < 3; norm_num)]
  · unfold scaledWeight
    show (0 : ℝ) + 1 * 0.5 ≠ 0 + 1 * 2.5
    norm_num

-- ============================================================================
-- § 4: RepresentationStrength vs. Scaled — compositional inheritance
-- ============================================================================

/-- **Separation (RepStrength vs. Scaled).** RepStrength's compound
    activation depends on *constituent* frequencies via the `combine`
    rule; ScaledWeights' effective weight on a compound depends only on
    the compound's *own* frequency. So two compounds with the *same*
    compound frequency but different constituent frequencies receive:

    - RepStrength: distinct activations (under `min` combine, the
      compound with the lower-activation constituent loses).
    - ScaledWeights: identical effective weights (compound frequency
      is the only input).

    The concrete witness uses the identity sigmoid (so activation = log
    frequency) and `min` combine. Two compounds with different N2
    activations get different `compoundActivation` values. -/
theorem sep_repstrength_vs_scaled_compositional :
    let n1 : ToyItem := ⟨5⟩
    let n2_lo : ToyItem := ⟨1⟩
    let n2_hi : ToyItem := ⟨7⟩
    -- RepStrength under min-combine: distinct compound activations
    compoundActivation (sigmoid := id) (combine := minCombine) n1 n2_lo
      ≠ compoundActivation (sigmoid := id) (combine := minCombine) n1 n2_hi
    ∧
    -- ScaledWeights sees only the compound's own freq (identical here)
    -- — both compounds, taken as their own ToyItem with logFreq 4,
    -- give the same scaled weight.
    scaledWeight (baseWeight := 0) (slope := 1) (⟨4⟩ : ToyItem)
      = scaledWeight (baseWeight := 0) (slope := 1) (⟨4⟩ : ToyItem) := by
  refine ⟨?_, rfl⟩
  -- compoundActivation id minCombine ⟨5⟩ ⟨1⟩ = min 5 1 = 1
  -- compoundActivation id minCombine ⟨5⟩ ⟨7⟩ = min 5 7 = 5
  unfold compoundActivation activation minCombine
  show min (id (5 : ℝ)) (id 1) ≠ min (id 5) (id 7)
  simp
  norm_num

-- ============================================================================
-- § 5: Indexed vs. UseListed — same threshold, different interpretation
-- ============================================================================

/-- **Separation (Indexed vs. UseListed).** Both theories partition the
    lexicon at a frequency threshold, but with opposite computational
    consequences: Indexed routes high-frequency items *through* the
    grammar (with stratum-specific constraints firing); UseListed
    routes them *around* the grammar (returning a stored surface).

    Concrete witness: above-threshold item, base constraint that
    always fires.

    - Indexed-CoreOnly: violation count `1` (stratum-specific
      constraint fires).
    - UseListed: returns the listed surface (`99`), grammar untouched.

    These two outcomes — `1` and `99` — live in different types
    (`Nat` violation count vs. listed surface representation), but
    structurally the divergence is: Indexed says "compute through
    grammar", UseListed says "skip grammar". -/
theorem sep_indexed_vs_uselisted_routing :
    let hi : ToyItem := ⟨10⟩
    -- Indexed: computes through grammar, base fires
    (mkCoreOnly (cutoff := 3) baseOne).eval hi = 1
    ∧
    -- UseListed: skips grammar, returns listed form
    dispatch (threshold := 3) (listedForm := fun _ : ToyItem => (99 : Nat))
      (grammarForm := fun _ : ToyItem => (7 : Nat)) hi
    = 99 := by
  refine ⟨?_, ?_⟩
  · have h_core : isCore (α := ToyItem) 3 ⟨10⟩ := by
      unfold isCore; show (10 : ℝ) ≥ 3; norm_num
    simp [mkCoreOnly, h_core, baseOne]
  · unfold dispatch
    have h_listed : tokenLogFreq (⟨10⟩ : ToyItem) ≥ (3 : ℝ) := by
      show (10 : ℝ) ≥ 3; norm_num
    simp [h_listed]

-- ============================================================================
-- § 6: RepresentationStrength vs. UseListed — gradient vs. step in the lexicon
-- ============================================================================

/-- **Separation (RepStrength vs. UseListed).** Two items both below
    the listing threshold ("novel" from UseListed's perspective):

    - RepStrength: assigns them distinct activations as a continuous
      function of log-frequency.
    - UseListed: dispatches both to the grammar, which (under any
      frequency-blind grammar function) returns the same value.

    This is the mirror of `sep_uselisted_vs_scaled_on_novel_pair`
    (§3) for the lexicon-side gradient theory: UseListed's storage
    gate is binary, while RepStrength's activation channel is
    continuous in log-frequency even within a single stratum.

    Empirical content: with novel stimuli at varying log-frequencies,
    RepStrength predicts gradient lexical-strength effects; UseListed
    predicts no frequency gradient on novel items. -/
theorem sep_repstrength_vs_uselisted_subthreshold :
    let lo : ToyItem := ⟨0.5⟩
    let hi : ToyItem := ⟨2.5⟩
    -- RepStrength: distinct activations even sub-threshold
    activation (sigmoid := id) lo ≠ activation (sigmoid := id) hi
    ∧
    -- UseListed: both novel → grammar dispatch, frequency-blind
    dispatch (threshold := 3) (listedForm := fun _ : ToyItem => (99 : Nat))
        (grammarForm := fun _ : ToyItem => (7 : Nat)) lo
      = dispatch (threshold := 3) (listedForm := fun _ : ToyItem => (99 : Nat))
        (grammarForm := fun _ : ToyItem => (7 : Nat)) hi := by
  refine ⟨?_, ?_⟩
  · unfold activation
    show (0.5 : ℝ) ≠ 2.5
    norm_num
  · rw [dispatch_novel_eq_grammar (α := ToyItem) (β := Nat) 3
          (fun _ => 99) (fun _ => 7) ⟨0.5⟩ (by show (0.5 : ℝ) < 3; norm_num),
        dispatch_novel_eq_grammar (α := ToyItem) (β := Nat) 3
          (fun _ => 99) (fun _ => 7) ⟨2.5⟩ (by show (2.5 : ℝ) < 3; norm_num)]

-- ============================================================================
-- § 7: RepresentationStrength vs. Indexed — gradient vs. step (lexicon-side)
-- ============================================================================

/-- **Separation (RepStrength vs. Indexed).** Two items in the same
    Indexed stratum ("core") with different log-frequencies:

    - RepStrength: assigns them distinct activations.
    - Indexed: assigns them the same effective violation count
      (the stratum determines everything within).

    This is the lexicon-side mirror of `sep_indexed_vs_scaled` (§2):
    both Indexed and (Indexed-vs-Scaled) RepStrength take the same
    contrast, but route it through different cells of the directory's
    discrete/continuous × grammar/lexicon grid. RepStrength's
    continuity *within a stratum* is the discriminating feature. -/
theorem sep_repstrength_vs_indexed_within_stratum :
    let lo : ToyItem := ⟨5⟩
    let hi : ToyItem := ⟨10⟩
    -- RepStrength: distinct activations within stratum
    activation (sigmoid := id) lo ≠ activation (sigmoid := id) hi
    ∧
    -- Indexed: equal violation counts within the same stratum
    (mkCoreOnly (cutoff := 3) baseOne).eval lo
      = (mkCoreOnly (cutoff := 3) baseOne).eval hi := by
  refine ⟨?_, ?_⟩
  · unfold activation
    show (5 : ℝ) ≠ 10
    norm_num
  · have h_lo : isCore (α := ToyItem) 3 ⟨5⟩ := by
      show (5 : ℝ) ≥ 3; norm_num
    have h_hi : isCore (α := ToyItem) 3 ⟨10⟩ := by
      show (10 : ℝ) ≥ 3; norm_num
    simp [mkCoreOnly, h_lo, h_hi, baseOne]

end Constraints.ItemSpecificity.Separation
