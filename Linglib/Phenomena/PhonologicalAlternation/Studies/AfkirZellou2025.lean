import Linglib.Theories.Phonology.HarmonicGrammar.Variation
import Linglib.Theories.Phonology.Constraints
import Linglib.Theories.Phonology.Syllable.NaturalClass
import Linglib.Fragments.Tarifit.Inventory

/-!
# Afkir & Zellou (2025): The Phonetics of Tarifit
@cite{afkir-zellou-2025}

*The Phonetics of Tarifit: Variation and Change in a Moroccan Amazigh
Language.* Cambridge Elements in Phonetics.

## Key empirical findings

1. **Two independent schwa processes**: prosodic template schwa (C2əC3,
   morphological) vs intrusive schwa (C1ǎC2, articulatory). They differ
   in phonetic quality, duration, and conditioning environment.

2. **Sonority-conditioned variation**: the C1–C2 sonority profile
   determines whether intrusive schwa is likely:
   - **Rising** sonority (C1 < C2): intrusive schwa is almost exclusively
     present (>90% of productions for words with /r/ as C2)
   - **Falling/plateauing** (C1 ≥ C2): intrusive schwa is never or rarely
     present

3. **Gradient vowelless production**: ~5% of tokens surface without any
   schwa (CCC). This is more accessible for words with low C2/C3
   sonority (voiceless obstruents).

4. **Sonority granularity matters**: the 8-level Parker scale — splitting
   obstruents by voicing — correctly predicts the gradient pattern, while
   the coarser 6-level Clements scale collapses critical contrasts.

5. **Perception**: intrusive schwa boosts auditory discrimination of
   minimal pairs only for falling-sonority clusters (§5.3.1, Figure 28),
   consistent with *SONO-PEAK: intrusive schwa in falling onsets creates
   a new sonority peak that alters perceived syllable structure.

## Formal reconstruction

**Note**: the paper uses mixed effects logistic regression for its
statistical analyses, not OT or Harmonic Grammar. The MaxEnt model
below is our own formal reconstruction of the paper's empirical
generalizations, designed to make the sonority-conditioned predictions
verifiable via `native_decide`. The five constraints and their weights
are chosen to capture the paper's main findings about rising/falling/
plateauing onset clusters and gradient vowelless accessibility.

**Limitation**: the model correctly predicts whether faithful or intrusive
wins for each sonority profile, and correctly ranks words by *relative*
vowelless accessibility. However, it overpenalizes vowelless for words
with high-sonority C3 (e.g. /ħkəm/, /sχəf/), predicting intrusive >
vowelless when empirically vowelless > intrusive for those items. The
paper notes these as partly idiosyncratic (Table 7).
-/

namespace Phenomena.PhonologicalAlternation.Studies.AfkirZellou2025

open Theories.Phonology.HarmonicGrammar Theories.Phonology.Constraints
open Theories.Phonology.Syllable
open Fragments.Tarifit.Inventory
open Core.OT

-- ============================================================================
-- § 1: Surface Forms and Candidates
-- ============================================================================

/-- The three possible surface realizations of a CCəC word. -/
inductive SurfaceForm where
  /-- CCəC: template schwa preserved, no intrusive schwa. -/
  | faithful
  /-- CǎCəC: intrusive schwa inserted between C1 and C2. -/
  | intrusive
  /-- CCC: vowelless — no schwa at all. -/
  | vowelless
  deriving DecidableEq, BEq, Repr

/-- A candidate pairs a word's consonant profile with a surface form. -/
structure TarifitCandidate where
  c1 : NatClass
  c2 : NatClass
  c3 : NatClass
  surface : SurfaceForm
  deriving DecidableEq, BEq, Repr

/-- Build a candidate from a word and surface form. -/
def mkCandidate (w : TriconWord) (sf : SurfaceForm) : TarifitCandidate :=
  { c1 := w.c1, c2 := w.c2, c3 := w.c3, surface := sf }

-- ============================================================================
-- § 2: MaxEnt Constraints
-- ============================================================================

/-- MAX-V (faithfulness): penalizes deletion of template schwa.
    Violated once by vowelless production. -/
def maxV : WeightedConstraint TarifitCandidate :=
  mkMaxW "MAX-V" (fun c => c.surface == .vowelless) 3

/-- *SONO-CC (markedness): penalizes vowelless clusters proportional to
    consonant sonority. Higher-sonority consonants in a bare CC cluster
    are more marked because they expect a vocalic nucleus.
    Violation count = c2.parkerSonority + c3.parkerSonority.
    Models the regression finding that lower C2/C3 sonority predicts
    more vowelless production (@cite{afkir-zellou-2025} Figure 19). -/
def sonoCC : WeightedConstraint TarifitCandidate :=
  mkMarkGradW "*SONO-CC" (fun c => match c.surface with
    | .vowelless => c.c2.parkerSonority + c.c3.parkerSonority
    | _ => 0) 1

/-- DEP-V (faithfulness): penalizes insertion of intrusive schwa.
    Violated once by intrusive production. -/
def depV : WeightedConstraint TarifitCandidate :=
  mkDepW "DEP-V" (fun c => c.surface == .intrusive) 2

/-- *SONO-PEAK (markedness): penalizes intrusive schwa in falling-sonority
    environments. The penalty is proportional to the sonority drop
    (c1.son - c2.son), modeling the articulatory implausibility of a
    vocalic gesture between a more-sonorous C1 and less-sonorous C2.
    Zero violations for rising or plateauing onsets (Nat subtraction).
    Captures the regression finding (est. = 0.8, p < 0.001) that
    rising sonority predicts C1ǎC2 presence (@cite{afkir-zellou-2025}
    Figure 21). -/
def sonoPeak : WeightedConstraint TarifitCandidate :=
  mkMarkGradW "*SONO-PEAK" (fun c => match c.surface with
    | .intrusive => c.c1.parkerSonority - c.c2.parkerSonority
    | _ => 0) 2

/-- *COMPLEX-ONSET (markedness): penalizes complex onsets with rising
    sonority in the faithful parse. The penalty is proportional to the
    sonority rise (c2.son - c1.son), modeling the pressure to break up
    clusters where C2 is much more sonorous than C1.
    Zero violations for falling or plateauing onsets (Nat subtraction). -/
def complexOnset : WeightedConstraint TarifitCandidate :=
  mkMarkGradW "*COMPLEX-ONSET" (fun c => match c.surface with
    | .faithful => c.c2.parkerSonority - c.c1.parkerSonority
    | _ => 0) 1

/-- The MaxEnt constraint set for Tarifit schwa variation. -/
def tarifitConstraints : List (WeightedConstraint TarifitCandidate) :=
  [maxV, sonoCC, depV, sonoPeak, complexOnset]

-- ============================================================================
-- § 3: Rising Onset — Intrusive Schwa Preferred
-- ============================================================================

/-- /qrəβ/ (VLS–liquid, rise=5): intrusive > faithful > vowelless.
    Table 9 "almost exclusively" C1ǎC2 (@cite{afkir-zellou-2025}). -/
theorem qreb_intrusive_gt_faithful :
    moreProbable tarifitConstraints
      (mkCandidate w_qreb .intrusive) (mkCandidate w_qreb .faithful) := by
  native_decide

theorem qreb_faithful_gt_vowelless :
    moreProbable tarifitConstraints
      (mkCandidate w_qreb .faithful) (mkCandidate w_qreb .vowelless) := by
  native_decide

/-- /qməʕ/ (VLS–nasal, rise=4): intrusive > faithful.
    Table 9 "variably" C1ǎC2 (@cite{afkir-zellou-2025}). -/
theorem qmes_intrusive_gt_faithful :
    moreProbable tarifitConstraints
      (mkCandidate w_qmes .intrusive) (mkCandidate w_qmes .faithful) := by
  native_decide

/-- /srəm/ (VLF–liquid, rise=3): intrusive > faithful.
    Table 9 "almost exclusively" C1ǎC2 (@cite{afkir-zellou-2025}). -/
theorem srem_intrusive_gt_faithful :
    moreProbable tarifitConstraints
      (mkCandidate w_srem .intrusive) (mkCandidate w_srem .faithful) := by
  native_decide

-- ============================================================================
-- § 4: Falling Onset — Faithful Preferred, Intrusive Disfavored
-- ============================================================================

/-- /ntəf/ (nasal–VLS, fall=4): faithful > vowelless > intrusive.
    Table 9 "never" C1ǎC2, Table 7 "often vowelless"
    (@cite{afkir-zellou-2025}). -/
theorem ntef_faithful_gt_vowelless :
    moreProbable tarifitConstraints
      (mkCandidate w_ntef .faithful) (mkCandidate w_ntef .vowelless) := by
  native_decide

theorem ntef_vowelless_gt_intrusive :
    moreProbable tarifitConstraints
      (mkCandidate w_ntef .vowelless) (mkCandidate w_ntef .intrusive) := by
  native_decide

/-- /nqəβ/ (nasal–VLS, fall=4): faithful > vowelless.
    Table 9 "variably" C1ǎC2 — one of the few exceptions to the
    falling=never pattern (@cite{afkir-zellou-2025} Table 9 note). -/
theorem nqeb_faithful_gt_vowelless :
    moreProbable tarifitConstraints
      (mkCandidate w_nqeb .faithful) (mkCandidate w_nqeb .vowelless) := by
  native_decide

/-- /ħkəm/ (VLF–VLS, fall=2): faithful > intrusive > vowelless (model).
    Table 9 "never" C1ǎC2; Table 7 "often vowelless" (13–20%)
    (@cite{afkir-zellou-2025}). The model correctly predicts faithful
    as winner but overpenalizes vowelless via *SONO-CC (C3=nasal, son=5);
    empirically vowelless > intrusive, noted as idiosyncratic in Table 7. -/
theorem hkem_faithful_gt_intrusive :
    moreProbable tarifitConstraints
      (mkCandidate w_hkem .faithful) (mkCandidate w_hkem .intrusive) := by
  native_decide

theorem hkem_faithful_gt_vowelless :
    moreProbable tarifitConstraints
      (mkCandidate w_hkem .faithful) (mkCandidate w_hkem .vowelless) := by
  native_decide

-- ============================================================================
-- § 5: Plateauing Onset — Faithful Preferred
-- ============================================================================

/-- /sχəf/ (VLF–VLF, plateau): faithful > intrusive > vowelless (model).
    Table 9 "never" C1ǎC2; Table 7 "often vowelless" (13–20%)
    (@cite{afkir-zellou-2025}). Like /ħkəm/, the model correctly blocks
    intrusive but overpenalizes vowelless; empirically this is one of the
    most frequently vowelless words. -/
theorem skhef_faithful_gt_intrusive :
    moreProbable tarifitConstraints
      (mkCandidate w_skhef .faithful) (mkCandidate w_skhef .intrusive) := by
  native_decide

theorem skhef_faithful_gt_vowelless :
    moreProbable tarifitConstraints
      (mkCandidate w_skhef .faithful) (mkCandidate w_skhef .vowelless) := by
  native_decide

/-- /sfən/ (VLF–VLF, plateau): faithful > intrusive > vowelless.
    Table 9 "never" C1ǎC2 (@cite{afkir-zellou-2025}).
    Unlike /sχəf/, /sfən/ is not listed as frequently vowelless. -/
theorem sfen_faithful_gt_intrusive :
    moreProbable tarifitConstraints
      (mkCandidate w_sfen .faithful) (mkCandidate w_sfen .intrusive) := by
  native_decide

theorem sfen_faithful_gt_vowelless :
    moreProbable tarifitConstraints
      (mkCandidate w_sfen .faithful) (mkCandidate w_sfen .vowelless) := by
  native_decide

-- ============================================================================
-- § 6: Gradient Vowelless Accessibility
-- ============================================================================

/-- Low-sonority clusters make vowelless production more accessible:
    /ntəf/ (C2=VLS, C3=VLF) has higher vowelless harmony than
    /qrəβ/ (C2=liquid, C3=VDF), because *SONO-CC penalizes
    high-sonority clusters more heavily.
    Captures the regression result (C2 est. = -0.7, C3 est. = -1.4)
    that lower C2/C3 sonority predicts more vowelless production
    (@cite{afkir-zellou-2025} Figure 19). -/
theorem vowelless_more_accessible_low_sonority :
    moreProbable tarifitConstraints
      (mkCandidate w_ntef .vowelless) (mkCandidate w_qreb .vowelless) := by
  native_decide

/-- Among vowelless candidates, all-obstruent clusters have the highest
    harmony (least penalized). Consistent with Table 7: /sχəf/ and /skəf/
    are the most frequently vowelless words (@cite{afkir-zellou-2025}). -/
theorem vowelless_obstruent_gt_sonorant :
    moreProbable tarifitConstraints
      (mkCandidate w_skhef .vowelless) (mkCandidate w_srem .vowelless) := by
  native_decide

/-- /sχəf/ (all VLF) has higher vowelless harmony than /sfən/ (VLF–VLF–N),
    because C3=nasal(5) is more sonorous than C3=VLF(3). -/
theorem vowelless_all_obstruent_gt_mixed :
    moreProbable tarifitConstraints
      (mkCandidate w_skhef .vowelless) (mkCandidate w_sfen .vowelless) := by
  native_decide

-- ============================================================================
-- § 7: Structural Properties
-- ============================================================================

/-- Falling/plateauing onset: faithful incurs zero constraint violations.
    *COMPLEX-ONSET only penalizes rising sonority (c2.son - c1.son = 0
    for falling/plateauing), and faithful violates no faithfulness
    constraint. -/
theorem falling_faithful_zero :
    harmonyScore tarifitConstraints (mkCandidate w_ntef .faithful) = 0 := by
  native_decide

theorem plateauing_faithful_zero :
    harmonyScore tarifitConstraints (mkCandidate w_skhef .faithful) = 0 := by
  native_decide

/-- Rising onset intrusive: harmony = -2 (only DEP-V violation).
    *SONO-PEAK contributes 0 for rising onsets (Nat subtraction). -/
theorem rising_intrusive_base_cost :
    harmonyScore tarifitConstraints (mkCandidate w_qreb .intrusive) = -2 := by
  native_decide

/-- Falling onset intrusive: additional *SONO-PEAK penalty.
    /ntəf/ intrusive: DEP-V (-2) + *SONO-PEAK 4 × (-2) = -10. -/
theorem falling_intrusive_penalized :
    harmonyScore tarifitConstraints (mkCandidate w_ntef .intrusive) = -10 := by
  native_decide

/-- Rising onset faithful: *COMPLEX-ONSET penalty proportional to rise.
    /qrəβ/ faithful: *COMPLEX-ONSET (6-1=5) × (-1) = -5. -/
theorem rising_faithful_penalized :
    harmonyScore tarifitConstraints (mkCandidate w_qreb .faithful) = -5 := by
  native_decide

-- ============================================================================
-- § 8: Constraint Independence — Two Schwa Processes
-- ============================================================================

-- The paper's central theoretical claim (§4.2.8) is that prosodic
-- template schwa (C2əC3) and intrusive schwa (C1ǎC2) are independent
-- processes: C1ǎC2 presence does not predict C2əC3 presence or duration
-- (logistic regression p = 0.1; linear regression p = 0.8). Our
-- constraint system structurally mirrors this: intrusive and vowelless
-- candidates violate completely disjoint constraint subsets.

/-- Intrusive candidates never violate MAX-V, *SONO-CC, or *COMPLEX-ONSET.
    Their harmony depends only on DEP-V and *SONO-PEAK. -/
theorem intrusive_disjoint (c : TarifitCandidate) (h : c.surface = .intrusive) :
    maxV.eval c = 0 ∧ sonoCC.eval c = 0 ∧ complexOnset.eval c = 0 := by
  rcases c with ⟨c1, c2, c3, sf⟩; subst h; exact ⟨rfl, rfl, rfl⟩

/-- Vowelless candidates never violate DEP-V, *SONO-PEAK, or *COMPLEX-ONSET.
    Their harmony depends only on MAX-V and *SONO-CC. -/
theorem vowelless_disjoint (c : TarifitCandidate) (h : c.surface = .vowelless) :
    depV.eval c = 0 ∧ sonoPeak.eval c = 0 ∧ complexOnset.eval c = 0 := by
  rcases c with ⟨c1, c2, c3, sf⟩; subst h; exact ⟨rfl, rfl, rfl⟩

/-- Faithful candidates never violate MAX-V, DEP-V, *SONO-CC, or *SONO-PEAK.
    Their harmony depends only on *COMPLEX-ONSET. -/
theorem faithful_disjoint (c : TarifitCandidate) (h : c.surface = .faithful) :
    maxV.eval c = 0 ∧ depV.eval c = 0 ∧ sonoCC.eval c = 0 ∧
    sonoPeak.eval c = 0 := by
  rcases c with ⟨c1, c2, c3, sf⟩; subst h; exact ⟨rfl, rfl, rfl, rfl⟩

end Phenomena.PhonologicalAlternation.Studies.AfkirZellou2025
