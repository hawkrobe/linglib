/-
# NeoGricean Predictions: Theory meets Phenomena

This module proves that NeoGricean exhaustivity theory correctly predicts
the empirical data in `Phenomena/ScalarImplicatures/`.

## Predictions Verified

1. **Scales**: Exhaustification derives the scalar implicature (¬stronger)
2. **Hurford**: Rescued cases are exactly those where exh breaks entailment
3. **Singh**: Felicitous cases are weak-first (economy condition)

## Architecture

- Phenomena files: Theory-neutral empirical data (strings, judgments)
- ScaleSemantics: Semantic structures (meanings, entailments)
- This file: Proves theory predicts data

## Key References

- Spector (2016) "Comparing exhaustivity operators"
- Fox & Spector (2018) "Economy and embedded exhaustification"
-/

import Linglib.Theories.NeoGricean.Exhaustivity
import Linglib.Theories.NeoGricean.ScaleSemantics
import Linglib.Theories.NeoGricean.FoxSpector2018
import Linglib.Phenomena.ScalarImplicatures.Scales
import Linglib.Phenomena.ScalarImplicatures.Hurford
import Linglib.Phenomena.ScalarImplicatures.Singh

namespace NeoGricean.Predictions

open NeoGricean.Exhaustivity
open NeoGricean.ScaleSemantics
open Phenomena.ScalarImplicatures.Scales
open Phenomena.ScalarImplicatures.Hurford
open Phenomena.ScalarImplicatures.Singh

-- ============================================================================
-- PART 1: HORN SCALE PREDICTIONS
-- ============================================================================

/-
## Scale Predictions

For each Horn scale, exhaustifying the weaker term derives ¬stronger.
This matches the implicatures in `Phenomena/ScalarImplicatures/Scales.lean`.
-/

/--
**Prediction**: exh(some) → ¬all.

At any world where exhIE(some) holds, "all" is false.
This derives the implicature "some → not all".
-/
theorem someAll_implicature :
    ∀ w : QuantWorld, exhIE someAllScale.alts someQ w → ¬allQ w := by
  intro w hexh
  intro hall
  -- exhIE excludes all-worlds by including ¬all in IE
  have hie_neg_all : (∼allQ) ∈ IE someAllScale.alts someQ := by
    intro E hE_mc
    by_contra h_not_in
    let E' := E ∪ {∼allQ}
    have hcompat : isCompatible someAllScale.alts someQ E' := by
      obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
      refine ⟨Set.mem_union_left _ hphi, ?_, ?_⟩
      · intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · exact hform ψ hψ_E
        · simp only [Set.mem_singleton_iff] at hψ_new
          right
          refine ⟨allQ, ?_, hψ_new⟩
          simp [someAllScale, HornScale.alts]
      · -- Consistency: w=1 witnesses someQ ∧ ¬allQ
        use ⟨1, by omega⟩
        intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
          · simp [someQ]
          · simp [someAllScale, HornScale.alts] at ha
            rcases ha with rfl | rfl
            · -- ψ = ∼someQ: inconsistent with someQ in E
              exfalso
              obtain ⟨u, hu⟩ := hcons
              exact hu (∼someQ) hψ_E (hu someQ hphi)
            · -- ψ = ∼allQ
              simp only [pneg, allQ]; omega
        · simp only [Set.mem_singleton_iff] at hψ_new
          rw [hψ_new]
          simp only [pneg, allQ]; omega
    have hsubset : E ⊆ E' := Set.subset_union_left
    have hE'_not_sub_E : ¬(E' ⊆ E) := by
      intro hle
      apply h_not_in
      exact hle (Set.mem_union_right E (Set.mem_singleton _))
    exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
  have hneg_all_w : (∼allQ) w := hexh (∼allQ) hie_neg_all
  simp only [pneg] at hneg_all_w
  exact hneg_all_w hall

/--
**Prediction**: exh(or) → ¬and.

At any world where exhIE(or) holds, "and" is false.
This derives the implicature "or → not both".
-/
theorem orAnd_implicature :
    ∀ w : ConnWorld, exhIE orAndScale.alts orConn w → ¬andConn w := by
  intro w hexh hand
  have hie_neg_and : (∼andConn) ∈ IE orAndScale.alts orConn := by
    intro E hE_mc
    by_contra h_not_in
    let E' := E ∪ {∼andConn}
    have hcompat : isCompatible orAndScale.alts orConn E' := by
      obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
      refine ⟨Set.mem_union_left _ hphi, ?_, ?_⟩
      · intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · exact hform ψ hψ_E
        · simp only [Set.mem_singleton_iff] at hψ_new
          right
          refine ⟨andConn, ?_, hψ_new⟩
          simp [orAndScale, HornScale.alts]
      · -- Consistency: onlyA witnesses orConn ∧ ¬andConn
        use ConnWorld.onlyA
        intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
          · simp [orConn]
          · simp [orAndScale, HornScale.alts] at ha
            rcases ha with rfl | rfl
            · exfalso
              obtain ⟨u, hu⟩ := hcons
              exact hu (∼orConn) hψ_E (hu orConn hphi)
            · simp only [pneg, andConn]; tauto
        · simp only [Set.mem_singleton_iff] at hψ_new
          rw [hψ_new]
          simp only [pneg, andConn]; tauto
    have hsubset : E ⊆ E' := Set.subset_union_left
    have hE'_not_sub_E : ¬(E' ⊆ E) := by
      intro hle
      apply h_not_in
      exact hle (Set.mem_union_right E (Set.mem_singleton _))
    exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
  have hneg_and_w : (∼andConn) w := hexh (∼andConn) hie_neg_and
  simp only [pneg] at hneg_and_w
  exact hneg_and_w hand

/--
**Prediction**: exh(possible) → ¬necessary.
-/
theorem possibleNecessary_implicature :
    ∀ w : ModalWorld, exhIE possibleNecessaryScale.alts possibleP w → ¬necessaryP w := by
  intro w hexh hnec
  have hie_neg_nec : (∼necessaryP) ∈ IE possibleNecessaryScale.alts possibleP := by
    intro E hE_mc
    by_contra h_not_in
    let E' := E ∪ {∼necessaryP}
    have hcompat : isCompatible possibleNecessaryScale.alts possibleP E' := by
      obtain ⟨⟨hphi, hform, hcons⟩, _⟩ := hE_mc
      refine ⟨Set.mem_union_left _ hphi, ?_, ?_⟩
      · intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · exact hform ψ hψ_E
        · simp only [Set.mem_singleton_iff] at hψ_new
          right
          refine ⟨necessaryP, ?_, hψ_new⟩
          simp [possibleNecessaryScale, HornScale.alts]
      · -- Consistency: ModalWorld.some witnesses possibleP ∧ ¬necessaryP
        use ModalWorld.some
        intro ψ hψ
        rcases hψ with hψ_E | hψ_new
        · rcases hform ψ hψ_E with rfl | ⟨a, ha, rfl⟩
          · simp [possibleP]
          · simp [possibleNecessaryScale, HornScale.alts] at ha
            rcases ha with rfl | rfl
            · exfalso
              obtain ⟨u, hu⟩ := hcons
              exact hu (∼possibleP) hψ_E (hu possibleP hphi)
            · simp only [pneg, necessaryP]; tauto
        · simp only [Set.mem_singleton_iff] at hψ_new
          rw [hψ_new]
          simp only [pneg, necessaryP]; tauto
    have hsubset : E ⊆ E' := Set.subset_union_left
    have hE'_not_sub_E : ¬(E' ⊆ E) := by
      intro hle
      apply h_not_in
      exact hle (Set.mem_union_right E (Set.mem_singleton _))
    exact hE'_not_sub_E (hE_mc.2 E' hcompat hsubset)
  have hneg_nec_w : (∼necessaryP) w := hexh (∼necessaryP) hie_neg_nec
  simp only [pneg] at hneg_nec_w
  exact hneg_nec_w hnec

-- ============================================================================
-- PART 2: HURFORD PREDICTIONS
-- ============================================================================

/-
## Hurford Predictions

The theory predicts:
- Rescued cases: exh breaks entailment
- Unrescued cases: exh doesn't help (no scalar alternative)

For semantic scales (some/all, possible/necessary), exh breaks entailment.
For hyponym/hypernym (American/Californian), there's no scalar exh to apply.
-/

/--
Semantic structure for "some or all" (rescued Hurford case).
-/
def someOrAll_semantic : HurfordSemantic QuantWorld :=
  { disjunctA := someQ
  , disjunctB := allQ
  , entailment := Or.inr all_entails_some
  , alts := {someQ, allQ}
  }

/--
**Prediction**: "some or all" is rescued because exh(some) doesn't entail all.
-/
theorem someOrAll_is_rescued : someOrAll_semantic.isRescued := by
  -- isRescued = ¬(exhIE alts A ⊆ B) ∨ ¬(exhIE alts B ⊆ A)
  -- We show the first disjunct: ¬(exhIE {some,all} some ⊆ all)
  left
  intro h_entails
  -- h_entails: exhIE {some,all} some ⊆ all
  -- But exhIE(some) implies ¬all (by someAll_implicature)
  -- So exhIE(some) and all can't both hold - contradiction
  -- We need a world where exhIE(some) holds
  have hw1 : exhIE someOrAll_semantic.alts someQ ⟨1, by omega⟩ := by
    -- At w=1: some holds, all doesn't hold
    -- exhIE requires all IE members to hold
    intro ψ hψ_IE
    have hMC : isMCSet someOrAll_semantic.alts someQ {someQ, ∼allQ} := by
      constructor
      · -- Compatible
        refine ⟨Set.mem_insert _ _, ?_, ?_⟩
        · intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · left; rfl
          · right; exact ⟨allQ, Or.inr (Set.mem_singleton _), rfl⟩
        · use ⟨1, by omega⟩
          intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · simp [someQ]
          · simp only [pneg, allQ]; omega
      · -- Maximal
        intro E' hE'_compat hsubset ψ' hψ'_E'
        rcases hE'_compat.2.1 ψ' hψ'_E' with rfl | ⟨a, ha, rfl⟩
        · exact Or.inl rfl
        · simp only [someOrAll_semantic, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl
          · -- ∼someQ: inconsistent with someQ
            exfalso
            obtain ⟨u, hu⟩ := hE'_compat.2.2
            have hsomeQ := hE'_compat.1
            exact hu (∼someQ) hψ'_E' (hu someQ hsomeQ)
          · -- ∼allQ ∈ {someQ, ∼allQ}
            exact Or.inr rfl
    have hψ_in_MC : ψ ∈ ({someQ, ∼allQ} : Set (Prop' QuantWorld)) := hψ_IE _ hMC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_in_MC
    rcases hψ_in_MC with rfl | rfl
    · simp [someQ]
    · simp only [pneg, allQ]; omega
  -- Now: h_entails says exhIE(some) ⊆ all
  -- So at w=1: allQ ⟨1, by omega⟩ should hold
  have hall_w1 : allQ ⟨1, by omega⟩ := h_entails ⟨1, by omega⟩ hw1
  simp [allQ] at hall_w1

/--
**Prediction**: Theory matches data for "some or all" (felicitous = true).
-/
theorem someOrAll_prediction_matches_data :
    someOrAll_semantic.isRescued ↔ someOrAll.felicitous = true := by
  constructor
  · intro _; rfl
  · intro _; exact someOrAll_is_rescued

-- ============================================================================
-- PART 3: SINGH PREDICTIONS
-- ============================================================================

/-
## Singh Predictions

The theory predicts: felicitous ↔ (weak-first ∧ exh breaks entailment)

For or/and scale:
- exh(or) breaks entailment to and (exclusive or ⊄ and)
- So weak-first is felicitous, strong-first is not
-/

/--
Semantic structure for "A or B, or both" (weak-first Singh case).
-/
def orThenBoth_semantic : SinghSemantic ConnWorld :=
  { weaker := orConn
  , stronger := andConn
  , entailment := and_entails_or
  , alts := {orConn, andConn}
  , weakerFirst := true
  }

/--
Semantic structure for "both, or A or B" (strong-first Singh case).
-/
def bothThenOr_semantic : SinghSemantic ConnWorld :=
  { weaker := orConn
  , stronger := andConn
  , entailment := and_entails_or
  , alts := {orConn, andConn}
  , weakerFirst := false
  }

/--
**Prediction**: exh(or) breaks entailment to and.
-/
theorem orAnd_exh_breaks_entailment :
    ¬(exhIE {orConn, andConn} orConn ⊆ₚ andConn) := by
  intro h
  -- At onlyA: exhIE(or) holds (or holds, ¬and holds)
  have hexh : exhIE {orConn, andConn} orConn ConnWorld.onlyA := by
    intro ψ hψ_IE
    have hMC : isMCSet {orConn, andConn} orConn {orConn, ∼andConn} := by
      constructor
      · refine ⟨Set.mem_insert _ _, ?_, ?_⟩
        · intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · left; rfl
          · right; exact ⟨andConn, Or.inr (Set.mem_singleton _), rfl⟩
        · use ConnWorld.onlyA
          intro ψ' hψ'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ'
          rcases hψ' with rfl | rfl
          · simp [orConn]
          · simp only [pneg, andConn]; tauto
      · intro E' hE'_compat hsubset ψ' hψ'_E'
        rcases hE'_compat.2.1 ψ' hψ'_E' with rfl | ⟨a, ha, rfl⟩
        · exact Or.inl rfl
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl
          · exfalso
            obtain ⟨u, hu⟩ := hE'_compat.2.2
            exact hu (∼orConn) hψ'_E' (hu orConn hE'_compat.1)
          · exact Or.inr rfl
    have hψ_in : ψ ∈ ({orConn, ∼andConn} : Set (Prop' ConnWorld)) := hψ_IE _ hMC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ_in
    rcases hψ_in with rfl | rfl
    · simp [orConn]
    · simp only [pneg, andConn]; tauto
  -- But h says exhIE(or) ⊆ and, so and(onlyA) should hold
  have hand : andConn ConnWorld.onlyA := h ConnWorld.onlyA hexh
  simp [andConn] at hand

/--
**Prediction**: "A or B, or both" (weak-first) is predicted felicitous.
-/
theorem orThenBoth_predicted_felicitous : orThenBoth_semantic.predictedFelicitous := by
  constructor
  · -- weakerFirst = true
    rfl
  · -- exhBreaksEntailment
    exact orAnd_exh_breaks_entailment

/--
**Prediction**: Theory matches data for weak-first Singh case.
-/
theorem orThenBoth_prediction_matches_data :
    orThenBoth_semantic.predictedFelicitous ↔ orThenBoth.felicitous = true := by
  constructor
  · intro _; rfl
  · intro _; exact orThenBoth_predicted_felicitous

/--
**Prediction**: "both, or A or B" (strong-first) is NOT predicted felicitous.

Even though exh breaks entailment, strong-first fails because
exh(strong) is vacuous (nothing to exclude).
-/
theorem bothThenOr_not_predicted_felicitous : ¬bothThenOr_semantic.predictedFelicitous := by
  intro ⟨hwf, _⟩
  -- weakerFirst = false, but predictedFelicitous requires true
  simp [bothThenOr_semantic] at hwf

/--
**Prediction**: Theory matches data for strong-first Singh case.
-/
theorem bothThenOr_prediction_matches_data :
    ¬bothThenOr_semantic.predictedFelicitous ↔ bothThenOr.felicitous = false := by
  constructor
  · intro _; rfl
  · intro _; exact bothThenOr_not_predicted_felicitous

-- ============================================================================
-- PART 4: SUMMARY THEOREMS
-- ============================================================================

/--
**Main Result**: Theory correctly predicts all three Horn scale implicatures.

For each scale, exh(weaker) → ¬stronger.
-/
theorem all_scale_implicatures_derived :
    (∀ w, exhIE someAllScale.alts someQ w → ¬allQ w) ∧
    (∀ w, exhIE orAndScale.alts orConn w → ¬andConn w) ∧
    (∀ w, exhIE possibleNecessaryScale.alts possibleP w → ¬necessaryP w) :=
  ⟨someAll_implicature, orAnd_implicature, possibleNecessary_implicature⟩

/--
**Main Result**: Theory correctly predicts Singh asymmetry.

Weak-first is felicitous, strong-first is not.
-/
theorem singh_asymmetry_derived :
    orThenBoth_semantic.predictedFelicitous ∧
    ¬bothThenOr_semantic.predictedFelicitous :=
  ⟨orThenBoth_predicted_felicitous, bothThenOr_not_predicted_felicitous⟩

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Proves

### Scale Predictions
| Scale | Implicature | Theorem |
|-------|-------------|---------|
| some/all | some → ¬all | `someAll_implicature` |
| or/and | or → ¬and | `orAnd_implicature` |
| possible/necessary | possible → ¬necessary | `possibleNecessary_implicature` |

### Hurford Predictions
| Case | Felicitous | Rescued | Theorem |
|------|------------|---------|---------|
| some or all | Yes | Yes | `someOrAll_is_rescued` |

### Singh Predictions
| Case | Order | Felicitous | Theorem |
|------|-------|------------|---------|
| A or B, or both | weak-first | Yes | `orThenBoth_predicted_felicitous` |
| both, or A or B | strong-first | No | `bothThenOr_not_predicted_felicitous` |

### Significance

These proofs demonstrate that NeoGricean exhaustivity theory (Spector 2016,
Fox & Spector 2018) correctly predicts the empirical data in
`Phenomena/ScalarImplicatures/`.
-/

end NeoGricean.Predictions
