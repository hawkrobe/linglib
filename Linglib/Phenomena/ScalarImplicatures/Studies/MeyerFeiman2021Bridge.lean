import Linglib.Phenomena.ScalarImplicatures.Studies.MeyerFeiman2021
import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Phenomena.Modality.FreeChoice

/-!
# Meyer & Feiman (2021) — Bridge Theorems

Connects the process profile classification to the observed priming data
and to the broader scalar implicature and free choice phenomena in linglib.

## Structure

1. **Per-experiment verification**: each experiment's result matches the
   profile-based prediction
2. **Cross-category theorems**: shared vs different ALT-NEG correctly
   predicts priming pattern
3. **Connections to existing data**: Horn scale classification, Hurford
   rescue, FC phenomena
-/

namespace Phenomena.ScalarImplicatures.Studies.MeyerFeiman2021


/-! ## Section 1: Process Profile Consistency -/

/-- Quantifiers and numerals share ALT-NEG (both use exhaustification). -/
theorem quantifier_numeral_shared_altNeg :
    sharesAltNeg .quantifier .numeral = true := rfl

/-- Quantifiers and numerals differ on ALT-GEN. -/
theorem quantifier_numeral_different_altGen :
    sharesAltGen .quantifier .numeral = false := rfl

/-- FC uses a different ALT-NEG mechanism from quantifiers. -/
theorem fc_quantifier_different_altNeg :
    sharesAltNeg .freeChoiceDisjunction .quantifier = false := rfl

/-- FC uses a different ALT-NEG mechanism from numerals. -/
theorem fc_numeral_different_altNeg :
    sharesAltNeg .freeChoiceDisjunction .numeral = false := rfl

/-- *some* and *three* share exhaustification. -/
theorem some_three_same_altNeg :
    (itemProfile .some_).altNeg = (itemProfile .three).altNeg := rfl

/-- *some* and *three* differ on ALT-GEN source. -/
theorem some_three_different_altGen :
    (itemProfile .some_).altGen ≠ (itemProfile .three).altGen := by decide

/-- FC *or* uses a completely different mechanism from *some*. -/
theorem fcOr_some_different_mechanism :
    (itemProfile .fcOr).altNeg ≠ (itemProfile .some_).altNeg := by decide


/-! ## Section 2: Per-Experiment Verification

Each experiment's observed priming result matches the profile prediction. -/

/-- Exp 1–2: priming predicted (shared ALT-NEG) and observed. -/
theorem exp1_2_matches_prediction :
    exp1_2.primingObserved = predictsPriming exp1_2.primeClass exp1_2.targetClass := rfl

/-- Exp 3–4: priming predicted (shared ALT-NEG) and observed. -/
theorem exp3_4_matches_prediction :
    exp3_4.primingObserved = predictsPriming exp3_4.primeClass exp3_4.targetClass := rfl

/-- Exp 5: no priming predicted (different ALT-NEG) and none observed. -/
theorem exp5_matches_prediction :
    exp5.primingObserved = predictsPriming exp5.primeClass exp5.targetClass := rfl

/-- Exp 6: no priming predicted (different ALT-NEG) and none observed. -/
theorem exp6_matches_prediction :
    exp6.primingObserved = predictsPriming exp6.primeClass exp6.targetClass := rfl

/-- All experiments match the profile-based prediction. -/
theorem all_experiments_match :
    allExperiments.all (λ e => e.primingObserved == predictsPriming e.primeClass e.targetClass)
    = true := by native_decide


/-! ## Section 3: Falsification Theorems -/

/-- The decomposed account is compatible with the data. -/
theorem decomposed_compatible : compatibleWithData .decomposed = true := rfl

/-- The uniform-online account is falsified. -/
theorem uniform_online_falsified : compatibleWithData .uniformOnline = false := rfl

/-- The uniform-offline account is falsified. -/
theorem uniform_offline_falsified : compatibleWithData .uniformOffline = false := rfl

/-- The fully-independent account is falsified. -/
theorem fully_independent_falsified : compatibleWithData .fullyIndependent = false := rfl

/-- Exactly one of the four positions survives the data. -/
theorem exactly_one_survives :
    [TheoreticalPosition.uniformOnline, .uniformOffline, .decomposed, .fullyIndependent].filter
      compatibleWithData = [.decomposed] := by native_decide


/-! ## Section 4: Connections to Basic SI Data

The process profile classification aligns with Horn scale properties. -/

/-- The quantifier scale ⟨some, all⟩ has an online ALT-GEN profile. -/
theorem quantifier_scale_online :
    (scaleProfile Phenomena.ScalarImplicatures.quantifierScale).altGen = .online := rfl

/-- The numeral scale ⟨1, 2, 3, ...⟩ has an offline ALT-GEN profile. -/
theorem numeral_scale_offline :
    (scaleProfile Phenomena.ScalarImplicatures.numeralScale).altGen = .offline := rfl

/-- Both quantifier and numeral scales share ALT-NEG = exhaustification. -/
theorem both_scales_exhaust :
    (scaleProfile Phenomena.ScalarImplicatures.quantifierScale).altNeg =
    (scaleProfile Phenomena.ScalarImplicatures.numeralScale).altNeg := rfl

/-- The connective scale ⟨or, and⟩ (standard, non-FC) also uses exhaustification.
    This is important: standard exclusive-or implicature ("A or B → not both")
    is a *different* use of "or" from free choice ("You may A or B → may A ∧ may B").
    Same lexical item, different processing architecture depending on modal embedding. -/
theorem connective_scale_exhaust :
    (scaleProfile Phenomena.ScalarImplicatures.connectiveScale).altNeg = .exhaustification := rfl


/-! ## Section 5: Connections to Hurford Rescue

Hurford rescue requires exhaustification to be available. The offline
ALT-GEN of numerals means exhaustification of "three" to "exactly three"
is immediately available — the alternatives {1,2,4,5,...} are pre-stored.

For quantifiers (online ALT-GEN), alternatives must be computed first,
then exhaustified. Both paths end in the same ALT-NEG, but the speed
of alternative availability differs. -/

/-- Numeral Hurford rescue: "three or all" is rescued because
    exh(three) = "exactly three" is available via offline alternatives. -/
theorem hurford_numeral_rescue_available :
    hurfordNumeralProfile.altGen = .offline := rfl

/-- Both rescued-numeral and rescued-quantifier Hurford cases use
    the same strengthening mechanism (exhaustification). -/
theorem hurford_same_neg_mechanism :
    hurfordNumeralProfile.altNeg =
    (scaleProfile Phenomena.ScalarImplicatures.quantifierScale).altNeg := rfl


/-! ## Section 6: Connections to Free Choice Phenomena

The FC process profile connects to the FC data in
`Phenomena.Modality.FreeChoice`. -/

/-- FC uses innocent inclusion, not exhaustification. -/
theorem fc_uses_inclusion : freeChoiceProfile.altNeg = .innocentInclusion := rfl

/-- The SI/FC contrast is a processing architecture difference. -/
theorem si_fc_different_mechanisms : siVsFc.sameMechanism = false := rfl

/-- FC data items are correctly classified as having a distinct mechanism
    from standard SI data items. -/
theorem fc_data_distinct_from_si :
    (classProfile .freeChoiceDisjunction).altNeg ≠
    (classProfile .quantifier).altNeg := by decide

/-- FC cancellability (from FreeChoice.lean) is consistent with the FC
    profile using innocentInclusion: pragmatic mechanisms are cancellable.
    Both exhaustification-based SI and II-based FC are pragmatic, but they
    are different *kinds* of pragmatic computation. -/
theorem fc_cancellable_consistent :
    Phenomena.Modality.FreeChoice.explicitCancellation.felicitous = true := rfl


/-! ## Section 7: The Spectrum as a Whole

The three-way classification reveals that "scalar inference" is not a
natural kind — it is a family of phenomena sharing some but not all
sub-computations. -/

/-- All three classes share the property of being scalar (involving
    alternatives), but differ in processing architecture. -/
theorem all_involve_alternatives :
    [ScalarItemClass.quantifier, .numeral, .freeChoiceDisjunction].all
      (fun c => (classProfile c).altNeg != .none) = true := by native_decide

/-- No two of the three classes have identical process profiles. -/
theorem all_profiles_distinct :
    classProfile .quantifier ≠ classProfile .numeral ∧
    classProfile .quantifier ≠ classProfile .freeChoiceDisjunction ∧
    classProfile .numeral ≠ classProfile .freeChoiceDisjunction := by
  exact ⟨by decide, by decide, by decide⟩


end Phenomena.ScalarImplicatures.Studies.MeyerFeiman2021
