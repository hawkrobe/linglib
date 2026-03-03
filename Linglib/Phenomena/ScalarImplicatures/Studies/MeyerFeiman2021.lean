import Linglib.Phenomena.ScalarImplicatures.Basic
import Linglib.Phenomena.Modality.FreeChoice

/-!
# @cite{meyer-feiman-2021} — Composing Alternatives
@cite{bar-lev-fox-2017} @cite{chierchia-2004} @cite{fox-2007}

Structural priming evidence that scalar and free choice implicatures
decompose into independently parameterizable sub-computations.

## Citation

Meyer, M.-C. & Feiman, R. (2021). Composing alternatives: The structural
source of scalar and free choice implicatures. *Journal of Memory and
Language*, 121, 104279.

## Core Contribution

Implicature computation factors into two sub-operations:

1. **ALT-GEN** (alternative generation): Computing what the speaker
   *could have said*
2. **ALT-NEG** (alternative negation): Strengthening by negating the
   un-uttered alternatives

Each sub-operation can independently be **online** (computed during
processing) or **offline** (pre-stored with the lexical entry). This
gives a spectrum of processing architectures:

| Item     | ALT-GEN  | ALT-NEG        | Category      |
|----------|----------|----------------|---------------|
| *some*   | online   | online         | Quantifier    |
| *three*  | offline  | online         | Numeral       |
| FC *or*  | —        | different mech | FC disjunction|

## Experimental Evidence (6 experiments)

Structural priming paradigm: if two expressions share a sub-computation,
processing one facilitates processing the other.

- **Exp 1–2**: *some* → numerals (bidirectional priming)
- **Exp 3–4**: numerals → *some* (bidirectional priming)
- **Exp 5**: FC *or* → *some* (NO priming)
- **Exp 6**: FC *or* → numerals (NO priming)

The pattern falsifies any uniform account: shared ALT-NEG between *some*
and numerals, but FC uses an entirely different mechanism (assertion-based
per @cite{bar-lev-fox-2017}, not negation-based).

-/

namespace Phenomena.ScalarImplicatures.Studies.MeyerFeiman2021


/-! ## Processing Architecture Types -/

/-- How alternatives are made available during processing.

Meyer & Feiman's key theoretical distinction (§1.2, §5):
- `online`: alternatives computed from the Horn scale at processing time
  (e.g., *some* → {*most*, *all*} derived from ⟨some, most, all⟩)
- `offline`: alternatives stored with the lexical entry
  (e.g., *three* → {*one*, *two*, *four*,...} stored in the numeral system) -/
inductive AltGenSource where
  /-- Computed from Horn scale at processing time -/
  | online
  /-- Pre-stored with lexical entry -/
  | offline
  deriving DecidableEq, BEq, Repr, Inhabited

/-- What is done with alternatives once generated.

The mechanism by which un-uttered alternatives contribute to meaning:
- `exhaustification`: negate alternatives (standard SI: "not all")
- `innocentInclusion`: assert alternatives (FC: "may A ∧ may B")
- `none`: no strengthening operation applies -/
inductive AltNegMechanism where
  /-- IE: negate alternatives (standard scalar implicature) -/
  | exhaustification
  /-- II: assert alternatives (free choice inference) -/
  | innocentInclusion
  /-- No strengthening -/
  | none
  deriving DecidableEq, BEq, Repr, Inhabited

/-- A scalar item's implicature processing profile.

Combines ALT-GEN source and ALT-NEG mechanism to classify how a given
scalar item's implicature is computed. Meyer & Feiman argue that these
two dimensions are independently parameterizable (§5). -/
structure ProcessProfile where
  /-- How alternatives are generated -/
  altGen : AltGenSource
  /-- What is done with alternatives -/
  altNeg : AltNegMechanism
  deriving DecidableEq, BEq, Repr

instance : Inhabited ProcessProfile where
  default := ⟨.online, .exhaustification⟩


/-! ## Scalar Item Classification -/

/-- The three classes of scalar item distinguished by Meyer & Feiman.

The paper argues these are not merely taxonomic labels but reflect genuine
processing differences, as demonstrated by the priming pattern. -/
inductive ScalarItemClass where
  /-- Quantifiers: ALT-GEN online, ALT-NEG online (§2.1) -/
  | quantifier
  /-- Numerals: ALT-GEN offline, ALT-NEG online (§2.2) -/
  | numeral
  /-- Free choice disjunction: different mechanism entirely (§2.3) -/
  | freeChoiceDisjunction
  deriving DecidableEq, BEq, Repr, Inhabited

/-- The process profile for each scalar item class.

This is the paper's central theoretical claim (Table 1, §5). -/
def classProfile : ScalarItemClass → ProcessProfile
  | .quantifier          => ⟨.online, .exhaustification⟩
  | .numeral             => ⟨.offline, .exhaustification⟩
  | .freeChoiceDisjunction => ⟨.online, .innocentInclusion⟩

/-- Concrete scalar items used in the experiments. -/
inductive ScalarItem where
  | some_       -- Experiments 1–6 (target or prime)
  | three       -- Experiments 1–6 (target or prime)
  | four        -- Experiments 1–4
  | fcOr        -- Experiments 5–6 (FC disjunction under modal)
  deriving DecidableEq, BEq, Repr

/-- Classify a concrete item into its class. -/
def itemClass : ScalarItem → ScalarItemClass
  | .some_  => .quantifier
  | .three  => .numeral
  | .four   => .numeral
  | .fcOr   => .freeChoiceDisjunction

/-- Get the process profile for a concrete item. -/
def itemProfile (item : ScalarItem) : ProcessProfile :=
  classProfile (itemClass item)


/-! ## Priming Predictions

Meyer & Feiman's reasoning (§2.3, §5):

- Two items **prime** each other iff they share a sub-computation
- Shared ALT-NEG → cross-category priming (*some* ↔ numerals)
- Different ALT-NEG → no priming (FC ↮ *some*, FC ↮ numerals)
- Shared vs different ALT-GEN → asymmetry in priming strength -/

/-- Whether two scalar item classes share ALT-NEG. -/
def sharesAltNeg (a b : ScalarItemClass) : Bool :=
  (classProfile a).altNeg == (classProfile b).altNeg

/-- Whether two scalar item classes share ALT-GEN. -/
def sharesAltGen (a b : ScalarItemClass) : Bool :=
  (classProfile a).altGen == (classProfile b).altGen

/-- Predicted priming between two classes: occurs iff shared ALT-NEG. -/
def predictsPriming (a b : ScalarItemClass) : Bool :=
  sharesAltNeg a b


/-! ## Experimental Data -/

/-- Result of a structural priming experiment.

Each experiment tests whether processing a scalar implicature with
one item type facilitates processing with another. -/
structure PrimingExperiment where
  /-- Experiment identifier -/
  experiment : String
  /-- Prime scalar item class -/
  primeClass : ScalarItemClass
  /-- Target scalar item class -/
  targetClass : ScalarItemClass
  /-- Was significant priming observed? -/
  primingObserved : Bool
  /-- Number of participants -/
  nParticipants : Nat
  /-- Effect description -/
  effectDescription : String
  deriving Repr

/-- Experiments 1–2: *some* primes numerals. -/
def exp1_2 : PrimingExperiment :=
  { experiment := "Exp 1–2"
  , primeClass := .quantifier
  , targetClass := .numeral
  , primingObserved := true
  , nParticipants := 98
  , effectDescription := "After computing 'some→not all', participants more likely to compute 'three→exactly three'" }

/-- Experiments 3–4: numerals prime *some*. -/
def exp3_4 : PrimingExperiment :=
  { experiment := "Exp 3–4"
  , primeClass := .numeral
  , targetClass := .quantifier
  , primingObserved := true
  , nParticipants := 100
  , effectDescription := "After computing 'three→exactly three', participants more likely to compute 'some→not all'" }

/-- Experiment 5: FC *or* does NOT prime *some*. -/
def exp5 : PrimingExperiment :=
  { experiment := "Exp 5"
  , primeClass := .freeChoiceDisjunction
  , targetClass := .quantifier
  , primingObserved := false
  , nParticipants := 100
  , effectDescription := "FC 'or' computation does not facilitate 'some→not all'" }

/-- Experiment 6: FC *or* does NOT prime numerals. -/
def exp6 : PrimingExperiment :=
  { experiment := "Exp 6"
  , primeClass := .freeChoiceDisjunction
  , targetClass := .numeral
  , primingObserved := false
  , nParticipants := 100
  , effectDescription := "FC 'or' computation does not facilitate 'three→exactly three'" }

/-- All experiments from @cite{meyer-feiman-2021}. -/
def allExperiments : List PrimingExperiment :=
  [exp1_2, exp3_4, exp5, exp6]


/-! ## Key Empirical Findings -/

/-- The three main findings of the paper (§5). -/
structure MainFindings where
  /-- Finding 1: Bidirectional priming between *some* and numerals -/
  someNumeralPriming : Bool
  /-- Finding 2: No priming between FC *or* and *some* -/
  noFCSomePriming : Bool
  /-- Finding 3: No priming between FC *or* and numerals -/
  noFCNumeralPriming : Bool
  deriving Repr

def mainFindings : MainFindings :=
  { someNumeralPriming := true
  , noFCSomePriming := true
  , noFCNumeralPriming := true }


/-! ## Connections to Other Phenomena

The process profile classification connects to several existing
phenomena in linglib. -/

/-- For each scale in the library's basic data, which process profile applies.

This connects Meyer & Feiman's classification to the Horn scale data
in `Phenomena.ScalarImplicatures.Basic`. -/
def scaleProfile (scale : Phenomena.ScalarImplicatures.HornScaleDatum) : ProcessProfile :=
  if scale.name == "Numerals" then
    classProfile .numeral
  else
    classProfile .quantifier

/-- Numeral Hurford rescue (e.g., "three or all") involves the offline/online
    profile — alternatives are stored, so exhaustification ("exactly three")
    is immediately available for Hurford rescue. -/
def hurfordNumeralProfile : ProcessProfile := classProfile .numeral

/-- FC phenomena use a fundamentally different mechanism from standard SI.

This connects to `Phenomena.Modality.FreeChoice`, where the FC inference
◇(A ∨ B) → ◇A ∧ ◇B is derived via Innocent Inclusion rather than
Innocent Exclusion. -/
def freeChoiceProfile : ProcessProfile := classProfile .freeChoiceDisjunction

/-- The asymmetry between SI and FC is a processing architecture difference,
    not just a semantic difference. Both involve alternatives, but:
    - SI: negate alternatives (IE)
    - FC: assert alternatives (II) -/
structure SIvsFCContrast where
  /-- Standard SI mechanism -/
  siMechanism : AltNegMechanism
  /-- FC mechanism -/
  fcMechanism : AltNegMechanism
  /-- Are they the same? -/
  sameMechanism : Bool
  deriving Repr

def siVsFc : SIvsFCContrast :=
  { siMechanism := .exhaustification
  , fcMechanism := .innocentInclusion
  , sameMechanism := false }


/-! ## Falsified Accounts

Meyer & Feiman's data rules out several theoretical positions (§5). -/

/-- Theoretical positions about scalar inference processing. -/
inductive TheoreticalPosition where
  /-- All scalar inferences use the same online computation -/
  | uniformOnline
  /-- All scalar inferences use stored/default meanings -/
  | uniformOffline
  /-- Scalar items differ in ALT-GEN but share ALT-NEG (M&F's position) -/
  | decomposed
  /-- Each scalar item class is fully independent -/
  | fullyIndependent
  deriving DecidableEq, BEq, Repr

/-- Whether a theoretical position is compatible with the priming data. -/
def compatibleWithData (pos : TheoreticalPosition) : Bool :=
  match pos with
  | .uniformOnline =>
    -- Predicts uniform priming across all pairs: falsified by Exp 5–6
    false
  | .uniformOffline =>
    -- Predicts no cross-category priming: falsified by Exp 1–4
    false
  | .decomposed =>
    -- Predicts selective priming (shared ALT-NEG only): confirmed
    true
  | .fullyIndependent =>
    -- Predicts no cross-category priming: falsified by Exp 1–4
    false

-- ============================================================================
-- § Process Profile Verification
-- ============================================================================

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

-- § Per-Experiment Verification

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

-- § Falsification Theorems

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

-- § Connections to Basic SI Data

/-- The quantifier scale ⟨some, all⟩ has an online ALT-GEN profile. -/
theorem quantifier_scale_online :
    (scaleProfile Phenomena.ScalarImplicatures.quantifierScale).altGen = .online := rfl

/-- The numeral scale ⟨1, 2, 3,...⟩ has an offline ALT-GEN profile. -/
theorem numeral_scale_offline :
    (scaleProfile Phenomena.ScalarImplicatures.numeralScale).altGen = .offline := rfl

/-- Both quantifier and numeral scales share ALT-NEG = exhaustification. -/
theorem both_scales_exhaust :
    (scaleProfile Phenomena.ScalarImplicatures.quantifierScale).altNeg =
    (scaleProfile Phenomena.ScalarImplicatures.numeralScale).altNeg := rfl

/-- The connective scale ⟨or, and⟩ (standard, non-FC) also uses exhaustification. -/
theorem connective_scale_exhaust :
    (scaleProfile Phenomena.ScalarImplicatures.connectiveScale).altNeg = .exhaustification := rfl

-- § Connections to Hurford Rescue

/-- Numeral Hurford rescue: "three or all" is rescued because
    exh(three) = "exactly three" is available via offline alternatives. -/
theorem hurford_numeral_rescue_available :
    hurfordNumeralProfile.altGen = .offline := rfl

/-- Both rescued-numeral and rescued-quantifier Hurford cases use
    the same strengthening mechanism (exhaustification). -/
theorem hurford_same_neg_mechanism :
    hurfordNumeralProfile.altNeg =
    (scaleProfile Phenomena.ScalarImplicatures.quantifierScale).altNeg := rfl

-- § Connections to Free Choice Phenomena

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
    profile using innocentInclusion. -/
theorem fc_cancellable_consistent :
    Phenomena.Modality.FreeChoice.explicitCancellation.felicitous = true := rfl

-- § The Spectrum as a Whole

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
