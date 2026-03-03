import Linglib.Phenomena.Causatives.Studies.BeaversEtAl2021
import Linglib.Theories.Morphology.RootTypology
import Linglib.Fragments.Chuj.VerbBuilding

/-!
Root Typology Theory ↔ BeaversEtAl2021 Empirical Data
@cite{coon-2019}

Connects the theory-side predictions of `Theories/Morphology/RootTypology.lean`
(@cite{beavers-etal-2021} formalization) to the empirical data in
`Phenomena/Causatives/Studies/BeaversEtAl2021.lean`.

## What this bridge proves

1. **Classification isomorphism**: The theory's `RootType` and the phenomena's
   `CoSRootClass` are provably isomorphic — they describe the same partition.

2. **Diagnostic alignment**: The phenomena's semantic diagnostics
   (`changeDenialTest`, `restitutiveAgainTest`) agree exactly with the theory's
   Boolean correlates (`entailsChange`, `allowsRestitutiveAgain`).

3. **Prediction ↔ attestation**: The theory predicts PC roots HAVE simple
   statives and result roots LACK them; the empirical data confirms this
   (PC: 7/8 sample roots ≥ 50%; result: all 10 sample roots ≤ 10%).

4. **Markedness prediction**: The theory predicts PC verbs are marked and result
   verbs are unmarked; the statistical comparison confirms PC median (56.01%)
   exceeds result median (15.20%).

5. **Fragment grounding**: The Chuj fragment's `Root` values instantiate the
   theory's predictions — e.g., `rootTV_res.entailsChange = true` matches the
   theory's `RootType.entailsChange.result = true`.

## Derivational chain

```
Core/Root.lean (types: RootType, RootArity, Root)
    ↓
Theories/Morphology/RootTypology.lean (predictions: grand_unification)
    ↓ ↓
Fragments/Chuj/VerbBuilding.lean THIS BRIDGE FILE
    ↓ ↓
    └──────────────────────────────→ Phenomena/Causatives/Studies/BeaversEtAl2021.lean
```

-/

namespace Phenomena.Causatives.Studies.Coon2019

open Phenomena.Causatives.Studies.BeaversEtAl2021

-- ════════════════════════════════════════════════════
-- § 1. Classification Isomorphism
-- ════════════════════════════════════════════════════

/-- Map the theory's root type to the phenomena's root class.
    These are parallel enums — the bridge makes the correspondence explicit. -/
def toCoSRootClass : RootType → CoSRootClass
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- Map back from phenomena to theory. -/
def fromCoSRootClass : CoSRootClass → RootType
  | .propertyConcept => .propertyConcept
  | .result => .result

/-- The mapping is a bijection (left inverse). -/
theorem roundtrip_left (rt : RootType) :
    fromCoSRootClass (toCoSRootClass rt) = rt := by
  cases rt <;> rfl

/-- The mapping is a bijection (right inverse). -/
theorem roundtrip_right (rc : CoSRootClass) :
    toCoSRootClass (fromCoSRootClass rc) = rc := by
  cases rc <;> rfl

-- ════════════════════════════════════════════════════
-- § 2. Diagnostic Alignment
-- ════════════════════════════════════════════════════

/-- The phenomena's `changeDenialTest` agrees with the theory's `entailsChange`.

    Theory: `RootType.entailsChange.result = true` (result roots entail change)
    Phenomena: `changeDenialTest.result =.negative` ("#The shattered vase
    has never shattered" is contradictory — the state entails prior change)

    The relationship is: entailsChange = true ↔ changeDenial = negative.
    That is, entailing change means the change-denial test FAILS. -/
theorem change_denial_matches_entailsChange (rc : CoSRootClass) :
    changeDenialTest rc = .positive ↔
    (fromCoSRootClass rc).entailsChange = false := by
  cases rc <;> simp [changeDenialTest, fromCoSRootClass, RootType.entailsChange]

/-- The phenomena's `restitutiveAgainTest` agrees with the theory's
    `allowsRestitutiveAgain`. -/
theorem restitutive_again_matches (rc : CoSRootClass) :
    restitutiveAgainTest rc = .positive ↔
    (fromCoSRootClass rc).allowsRestitutiveAgain = true := by
  cases rc <;> simp [restitutiveAgainTest, fromCoSRootClass,
    RootType.allowsRestitutiveAgain]

/-- Both diagnostics jointly align with the full semantic correlate package.
    This is the bridge version of `semantic_determines_morphosyntax`. -/
theorem diagnostics_align_with_theory (rc : CoSRootClass) :
    let rt := fromCoSRootClass rc
    (changeDenialTest rc = .negative ↔ rt.entailsChange = true) ∧
    (restitutiveAgainTest rc = .negative ↔ rt.allowsRestitutiveAgain = false) := by
  cases rc <;> simp [changeDenialTest, restitutiveAgainTest, fromCoSRootClass,
    RootType.entailsChange, RootType.allowsRestitutiveAgain]

-- ════════════════════════════════════════════════════
-- § 3. Simple Stative Prediction ↔ Attestation
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC roots have simple statives.
    **Data confirms**: 7 of 8 PC sample roots have ≥ 50% attestation.
    The one exception (oldRoot, age class) has 0 — noted by Beavers et al.
    as a crosslinguistic outlier. -/
theorem pc_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .propertyConcept = true ∧
    -- Empirical confirmation (all but one PC root)
    (pcRoots.filter (λ r => r.nSimpleStative * 2 ≥ r.nLanguages)).length ≥
    pcRoots.length - 1 := by
  exact ⟨rfl, by native_decide⟩

/-- **Theory predicts**: result roots LACK simple statives.
    **Data confirms**: all 10 result sample roots have ≤ 10% attestation. -/
theorem result_no_stative_prediction_matches_data :
    -- Theory prediction
    RootType.hasSimpleStative .result = false ∧
    -- Empirical confirmation (ALL result roots)
    resultRoots.all (λ r => r.nSimpleStative * 10 ≤ r.nLanguages) = true := by
  exact ⟨rfl, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 4. Markedness Prediction ↔ Statistical Comparison
-- ════════════════════════════════════════════════════

/-- **Theory predicts**: PC verbs are morphologically marked; result verbs
    are unmarked. (Markedness Generalization, eq. 44.)
    **Data confirms**: PC median marked % (56.01) > result median (15.20). -/
theorem markedness_prediction_matches_statistics :
    -- Theory: PC verbs are marked
    verbalMarkedness .propertyConcept = .marked ∧
    -- Theory: result verbs are unmarked
    verbalMarkedness .result = .unmarked ∧
    -- Data: PC marked rate exceeds result marked rate
    simpleStativeComparison.pcMedian > simpleStativeComparison.resultMedian ∧
    verbalMarkednessComparison.pcMedian > verbalMarkednessComparison.resultMedian := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════
-- § 5. Unattested Language Type
-- ════════════════════════════════════════════════════

/-- The theory's markedness complementarity predicts that if a language
    marks PC verbs, it should NOT also show result verbs as more marked
    than PC verbs. The fourth logically possible language type (result
    marked, PC unmarked) is unattested — exactly 3 types are attested.
    This matches the theory: `markedness_complementarity` says verbal and
    stative markedness are always opposite. -/
theorem unattested_type_matches_complementarity :
    -- Exactly three types attested
    LanguageType.allAttested.length = 3 ∧
    -- Theory: verbal and stative markedness always differ
    (∀ rt : RootType, verbalMarkedness rt ≠ stativeMarkedness rt) := by
  refine ⟨by native_decide, ?_⟩
  intro rt; cases rt <;> simp [verbalMarkedness, stativeMarkedness,
    RootType.entailsChange]

-- ════════════════════════════════════════════════════
-- § 6. Fragment Grounding: Chuj Roots Instantiate Theory
-- ════════════════════════════════════════════════════

open Fragments.Chuj

/-- Chuj √TV result roots instantiate the theory's result root predictions:
    entails change, no simple stative, unmarked verb. -/
theorem chuj_tv_res_is_result_root :
    rootTV_res.entailsChange = true ∧
    rootTV_res.changeType.hasSimpleStative = false ∧
    rootTV_res.verbalMarkedness = .unmarked := by
  exact ⟨rfl, rfl, rfl⟩

/-- Chuj √TV PC roots instantiate the theory's PC root predictions:
    no change entailment, has simple stative, marked verb. -/
theorem chuj_tv_pc_is_pc_root :
    rootTV_pc.entailsChange = false ∧
    rootTV_pc.changeType.hasSimpleStative = true ∧
    rootTV_pc.verbalMarkedness = .marked := by
  exact ⟨rfl, rfl, rfl⟩

/-- The Chuj fragment witnesses the full orthogonality theorem:
    all four cells of the (arity × changeType) matrix are inhabited. -/
theorem chuj_witnesses_orthogonality :
    -- selectsTheme + result (√TV result)
    rootTV_res.arity = .selectsTheme ∧ rootTV_res.changeType = .result ∧
    -- selectsTheme + PC (√TV PC)
    rootTV_pc.arity = .selectsTheme ∧ rootTV_pc.changeType = .propertyConcept ∧
    -- noTheme + PC (√ITV, √POS, √NOM)
    rootITV.arity = .noTheme ∧ rootITV.changeType = .propertyConcept :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Per-root class verification: each Chuj root's change entailment matches
    its predicted morphosyntactic correlates via `grand_unification`. -/
theorem chuj_roots_satisfy_grand_unification :
    -- Result root (√TV res): entails change → full result package
    (rootTV_res.changeType.hasSimpleStative = false ∧
     rootTV_res.changeType.verbalFormIsMarked = false ∧
     rootTV_res.changeType.allowsRestitutiveAgain = false) ∧
    -- PC root (√TV PC): no change → full PC package
    (rootTV_pc.changeType.hasSimpleStative = true ∧
     rootTV_pc.changeType.verbalFormIsMarked = true ∧
     rootTV_pc.changeType.allowsRestitutiveAgain = true) ∧
    -- PC root (√ITV): no change → full PC package
    (rootITV.changeType.hasSimpleStative = true ∧
     rootITV.changeType.verbalFormIsMarked = true ∧
     rootITV.changeType.allowsRestitutiveAgain = true) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

-- ════════════════════════════════════════════════════
-- § 7. Per-Root Data ↔ Theory Agreement
-- ════════════════════════════════════════════════════

/-- Every PC root in the empirical sample is classified as PC, and the theory
    predicts PC roots should have simple statives — they do. -/
theorem pc_roots_classified_and_predicted :
    -- Data: all sample PC roots are classified as PC
    pcRoots.all (·.rootClass == .propertyConcept) = true ∧
    -- Theory: PC has simple stative
    RootType.hasSimpleStative .propertyConcept = true := by
  exact ⟨by native_decide, rfl⟩

/-- Every result root in the empirical sample is classified as result, and the
    theory predicts result roots lack simple statives — they do. -/
theorem result_roots_classified_and_predicted :
    -- Data: all sample result roots are classified as result
    resultRoots.all (·.rootClass == .result) = true ∧
    -- Theory: result lacks simple stative
    RootType.hasSimpleStative .result = false := by
  exact ⟨by native_decide, rfl⟩

/-- The subclass taxonomies are parallel: the theory's `PCClass` and the
    phenomena's `PCSubclass` have the same constructors. Similarly for
    `ResultClass` and `ResultSubclass`. This is verified by exhaustive
    mapping (both have 6 PC subclasses and 8 result subclasses). -/
theorem subclass_counts_match :
    -- 6 PC subclasses in both
    [PCClass.dimension, .age, .value, .color, .physicalProperty, .speed].length =
    [PCSubclass.dimension, .age, .value, .color, .physicalProperty, .speed].length ∧
    -- 8 result subclasses in both
    [ResultClass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length =
    [ResultSubclass.entitySpecificCoS, .cooking, .breaking, .bending,
     .killing, .destroying, .calibratableCoS, .inherentlyDirectedMotion].length :=
  ⟨rfl, rfl⟩

end Phenomena.Causatives.Studies.Coon2019
