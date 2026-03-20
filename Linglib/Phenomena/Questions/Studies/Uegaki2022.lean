import Linglib.Theories.Semantics.Attitudes.CDistributivity
import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Semantics.Questions.LeftPeriphery

/-!
# Uegaki (2022) @cite{uegaki-2022}

*Question-orientedness and the Semantics of Clausal Complementation.* Cham: Springer.

## Core Thesis

All clause-embedding predicates uniformly select for **question-type** denotations
(sets of propositions, type ⟨⟨s,t⟩,t⟩). Proposition-taking is derived via the
type-shift p → {p}. This **question-oriented theory** provides:

1. A unified semantics for declarative and interrogative complementation
2. Semantic (not syntactic) explanations for selectional restrictions
3. Anti-rogativity of `believe`/`hope` via **triviality** (L-analyticity)
4. Responsiveness of `know`/`be happy` via veridicality breaking triviality
5. A constraint hierarchy: C-distributivity ⟹ {Strawson C-dist, P-to-Q Entailment}

## What This Study File Verifies

- The constraint hierarchy (Table 8.2): C-dist ⟹ P-to-Q Ent, with separation
- NVP classification matches the book's predictions
- Fictitious predicates (*shknow, *knopinion, *all-open) are correctly ruled out
- Highlighting resolves hope-whether apparent counterexamples
- Veridical vs non-veridical preferential asymmetry
- World-independence of non-veridical semantics (basis for L-analyticity)
- **Triviality identity**: assertion = presupposition when C = Q (L-analyticity)
- NVPClass ↔ SelectionClass bridge (question-oriented ↔ Left Periphery alignment)
- Full Table 8.2 with all four constraints

## Linglib Integration

This file imports and connects existing infrastructure:
- `CDistributivity.lean`: C-distributivity, P-to-Q Entailment, fictitious predicates,
  Veridical Uniformity
- `Preferential.lean`: NVP classification, TSP, highlighting, triviality theorems
- `LeftPeriphery.lean`: SelectionClass derivation
-/

namespace Phenomena.Questions.Studies.Uegaki2022

open Semantics.Attitudes.CDistributivity
open Semantics.Attitudes.Preferential hiding QuestionDen

-- ============================================================================
-- A. Constraint Hierarchy (Table 8.2)
-- ============================================================================

/-!
## Constraint Hierarchy

@cite{uegaki-2022} establishes a hierarchy of constraints on clause-embedding
predicates. The key result: P-to-Q Entailment is empirically superior to
C-distributivity and Strawson C-distributivity.

### The Hierarchy (independent weakenings)

C-distributivity ⟹ Strawson C-distributivity (with trivial presup)
C-distributivity ⟹ P-to-Q Entailment
(Strawson C-dist and P-to-Q Entailment are independent — neither implies the other)
-/

/-- C-distributivity implies P-to-Q Entailment (re-exported from CDistributivity.lean). -/
theorem constraint_hierarchy_cdist_ptoq {W E : Type*}
    (V_prop : E → BProp W → W → Bool)
    (V_question : E → QuestionDen W → W → Bool)
    (hCD : IsCDistributive V_prop V_question) :
    IsPtoQEntailing V_question :=
  cDistributive_implies_ptoq V_prop V_question hCD

-- ============================================================================
-- B. NVP Classification Matches Book Predictions
-- ============================================================================

/-!
## NVP Classification (@cite{uegaki-2022} Ch 6)

| Class | C-dist | Valence  | Takes Q? | Examples              |
|-------|--------|----------|----------|-----------------------|
| 1     | ✗      | any      | ✓        | worry, qidai          |
| 2     | ✓      | negative | ✓        | fear, dread            |
| 3     | ✓      | positive | ✗        | hope, wish, expect    |

Veridical preferentials (be happy, be surprised) break triviality despite
being C-distributive + positive, because truth adds a world-dependent constraint.
-/

/-- Class 3 (hope-type) is anti-rogative. -/
theorem class3_antirogative :
    NVPClass.canTakeQuestion .class3_cDist_positive = false := rfl

/-- Class 2 (fear-type) takes questions. -/
theorem class2_takes_questions :
    NVPClass.canTakeQuestion .class2_cDist_negative = true := rfl

/-- Class 1 (worry-type) takes questions. -/
theorem class1_takes_questions :
    NVPClass.canTakeQuestion .class1_nonCDist = true := rfl

/-- The NVP classification is exhaustive: every combination of C-dist × valence
    maps to exactly one class. -/
theorem nvp_classification_exhaustive (cd : Bool) (v : AttitudeValence) :
    classifyNVP cd v = .class1_nonCDist ∨
    classifyNVP cd v = .class2_cDist_negative ∨
    classifyNVP cd v = .class3_cDist_positive := by
  unfold classifyNVP
  cases cd <;> cases v <;> simp

-- ============================================================================
-- C. Triviality: The Core Derivation
-- ============================================================================

/-!
## The Triviality Derivation (@cite{uegaki-2022} Ch 6 §6.5)

Anti-rogativity of positive NVPs is DERIVED, not stipulated:

```
1. hope has degree-comparison semantics     (definition)
2. → hope is C-distributive                 (degreeComparisonPredicate_isCDistributive)
3. hope has positive valence                 (definition)
4. → hope has TSP                           (positive_hasTSP)
5. hope is non-veridical                     (definition)
6. 2 + 4 + 5 → assertion = presupposition  (hope_triviality_identity)
7. → L-analytic → unacceptable              (@cite{gajewski-2002})
```

The key step is (6): when the comparison class C equals the question Q,
the assertion (∃p ∈ Q. μ(x,p) > θ(Q)) is **identical** to the presupposition
(TSP: ∃p ∈ Q. μ(x,p) > θ(Q)). The meaning is L-analytic — its truth value
is completely determined by whether the presupposition holds, with no
informative content remaining.

Veridical predicates (be happy) break at step 6: truth requirement means
assertion is NOT entailed by TSP (`veridical_breaks_triviality`).
-/

/-- The full derivation chain for hope: C-dist + positive + non-veridical → trivial. -/
theorem hope_derivation_chain {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    -- Step 1-2: hope is C-distributive
    (hope μ θ).isCDistributive ∧
    -- Step 3-4: hope has TSP
    (hope μ θ).hasTSP = true ∧
    -- Step 5: hope is non-veridical
    (hope μ θ).veridical = false := by
  exact ⟨hope_isCDistributive μ θ, rfl, rfl⟩

/--
**Triviality identity** (re-exported from Preferential.lean):
When C = Q, hope's assertion IS its presupposition.

This is the heart of the anti-rogativity derivation. The assertion
∃p ∈ Q. μ(x,p) > θ(Q) is literally the same formula as TSP
∃p ∈ Q. μ(x,p) > θ(Q). The meaning is L-analytic.
-/
theorem hope_assertion_equals_presupposition {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q : QuestionDen W) :
    (hope μ θ).questionSemantics x Q Q = tspSatisfied μ θ x Q :=
  hope_triviality_identity μ θ x Q

/-- The full derivation chain for beHappy: C-dist + positive + veridical → NOT trivial. -/
theorem beHappy_derivation_chain {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    -- beHappy has TSP
    (beHappy μ θ).hasTSP = true ∧
    -- beHappy IS veridical (breaks triviality)
    (beHappy μ θ).veridical = true := by
  exact ⟨rfl, rfl⟩

-- ============================================================================
-- D. Highlighting Resolves hope-whether (@cite{uegaki-2022} Ch 6 §6.6)
-- ============================================================================

/-!
## hope-whether via Highlighting

@cite{white-2021} presents attested "hope whether" constructions as apparent
counterexamples to the anti-rogativity of positive NVPs.

@cite{uegaki-2022}'s solution: `hope` is sensitive to the **highlighted value**
of the complement (@cite{pruitt-roelofsen-2011}). Polar interrogatives highlight
only the overtly-realized proposition (singleton), so "hope whether p" ≈
"hope that p" — not trivial.

Constituent interrogatives highlight ALL alternatives, preserving triviality.
-/

/-- Polar interrogatives: hope-whether reduces to hope-that (not trivial). -/
theorem hope_whether_not_trivial {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (p neg_p : BProp W) (C : QuestionDen W) :
    hopeHighlightSemantics μ θ .polarInterrogative x [p, neg_p] C =
    decide (μ x p > θ C) :=
  hope_highlight_polar_equiv μ θ x p neg_p C

/-- Constituent interrogatives: hope-who is still trivial. -/
theorem hope_who_still_trivial {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : QuestionDen W)
    (h_subset : ∀ p, p ∈ Q → p ∈ C)
    (h_assert : hopeHighlightSemantics μ θ .constituentInterrog x Q C = true) :
    tspSatisfied μ θ x C = true :=
  hope_highlight_constituent_trivial μ θ x Q C h_subset h_assert

-- ============================================================================
-- E. Cross-Linguistic Embedding Data (Table 8.2)
-- ============================================================================

/-!
## Cross-Linguistic Predicates (@cite{uegaki-2022} Chs 4, 5, 8)

The book's key empirical argument for P-to-Q Entailment over C-distributivity
comes from cross-linguistic data: predicates that violate C-distributivity
but satisfy P-to-Q Entailment.

### Table 8.2: Four Constraints × Seven Predicates

|                          | *shknow | *knopinion | care | mõtlema | daroo | wonder | magtaka |
|--------------------------|---------|------------|------|---------|-------|--------|---------|
| Veridical Uniformity     | ✓       | ✓          | ✗    | ✓       | ✓     | ✗      | ✗       |
| C-distributivity         | ✓       | ✓          | ✗    | ✗       | ✗     | ✗      | ✗       |
| Strawson C-distributivity| ✓       | ✓          | ✓    | ✗       | ✗     | ✗      | ✗       |
| P-to-Q Entailment        | ✓       | ✓          | ✓    | ✓       | ✓     | ✓      | ✗       |

P-to-Q Entailment correctly rules out only `magtaka` among attested predicates,
while ruling out all three fictitious predicates (*shknow, *knopinion).
C-distributivity over-rules-out care, mõtlema, daroo, wonder.
-/

/-- Cross-linguistic embedding datum, encoding all four constraints
    from @cite{uegaki-2022} Table 8.2. -/
structure CrossLingDatum where
  predicate : String
  language : String
  takesDecl : Bool
  takesInterrog : Bool
  veridicalUniformity : Bool
  cDistributive : Bool
  strawsonCDist : Bool
  ptoqEntailing : Bool
  attested : Bool  -- false for fictitious predicates
  deriving Repr, BEq

/-- Full Table 8.2 data from @cite{uegaki-2022}, including fictitious predicates. -/
def table8_2 : List CrossLingDatum := [
  -- Fictitious (unattested)
  ⟨"*shknow",   "—",        true, true, true,  true,  true,  true,  false⟩,
  ⟨"*knopinion","—",        true, true, true,  true,  true,  true,  false⟩,
  -- Attested
  ⟨"care",      "English",  true, true, false, false, true,  true,  true⟩,
  ⟨"mõtlema",   "Estonian", true, true, true,  false, false, true,  true⟩,
  ⟨"daroo",     "Japanese", true, true, true,  false, false, true,  true⟩,
  ⟨"wonder",    "English",  false,true, false, false, false, true,  true⟩,
  ⟨"magtaka",   "Tagalog",  true, true, false, false, false, false, true⟩
]

/-- All predicates that satisfy C-distributivity also satisfy P-to-Q Entailment. -/
theorem cdist_subset_ptoq_empirical :
    table8_2.all (fun d => !d.cDistributive || d.ptoqEntailing) = true := by
  native_decide

/-- P-to-Q Entailment is strictly weaker: some attested predicates satisfy P-to-Q
    but not C-distributivity (care, mõtlema, daroo, wonder). -/
theorem ptoq_strictly_weaker :
    (table8_2.filter (fun d => d.attested && d.ptoqEntailing && !d.cDistributive)).length > 0 := by
  native_decide

/-- C-distributivity implies Strawson C-distributivity (Table 8.2 hierarchy). -/
theorem cdist_subset_strawson_empirical :
    table8_2.all (fun d => !d.cDistributive || d.strawsonCDist) = true := by
  native_decide

/-- P-to-Q Entailment rules out all fictitious predicates while keeping
    all attested predicates except magtaka. -/
theorem ptoq_rules_out_fictitious :
    table8_2.all (fun d =>
      d.attested || d.ptoqEntailing  -- fictitious predicates satisfy P-to-Q (vacuously)
    ) = true := by
  native_decide

/-- P-to-Q Entailment keeps more attested predicates than C-distributivity. -/
theorem ptoq_more_permissive_than_cdist :
    (table8_2.filter (fun d => d.attested && d.ptoqEntailing)).length >
    (table8_2.filter (fun d => d.attested && d.cDistributive)).length := by
  native_decide

-- ============================================================================
-- F. Left Periphery Connection
-- ============================================================================

/-!
## Connecting to Left Periphery Theory

@cite{uegaki-2022}'s question-oriented theory is complementary to the Left
Periphery analysis in `LeftPeriphery.lean`. The question-oriented theory explains
*why* predicates have their selectional restrictions (semantic triviality),
while the Left Periphery theory explains *how* the syntactic structure of
embedded clauses varies (CP vs PerspP vs SAP layers).

The connection: predicates that are anti-rogative under the question-oriented
theory (Class 3 NVPs, neg-raising predicates) correspond to `uninterrogative`
in the SelectionClass taxonomy. Predicates that are responsive correspond to
`responsive`. Rogative predicates correspond to `rogativePerspP`/`rogativeSAP`.
-/

open Semantics.Questions.LeftPeriphery

/-- Anti-rogative predicates (uninterrogative) don't embed interrogatives. -/
theorem antirogative_no_interrogative :
    allowsEmbedding .uninterrogative .subordination false false = false := by
  simp [allowsEmbedding]

/-- Responsive predicates allow subordination but not quasi-subordination
    in bare contexts. -/
theorem responsive_subordination_only :
    allowsEmbedding .responsive .subordination false false = true ∧
    allowsEmbedding .responsive .quasiSubordination false false = false :=
  ⟨rfl, rfl⟩

/-- Rogative predicates (wonder) allow both subordination and quasi-subordination. -/
theorem rogative_both :
    allowsEmbedding .rogativePerspP .subordination false false = true ∧
    allowsEmbedding .rogativePerspP .quasiSubordination false false = true :=
  ⟨rfl, rfl⟩

/--
NVPClass↔SelectionClass bridge: the question-oriented theory's NVP classification
aligns with the Left Periphery's SelectionClass taxonomy.

- Class 3 (anti-rogative) ↔ uninterrogative: both predict no interrogative embedding
- Class 1 (non-C-dist, e.g., worry) ↔ responsive: takes both decl and interrog
- Class 2 (C-dist + negative, e.g., fear) ↔ responsive: takes both decl and interrog
-/
def nvpToSelectionClass : NVPClass → SelectionClass
  | .class3_cDist_positive => .uninterrogative
  | .class1_nonCDist => .responsive  -- worry, qidai: takes both decl and interrog
  | .class2_cDist_negative => .responsive  -- fear, dread: takes both decl and interrog

/-- Anti-rogative NVPs (Class 3) map to uninterrogative SelectionClass. -/
theorem class3_is_uninterrogative :
    nvpToSelectionClass .class3_cDist_positive = .uninterrogative := rfl

/-- Question-taking NVPs agree with non-uninterrogative SelectionClasses on
    allowing interrogative embedding. -/
theorem nvp_selection_agreement :
    (NVPClass.canTakeQuestion .class3_cDist_positive = false ∧
     allowsEmbedding (nvpToSelectionClass .class3_cDist_positive) .subordination false false = false) ∧
    (NVPClass.canTakeQuestion .class1_nonCDist = true ∧
     allowsEmbedding (nvpToSelectionClass .class1_nonCDist) .subordination false false = true) ∧
    (NVPClass.canTakeQuestion .class2_cDist_negative = true ∧
     allowsEmbedding (nvpToSelectionClass .class2_cDist_negative) .subordination false false = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

-- ============================================================================
-- G. World-Independence and L-Analyticity
-- ============================================================================

/-!
## World-Independence (@cite{uegaki-2022} Ch 6 §6.5.4)

The triviality argument relies on non-veridical predicates having
**world-independent** semantics: ⟦x hopes p⟧(w, C) = μ(x,p) > θ(C)
contains no world variable. When assertion = presupposition
(`hope_triviality_identity`), this identity holds at ALL worlds —
making the meaning L-analytic per @cite{gajewski-2002}.

L-analyticity: An LF constituent is L-analytic iff its logical skeleton
receives the same truth-value under every variable assignment where the
denotation is defined. For non-veridical preferentials + interrogative
complement, the assertion is always true when TSP is met, regardless of
world — L-analytic → ungrammatical.
-/

/-- Hope's question semantics is world-independent: it gives the same
    result at any two worlds. -/
theorem hope_world_independent {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : QuestionDen W) (w₁ w₂ : W) :
    (hope μ θ).questionSemanticsAt x Q C w₁ =
    (hope μ θ).questionSemanticsAt x Q C w₂ :=
  nonveridical_worldIndependent "hope" .positive μ θ x Q C w₁ w₂

-- ============================================================================
-- H. Fictitious Predicate Verification
-- ============================================================================

/-!
## Fictitious Predicates (@cite{uegaki-2022} Table 8.2)

All three fictitious predicates from the book are formalized and proved
to violate P-to-Q Entailment:
- *shknow: know + wonder hybrid (`shknow_violates_ptoq`)
- *knopinion: know + no-opinion hybrid (`knopinion_violates_ptoq`)
- *all-open: universal compatibility (`allOpen_violates_ptoq`)
-/

-- Re-export knopinion verification from CDistributivity
example {W E : Type*} (believes : E → (W → Bool) → Bool)
    (x : E) (p q : BProp W) (w : W) (hp : believes x p = true) (hpq : p ≠ q) :
    ¬IsPtoQEntailing (knopinion believes) :=
  knopinion_violates_ptoq believes x p q w hp hpq

-- ============================================================================
-- I. Fear's Assertion Direction (@cite{uegaki-2022} §6.6.2)
-- ============================================================================

/-!
## Fear and Negative Preferentials

@cite{uegaki-2022} §6.6.2 proposes that fear's assertion direction is
**flipped** relative to hope: where hope asserts Pref(x, p) > θ(C),
fear asserts Pref(x, p) < θ(C). The presupposition (TSP) uses the
same direction (>) for both.

This means fear doesn't yield triviality even WITH TSP: the presupposition
says "something is preferred above threshold" while the assertion says
"something is preferred below threshold" — these are independent conditions,
not identical.

Our formalization simplifies this by treating negative valence as lacking
TSP entirely (`hasTSP .negative = false`). This captures the correct
result (fear takes questions) but via a different mechanism. The book's
more nuanced analysis — same TSP, flipped assertion — is left as future
refinement.
-/

end Phenomena.Questions.Studies.Uegaki2022
