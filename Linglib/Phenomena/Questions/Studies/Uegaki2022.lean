import Linglib.Theories.Semantics.Attitudes.CDistributivity
import Linglib.Theories.Semantics.Attitudes.EmbeddingConstraints
import Linglib.Theories.Semantics.Attitudes.Preferential
import Linglib.Theories.Interfaces.SyntaxSemantics.LeftPeriphery

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
- `CDistributivity.lean`: C-distributivity definition and proofs
- `EmbeddingConstraints.lean`: P-to-Q Entailment, Strawson C-dist,
  Veridical Uniformity, fictitious predicates
- `Preferential.lean`: NVP classification, TSP, highlighting, triviality theorems
- `LeftPeriphery.lean`: SelectionClass derivation
-/

namespace Phenomena.Questions.Studies.Uegaki2022

open Semantics.Attitudes.CDistributivity
open Semantics.Attitudes.EmbeddingConstraints
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

/-- A C-distributive `PreferentialPredicate` satisfies P-to-Q Entailment
    (for any fixed comparison class C).

    This closes the end-to-end chain for Class 2 and Class 3 NVPs:
    `attitude → isCDistributive → IsPtoQEntailing`.
    Class 1 NVPs (non-C-distributive) require individual P-to-Q proofs
    (e.g., `wonder_satisfies_ptoq`, `daroo_satisfies_ptoq`, `care_satisfies_ptoq`). -/
theorem preferential_cDist_implies_ptoq {W E : Type*}
    (V : Semantics.Attitudes.Preferential.PreferentialPredicate W E)
    (hCD : V.isCDistributive)
    (C : QuestionDen W) :
    IsPtoQEntailing (fun x Q (_w : W) => V.questionSemantics x Q C) := by
  intro x Q w p hp hSingleton
  have ⟨q, hq_mem, hq_holds⟩ := (hCD x [p] C w).mp hSingleton
  simp only [List.mem_singleton] at hq_mem
  exact (hCD x Q C w).mpr ⟨p, hp, hq_mem ▸ hq_holds⟩

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
| Veridical Uniformity     | ✓       | ✓          | ✗    | ✓       | ✓     | NA     | ✗       |
| C-distributivity         | ✓       | ✓          | ✗    | ✗       | ✗     | ✗      | ✗       |
| Strawson C-distributivity| ✓       | ✓          | ✓    | ✗       | ✗     | ✗      | ✗       |
| P-to-Q Entailment        | ✓       | ✓          | ✓    | ✓       | ✓     | ✓      | ✗       |

P-to-Q Entailment correctly rules out only `magtaka` among attested predicates,
while ruling out all three fictitious predicates (*shknow, *knopinion).
C-distributivity over-rules-out care, mõtlema, daroo, wonder.
-/

/-- Cross-linguistic embedding datum from @cite{uegaki-2022} Table 8.2.

Fields `satisfiesVU`, `satisfiesCDist`, `satisfiesStrawsonCDist`, `satisfiesPtoQ`
encode whether the predicate **satisfies** each constraint (not whether the
constraint makes a correct prediction). This aligns with the theory-level
definitions (`IsPtoQEntailing`, `IsCDistributive`, etc.) — e.g.,
`shknow_violates_ptoq` proves *shknow does NOT satisfy P-to-Q Entailment,
so `satisfiesPtoQ = false` for *shknow.

The paper's ✓/✗ table encodes "correct prediction" — a different concept.
For attested predicates, correct prediction = satisfies. For fictitious
predicates, correct prediction = violates (the constraint correctly rules
them out). Use `correctPrediction` to derive the paper's table. -/
structure CrossLingDatum where
  predicate : String
  language : String
  takesDecl : Bool
  takesInterrog : Bool
  satisfiesVU : Bool           -- satisfies Veridical Uniformity
  satisfiesCDist : Bool        -- satisfies C-distributivity
  satisfiesStrawsonCDist : Bool -- satisfies Strawson C-distributivity
  satisfiesPtoQ : Bool         -- satisfies P-to-Q Entailment
  attested : Bool              -- false for fictitious predicates
  deriving Repr, BEq

/-- Does a constraint make a correct prediction about this predicate?

For attested predicates: correct iff the predicate satisfies the constraint
(the constraint allows an actually-existing predicate).
For fictitious predicates: correct iff the predicate violates the constraint
(the constraint rules out a non-existent predicate). -/
def CrossLingDatum.correctPrediction (d : CrossLingDatum) (satisfies : Bool) : Bool :=
  if d.attested then satisfies else !satisfies

/-- Full Table 8.2 data from @cite{uegaki-2022}, including fictitious predicates.

Values use "satisfies" semantics:
- *shknow, *knopinion: violate ALL four constraints (all false)
- wonder: VU is NA in the paper (VU applies to responsive predicates;
  wonder is rogative). Encoded as `satisfiesVU = true` because
  `IsVeridicallyUniform` is vacuously satisfied: both `IsVeridicalDecl`
  and `IsVeridicalInterrog` hold vacuously when ⟦wonder⟧({p}↓)(x) is
  always false, making the biconditional trivially true. -/
def table8_2 : List CrossLingDatum := [
  -- Fictitious (unattested): violate all constraints
  ⟨"*shknow",   "—",        true, true, false, false, false, false, false⟩,
  ⟨"*knopinion","—",        true, true, false, false, false, false, false⟩,
  -- Attested
  ⟨"care",      "English",  true, true, false, false, true,  true,  true⟩,
  ⟨"mõtlema",   "Estonian", true, true, true,  false, false, true,  true⟩,
  ⟨"daroo",     "Japanese", true, true, true,  false, false, true,  true⟩,
  ⟨"wonder",    "English",  false,true, true,  false, false, true,  true⟩,
  ⟨"magtaka",   "Tagalog",  true, true, false, false, false, false, true⟩
]

/-- C-distributivity implies P-to-Q Entailment across all table predicates. -/
theorem cdist_implies_ptoq_empirical :
    table8_2.all (fun d => !d.satisfiesCDist || d.satisfiesPtoQ) = true := by
  native_decide

/-- P-to-Q Entailment is strictly weaker: some attested predicates satisfy P-to-Q
    but not C-distributivity (care, mõtlema, daroo, wonder). -/
theorem ptoq_strictly_weaker :
    (table8_2.filter (fun d =>
      d.attested && d.satisfiesPtoQ && !d.satisfiesCDist)).length > 0 := by
  native_decide

/-- C-distributivity implies Strawson C-distributivity across all table predicates. -/
theorem cdist_implies_strawson_empirical :
    table8_2.all (fun d => !d.satisfiesCDist || d.satisfiesStrawsonCDist) = true := by
  native_decide

/-- All unattested predicates violate P-to-Q Entailment — the constraint
    correctly rules out every fictitious predicate in the table. -/
theorem ptoq_rules_out_all_fictitious :
    table8_2.all (fun d => d.attested || !d.satisfiesPtoQ) = true := by
  native_decide

/-- P-to-Q Entailment allows more attested predicates than C-distributivity. -/
theorem ptoq_more_permissive_than_cdist :
    (table8_2.filter (fun d => d.attested && d.satisfiesPtoQ)).length >
    (table8_2.filter (fun d => d.attested && d.satisfiesCDist)).length := by
  native_decide

/-- P-to-Q makes correct predictions for all predicates except magtaka. -/
theorem ptoq_correct_predictions :
    (table8_2.filter (fun d =>
      d.correctPrediction d.satisfiesPtoQ)).length = 6 := by
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

open Interfaces.SyntaxSemantics.LeftPeriphery

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
NVPClass↔SelectionClass bridge (approximate): the question-oriented theory's
NVP classification partially aligns with the Left Periphery's SelectionClass.

- Class 3 (anti-rogative) → uninterrogative: correct (both predict no interrog)
- Class 2 (C-dist + negative) → responsive: correct (fear, dread take both)
- Class 1 (non-C-dist) → responsive: **approximate** — correct for worry and care
  (which take both decl + interrog), but **incorrect for wonder and daroo**, which
  are better classified as `.rogativePerspP`. The issue is that `.responsive`
  in the Left Periphery entails factivity/knowledge, which wonder and daroo lack.

This mapping is lossy because NVPClass captures C-dist × valence while
SelectionClass captures syntactic selection of left-peripheral layers —
orthogonal dimensions that don't reduce to each other.
-/
def nvpToSelectionClass : NVPClass → SelectionClass
  | .class3_cDist_positive => .uninterrogative
  | .class1_nonCDist => .responsive  -- approximate: correct for worry/care
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

/-!
### SelectionClass ↔ P-to-Q Bridge

The Left Periphery's `SelectionClass` taxonomy (syntactic selection) and the
question-oriented theory's P-to-Q Entailment (semantic constraint) are
consistent: every `SelectionClass` that admits interrogative embedding is
associated with a semantic structure that satisfies P-to-Q.

- `rogativePerspP` (wonder): P-to-Q via vacuous singleton (`wonder_satisfies_ptoq`)
- `responsive` (know, care): P-to-Q via C-distributivity (`cDistributive_implies_ptoq`)
  or relevance semantics
- `rogativeCP` (investigate): P-to-Q via existential semantics
- `rogativeSAP` (ask): P-to-Q via speech-act semantics

### Theoretical Gap: daroo

The `nvpToSelectionClass` bridge maps Class 1 (non-C-distributive, takes questions)
to `.responsive`. But `.responsive` in the Left Periphery sense requires factivity
and knowledge entailment — properties daroo lacks. Daroo's behavior is better
captured as `.rogativePerspP` (perspective-layer selection) with an extended
semantics that drops the ignorance component. This suggests the SelectionClass
taxonomy needs a finer-grained distinction within PerspP-selecting predicates:
those with ignorance (wonder) vs without (daroo).
-/

/-- P-to-Q Entailment is satisfied by all attested interrogative-embedding
    predicates in Table 8.2 except magtaka (Tagalog), which is the sole
    counterexample — motivating the search for a still-weaker constraint. -/
theorem ptoq_one_exception :
    (table8_2.filter (fun d =>
      d.attested && d.takesInterrog && !d.satisfiesPtoQ)).map (·.predicate)
    = ["magtaka"] := by
  native_decide

/-- The SelectionClass taxonomy is consistent with P-to-Q: for each
    interrogative-embedding SelectionClass, at least one attested predicate
    in Table 8.2 demonstrates P-to-Q satisfaction.

    - rogativePerspP: wonder satisfies P-to-Q (vacuous singleton)
    - responsive: care, daroo, mõtlema all satisfy P-to-Q -/
theorem selectionClass_ptoq_witnesses :
    -- rogativePerspP example: wonder
    (table8_2.any (fun d => d.predicate == "wonder" && d.satisfiesPtoQ)) = true ∧
    -- responsive examples: care, daroo, mõtlema
    (table8_2.any (fun d => d.predicate == "care" && d.satisfiesPtoQ)) = true ∧
    (table8_2.any (fun d => d.predicate == "daroo" && d.satisfiesPtoQ)) = true ∧
    (table8_2.any (fun d => d.predicate == "mõtlema" && d.satisfiesPtoQ)) = true := by
  native_decide

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
