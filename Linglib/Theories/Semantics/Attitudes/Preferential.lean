/-
# Preferential Attitude Semantics

Degree-based semantics for preferential attitude verbs like `hope`, `fear`,
`worry`, `wish`, `expect`, following @cite{villalta-2008} and @cite{romero-2015-salt}.

## Semantic Mechanism

Unlike doxastic attitudes (which use accessibility relations), preferential
attitudes use **degree comparison**:

⟦x hopes p⟧(w, C) = μ_hope(x, p) > θ_hope(C)

Where:
- μ_hope : Entity → Prop → Degree (preference function)
- θ_hope : ComparisonClass → Degree (contextual threshold)
- C : the comparison class of propositions

## Key Properties

1. **C-distributivity**: Does `x V Q` ⟺ `∃p ∈ Q. x V p`?
2. **Valence**: Evaluatively positive (hope) vs. negative (fear)
3. **TSP**: Threshold Significance Presupposition

## Architecture: C-Distributivity as Provable Property

C-distributivity is NOT stipulated — it must be PROVED for each predicate
from the structure of its semantics. Each predicate defines:
- `propSemantics`: how it combines with propositions
- `questionSemantics`: how it combines with questions

Then `IsCDistributive propSemantics questionSemantics` is a theorem.

## NVP Classification

| Class | C-dist | Valence | TSP | Takes Q? | Examples |
|-------|--------|---------|-----|----------|----------|
| 1 | ✗ | any | any | ✓ | worry, qidai, tanosimi |
| 2 | ✓ | negative | ✗ | ✓ | fear, osore, kork- |
| 3 | ✓ | positive | ✓ | ✗ | hope, wish, expect |

-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic
import Linglib.Core.Lexical.VerbClass
import Linglib.Theories.Semantics.Attitudes.CDistributivity
import Linglib.Theories.Semantics.Attitudes.Doxastic

namespace Semantics.Attitudes.Preferential

open Core.Verbs (AttitudeValence)
export Core.Verbs (AttitudeValence)
open Semantics.Attitudes.CDistributivity (IsCDistributive degreeComparison_isCDistributive
                      degreeComparisonProp degreeComparisonQuestion DegreeFn ThresholdFn)

-- Re-export types under more descriptive names for downstream use

/-- Question denotation: set of possible answers. Re-exported from `CDistributivity`. -/
abbrev AlternativeList (W : Type*) := Semantics.Attitudes.CDistributivity.AlternativeList W

/-- Preference function: μ(agent, prop) → degree. Alias for `DegreeFn`. -/
abbrev PreferenceFunction (W E : Type*) := DegreeFn W E

/-- Threshold function: θ(comparison_class) → degree. Alias for `ThresholdFn`. -/
abbrev ThresholdFunction (W : Type*) := ThresholdFn W

-- Connection to Question Semantics

/-!
## Grounding in Question Semantics
@cite{uegaki-sudo-2019} @cite{villalta-2008} @cite{rooth-1992} @cite{qing-uegaki-2025}

Questions are **alternative sets**. Our `AlternativeList W` is the
extensional, list-based representation of question denotations used by
the C-distributivity machinery (still Bool-shaped pending a follow-up
migration of `Semantics.Attitudes.CDistributivity` to substrate-aligned
Set propositions).

### Why This Matters for TSP

@cite{uegaki-sudo-2019} derive TSP from the interaction of:
1. Degree semantics (μ(x,p) > θ) — from @cite{villalta-2008}
2. Alternative semantics (questions as Hamblin sets) — from @cite{hamblin-1973b}
3. Focus-induced presuppositions — from @cite{rooth-1992}

The key insight: **questions introduce alternatives**, and combining a degree
predicate with alternatives triggers significance presuppositions.

### The Derivation Chain

```
Hamblin alternative set Q = {p₁, p₂,...} [@cite{hamblin-1973b}]
        ↓
Alternatives trigger focus semantics [@cite{rooth-1992}]
        ↓
Focus triggers significance presup [@cite{kennedy-2007}]
        ↓
For positive valence: significance = ∃p ∈ C. μ(x,p) > θ = TSP
```

### Rooth Integration (see `Focus/Sensitivity.lean`)

The compositional chain from focus marking to TSP is now explicit:

- `Focus/Interpretation.lean`: `FocusResolution` bundles ~'s two constraints
  (C ⊆ ⟦α⟧f, ⟦α⟧o ∈ C)
- `Focus/Sensitivity.lean`: `focusSignificance` derives the significance
  presupposition from a degree predicate + FocusResolution;
  `tsp_from_focus` proves significance = TSP for positive valence;
  `assertion_entails_tsp` shows TSP is entailed by the assertion
  (because ⟦α⟧o ∈ C guarantees a witness)
-/

/--
Key semantic operations are equivalent across representations.

The existential quantification `∃p ∈ Q. φ(p)` that appears in:
- C-distributivity: `V x Q C ↔ ∃p ∈ Q. V x p C`
- TSP: `∃p ∈ C. μ(x,p) > θ(C)`

works identically on List (via `List.any`) and Hamblin (via function application
to the characteristic function of answers satisfying φ).
-/
theorem exists_equiv_any {W : Type*} (Q : AlternativeList W) (φ : (W → Bool) → Bool) :
    (∃ p ∈ Q, φ p = true) ↔ (Q.any φ = true) := by
  simp only [List.any_eq_true]

/--
Subset relations are preserved.

`Q ⊆ C` (all answers to Q are in comparison class C) is the same whether
we use List containment or Hamblin entailment.
-/
def questionSubset {W : Type*} (Q C : AlternativeList W) : Prop :=
  ∀ p ∈ Q, p ∈ C

/--
The triviality condition uses subset + existential, both of which are
representation-independent for finite cases.
-/
theorem triviality_representation_independent {W : Type*}
    (Q C : AlternativeList W) (φ : (W → Bool) → Bool)
    (h_subset : questionSubset Q C)
    (h_exists_Q : Q.any φ = true) :
    C.any φ = true := by
  simp only [List.any_eq_true] at *
  obtain ⟨p, hp_in_Q, hp_holds⟩ := h_exists_Q
  exact ⟨p, h_subset p hp_in_Q, hp_holds⟩

-- Significance Presuppositions (@cite{kennedy-2007}, @cite{uegaki-sudo-2019})

/-!
## Deriving TSP from Degree Semantics

### Background: Significance in Degree Constructions

@cite{kennedy-2007} observes that degree constructions carry **significance presuppositions**.
The positive form of a gradable adjective presupposes the scale is "significant" in context:

  "John is tall" presupposes height is relevant/significant

### Application to Preferential Predicates

@cite{villalta-2008} shows preferential predicates ARE gradable predicates with degree semantics:

  ⟦x hopes p⟧ = μ_hope(x, p) > θ(C)

As degree constructions, they inherit significance presuppositions. But the CONTENT
of "significance" differs by valence:

### Positive Valence (hope, wish, expect)

For predicates expressing desires/goals:
- Significance = "there exists something the agent desires"
- Presupposition: ∃p ∈ C. μ(x, p) > θ(C)
- This IS the Threshold Significance Presupposition (TSP)

### Negative Valence (fear, dread)

For predicates expressing aversions/threats:
- Significance = "there exists something the agent wants to avoid"
- But this is NOT symmetric with TSP!
- You can identify threats without presupposing a positive desire
- The presupposition is about threat-identification, not desire-existence

### Why the Asymmetry?

The key insight (@cite{uegaki-sudo-2019}): Positive predicates express **bouletic goals** — states
the agent wants to achieve. Goals inherently presuppose there's something desirable.

Negative predicates express **threats** — states to avoid. Threats don't require
a symmetric positive goal. "I fear the worst" doesn't presuppose "I desire something."

### Consequence for Anti-Rogativity

Only TSP (positive significance) creates triviality with questions:
- Assertion: ∃p ∈ Q. μ(x,p) > θ(C)
- TSP: ∃p ∈ C. μ(x,p) > θ(C)
- When Q ⊆ C: Assertion ⊆ TSP → trivial!

Negative predicates lack TSP, so no triviality, so they CAN take questions.

-/

/--
Significance presupposition content varies by valence.

This captures the insight that ALL degree predicates have significance
presuppositions, but the content differs:
- Positive: presupposes desired alternative exists (= TSP)
- Negative: presupposes threat identified (weaker, different structure)
-/
inductive SignificanceContent where
  /-- Positive: ∃p ∈ C. μ(x,p) > θ — "something is desired" (= TSP) -/
  | desiredExists
  /-- Negative: threat identification — no symmetric existence presupposition -/
  | threatIdentified
  deriving DecidableEq, Repr

/--
Derive significance content from valence.

This is the key derivation: TSP is not stipulated, it FOLLOWS from
positive valence + degree semantics.
-/
def significanceFromValence (valence : AttitudeValence) : SignificanceContent :=
  match valence with
  | .positive => .desiredExists    -- Bouletic goals → TSP
  | .negative => .threatIdentified -- Threats → no TSP

/--
Does this significance content yield TSP?

TSP = presupposition that ∃p ∈ C. μ(x,p) > θ(C).
Only `desiredExists` has this form.
-/
def SignificanceContent.yieldsTSP : SignificanceContent → Bool
  | .desiredExists => true
  | .threatIdentified => false

/--
TSP distribution DERIVED from valence via significance presuppositions.

This theorem shows TSP is not stipulated — it follows from:
1. Degree predicates have significance presuppositions (Kennedy)
2. Significance content depends on valence (bouletic goals vs threats)
3. Only positive valence yields TSP-type significance
-/
def hasTSP (valence : AttitudeValence) : Bool :=
  (significanceFromValence valence).yieldsTSP

/-- Positive predicates have TSP. -/
theorem positive_hasTSP : hasTSP .positive = true := rfl

/-- Negative predicates lack TSP. -/
theorem negative_lacks_TSP : hasTSP .negative = false := rfl

/-- Check if TSP is satisfied for given parameters -/
def tspSatisfied {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (agent : E) (C : AlternativeList W) : Bool :=
  C.any λ p => μ agent p > θ C

/--
The significance presupposition for a degree predicate.

For positive valence, this is exactly TSP.
For negative valence, this is the weaker threat-identification condition.
-/
def significancePresupSatisfied {W E : Type*}
    (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (agent : E) (C : AlternativeList W) : Bool :=
  match significanceFromValence valence with
  | .desiredExists => tspSatisfied μ θ agent C  -- ∃p. μ(x,p) > θ
  | .threatIdentified => true  -- Weaker: just requires threat context

-- Preferential Predicate Structure

/--
A preferential attitude predicate with explicit semantics.

Each predicate defines:
- `propSemantics`: ⟦x V p⟧(w, C)
- `questionSemantics`: ⟦x V Q⟧(w, C)

C-distributivity is then a PROVABLE property, not a stipulated field.
-/
structure PreferentialPredicate (W E : Type*) where
  /-- Name of the predicate -/
  name : String
  /-- Is the predicate veridical? (NVPs are non-veridical by definition) -/
  veridical : Bool := false
  /-- Evaluative valence (positive/negative) -/
  valence : AttitudeValence
  /-- Preference function μ -/
  μ : PreferenceFunction W E
  /-- Threshold function θ -/
  θ : ThresholdFunction W
  /-- Propositional semantics: ⟦x V p⟧(C) -/
  propSemantics : E → (W → Bool) → AlternativeList W → Bool
  /-- Question semantics: ⟦x V Q⟧(C) -/
  questionSemantics : E → AlternativeList W → AlternativeList W → Bool

/-- Does the predicate have TSP? Derived from valence. -/
def PreferentialPredicate.hasTSP {W E : Type*}
    (V : PreferentialPredicate W E) : Bool :=
  Preferential.hasTSP V.valence

-- C-Distributivity: A Provable Property

/--
C-distributivity is a PROPERTY of a predicate's semantics, not a field.

A predicate V is C-distributive iff:
  ∀ x Q C, V.questionSemantics x Q C ↔ ∃p ∈ Q, V.propSemantics x p C

This must be PROVED for each predicate from its semantic definition.
-/
def PreferentialPredicate.isCDistributive {W E : Type*}
    (V : PreferentialPredicate W E) : Prop :=
  ∀ (x : E) (Q C : AlternativeList W) (_w : W),
    V.questionSemantics x Q C = true ↔
    ∃ p ∈ Q, V.propSemantics x p C = true

/-- Boolean version for computation -/
def PreferentialPredicate.cDistributive {W E : Type*}
    (V : PreferentialPredicate W E) (x : E) (Q C : AlternativeList W) : Bool :=
  V.questionSemantics x Q C == Q.any (λ p => V.propSemantics x p C)

-- Degree-Comparison Predicates (hope, fear, expect, wish)

/--
Build a degree-comparison predicate.

These have semantics:
- ⟦x V p⟧(C) = μ(x, p) > θ(C)
- ⟦x V Q⟧(C) = ∃p ∈ Q. μ(x, p) > θ(C)

C-distributivity follows AUTOMATICALLY from this structure.
-/
def mkDegreeComparisonPredicate {W E : Type*}
    (name : String) (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  { name := name
  , veridical := false
  , valence := valence
  , μ := μ
  , θ := θ
  , propSemantics := λ x p C => decide (μ x p > θ C)
  , questionSemantics := λ x Q C => Q.any λ p => decide (μ x p > θ C)
  }

/--
**Theorem**: Degree-comparison predicates are C-distributive.

This is PROVED, not stipulated. The proof follows from the structure
of the semantics: questionSemantics IS the existential over propSemantics.
-/
theorem degreeComparisonPredicate_isCDistributive {W E : Type*}
    (name : String) (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    (mkDegreeComparisonPredicate name valence μ θ).isCDistributive := by
  intro x Q C w
  simp only [mkDegreeComparisonPredicate, List.any_eq_true]

-- Standard Predicates with C-Distributivity Proofs

/-- Hope (preferential component): degree-comparison, positive valence.
This captures the preference ordering from @cite{villalta-2008} — the
component shared by all emotive doxastic analyses. For the full emotive
doxastic semantics with doxastic + uncertainty + preference components
(@cite{anand-hacquard-2013}), see `hopeHybrid` below.

Note: `hope` is structurally identical to `want` except for the name —
both are positive-valence degree-comparison predicates. What distinguishes
hope from want linguistically is the *additional* doxastic component
(uncertainty condition, epistemic licensing) that `hopeHybrid` captures. -/
def hope {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkDegreeComparisonPredicate "hope" .positive μ θ

/-- Hope is C-distributive (PROVED from its semantics) -/
theorem hope_isCDistributive {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    (hope μ θ).isCDistributive :=
  degreeComparisonPredicate_isCDistributive "hope" .positive μ θ

/-- Fear (preferential component): degree-comparison, negative valence.
Captures the preference ordering only. For the full emotive doxastic
semantics with uncertainty condition, see `fearHybrid` below. -/
def fear {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkDegreeComparisonPredicate "fear" .negative μ θ

/-- Fear is C-distributive (PROVED from its semantics) -/
theorem fear_isCDistributive {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    (fear μ θ).isCDistributive :=
  degreeComparisonPredicate_isCDistributive "fear" .negative μ θ

/-- Expect: degree-comparison, positive valence -/
def expect {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkDegreeComparisonPredicate "expect" .positive μ θ

/-- Expect is C-distributive -/
theorem expect_isCDistributive {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    (expect μ θ).isCDistributive :=
  degreeComparisonPredicate_isCDistributive "expect" .positive μ θ

/-- Wish: degree-comparison, positive valence -/
def wish {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkDegreeComparisonPredicate "wish" .positive μ θ

/-- Wish is C-distributive -/
theorem wish_isCDistributive {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    (wish μ θ).isCDistributive :=
  degreeComparisonPredicate_isCDistributive "wish" .positive μ θ

/-- Dread: degree-comparison, negative valence -/
def dread {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkDegreeComparisonPredicate "dread" .negative μ θ

/-- Dread is C-distributive -/
theorem dread_isCDistributive {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    (dread μ θ).isCDistributive :=
  degreeComparisonPredicate_isCDistributive "dread" .negative μ θ

/-- Hope and wish have identical preference semantics — they differ only
in name. @cite{anand-hacquard-2013}: what distinguishes hope from
want/wish is the doxastic component (captured by `hopeHybrid`), not
the preferential semantics. -/
theorem hope_eq_wish_semantics {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    (hope μ θ).propSemantics = (wish μ θ).propSemantics ∧
    (hope μ θ).questionSemantics = (wish μ θ).questionSemantics := by
  constructor <;> rfl

-- Non-C-Distributive Predicates (worry, qidai)

/--
Worry has DIFFERENT question semantics involving global uncertainty.

⟦x worries about Q⟧ ≠ ∃p ∈ Q. ⟦x worries about p⟧

The question semantics involves uncertainty about WHICH answer is true,
not just whether some answer satisfies the predicate.
-/
def worry {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (isUncertain : E → AlternativeList W → Bool)  -- Epistemic uncertainty
    : PreferentialPredicate W E :=
  { name := "worry"
  , veridical := false
  , valence := .negative
  , μ := μ
  , θ := θ
  -- Propositional: degree comparison (like fear)
  , propSemantics := λ x p C => decide (μ x p > θ C)
  -- Question: GLOBAL uncertainty, not existential over prop semantics
  , questionSemantics := λ x Q C =>
      isUncertain x Q && Q.any (λ p => decide (μ x p > θ C))
  }

/--
Worry is NOT C-distributive when there's an uncertainty requirement.

The question semantics requires global uncertainty, which is NOT
reducible to existential quantification over propositional semantics.
-/
theorem worry_not_cDistributive {W E : Type*} [Inhabited W]
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (isUncertain : E → AlternativeList W → Bool)
    (x : E) (Q C : AlternativeList W)
    (h_uncertain_false : isUncertain x Q = false)
    (h_exists : ∃ p ∈ Q, decide (μ x p > θ C) = true) :
    ¬(worry μ θ isUncertain).isCDistributive := by
  intro h_cdist
  -- questionSemantics x Q C = false (because isUncertain = false)
  have h1 : (worry μ θ isUncertain).questionSemantics x Q C = false := by
    simp only [worry, h_uncertain_false, Bool.false_and]
  -- But if C-distributive, questionSemantics should ↔ ∃p ∈ Q. propSemantics
  -- And propSemantics x p C = decide (μ x p > θ C), so h_exists gives us a witness
  have h2 : ∃ p ∈ Q, (worry μ θ isUncertain).propSemantics x p C = true := by
    simp only [worry]
    exact h_exists
  -- So by C-distributivity, questionSemantics should be true
  have h3 := (h_cdist x Q C default).mpr h2
  -- Contradiction: h1 says false, h3 says true
  rw [h1] at h3
  exact Bool.false_ne_true h3

/--
Mandarin "qidai" (look forward to): positive but non-C-distributive.

Like worry, it involves anticipation of RESOLUTION, not just existential
over individual propositions.
-/
def qidai {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (anticipatesResolution : E → AlternativeList W → Bool)
    : PreferentialPredicate W E :=
  { name := "qidai"
  , veridical := false
  , valence := .positive
  , μ := μ
  , θ := θ
  , propSemantics := λ x p C => decide (μ x p > θ C)
  -- Question semantics involves resolution anticipation
  , questionSemantics := λ x Q C =>
      anticipatesResolution x Q && Q.any (λ p => decide (μ x p > θ C))
  }

-- NVP Classification

/--
The three classes of Non-Veridical Preferential predicates.
-/
inductive NVPClass where
  | class1_nonCDist       -- Non-C-distributive: worry, qidai, tanosimi
  | class2_cDist_negative -- C-distributive + negative: fear, dread
  | class3_cDist_positive -- C-distributive + positive: hope, wish, expect
  deriving DecidableEq, Repr

/--
Classify an NVP. Note: this now requires knowing whether the predicate
is C-distributive, which must be PROVED separately.
-/
def classifyNVP (cDistributive : Bool) (valence : AttitudeValence) : NVPClass :=
  if !cDistributive then .class1_nonCDist
  else if valence == .negative then .class2_cDist_negative
  else .class3_cDist_positive

/-- Can this NVP class take questions canonically? -/
def NVPClass.canTakeQuestion : NVPClass → Bool
  | .class1_nonCDist => true       -- No triviality
  | .class2_cDist_negative => true -- No TSP, so no triviality
  | .class3_cDist_positive => false -- Triviality

-- Triviality for Class 3

/--
Class 3 triviality for degree-comparison predicates specifically.

Class 3 predicates (C-distributive + positive + TSP) yield trivial meanings
when combined with questions. When Q ⊆ C:
- Assertion: ∃p ∈ Q. μ(x,p) > θ(C)
- Presupposition (TSP): ∃p ∈ C. μ(x,p) > θ(C)
- Assertion ⊆ Presupposition → trivial!

For predicates built with `mkDegreeComparisonPredicate`, we can prove
that assertion implies presupposition when Q ⊆ C.
-/
theorem degreeComparison_triviality {W E : Type*}
    (name : String) (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W)
    (h_subset : ∀ p, p ∈ Q → p ∈ C)
    (h_assert : (mkDegreeComparisonPredicate name valence μ θ).questionSemantics x Q C = true) :
    tspSatisfied μ θ x C = true := by
  unfold mkDegreeComparisonPredicate at h_assert
  unfold tspSatisfied
  simp only [List.any_eq_true, decide_eq_true_eq] at *
  obtain ⟨p, hp_in_Q, hp_holds⟩ := h_assert
  exact ⟨p, h_subset p hp_in_Q, hp_holds⟩

/-- Hope + question yields trivial meaning when Q ⊆ C -/
theorem hope_triviality {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W)
    (h_subset : ∀ p, p ∈ Q → p ∈ C)
    (h_assert : (hope μ θ).questionSemantics x Q C = true) :
    tspSatisfied μ θ x C = true :=
  degreeComparison_triviality "hope" .positive μ θ x Q C h_subset h_assert

/--
**Reverse direction**: TSP → assertion when C ⊆ Q.

This is the other half of the triviality argument from @cite{uegaki-2022} §6.5.4:
TSP says ∃p ∈ C. μ(x,p) > θ(C). When C ⊆ Q, this p is also in Q,
so the assertion ∃p ∈ Q. μ(x,p) > θ(C) holds too.
-/
theorem hope_triviality_reverse {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W)
    (h_subset : ∀ p, p ∈ C → p ∈ Q)
    (h_tsp : tspSatisfied μ θ x C = true) :
    (hope μ θ).questionSemantics x Q C = true := by
  unfold tspSatisfied at h_tsp
  unfold hope mkDegreeComparisonPredicate
  simp only [List.any_eq_true, decide_eq_true_eq] at *
  obtain ⟨p, hp_in_C, hp_holds⟩ := h_tsp
  exact ⟨p, h_subset p hp_in_C, hp_holds⟩

/--
**Triviality identity**: When C = Q, assertion ↔ TSP.

This is the core of @cite{uegaki-2022} §6.5.4: the assertion of a non-veridical
preferential with an interrogative complement is **identical** to its
presupposition (TSP). Whenever TSP is satisfied (defined), the assertion
is true; whenever TSP fails, the assertion is false. The meaning is
L-analytic — its truth value is determined entirely by the presupposition,
leaving no informative content. This is what @cite{gajewski-2002} identifies
as the trigger for unacceptability.
-/
theorem hope_triviality_identity {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q : AlternativeList W) :
    (hope μ θ).questionSemantics x Q Q = tspSatisfied μ θ x Q := by
  simp only [hope, mkDegreeComparisonPredicate, tspSatisfied]

-- Classification Verification

/-- Hope is Class 3 (anti-rogative) -/
example : classifyNVP true .positive = .class3_cDist_positive := rfl

/-- Fear is Class 2 (takes questions) -/
example : classifyNVP true .negative = .class2_cDist_negative := rfl

/-- Worry is Class 1 (non-C-distributive, takes questions) -/
example : classifyNVP false .negative = .class1_nonCDist := rfl

/-- Qidai is Class 1 (positive but non-C-distributive, takes questions) -/
example : classifyNVP false .positive = .class1_nonCDist := rfl

-- Veridical Preferential Predicates (@cite{uegaki-sudo-2019})

/-!
## Veridical vs Non-Veridical Preferential Predicates

@cite{uegaki-sudo-2019} established a crucial distinction:

### Non-Veridical (hope) - TRIVIAL
```
Presup (TSP): ∃p ∈ C. μ(x,p) > θ(C)
Assertion: ∃p ∈ Q. μ(x,p) > θ(C)
When Q ⊆ C: Assertion ⊆ TSP → TRIVIAL
```

### Veridical (be happy) - NOT TRIVIAL
```
Presup: ∃p ∈ Q. p(w) ∧ μ(x,p) > θ(C)
Assertion: ∃p ∈ Q. p(w) ∧ μ(x,p) > θ(C)
                       ^^^^
                       TRUTH REQUIREMENT breaks triviality!
```

Even when Q ⊆ C, whether the assertion is true depends on WHICH answer p
is TRUE in the actual world w. This is the key insight: veridicality
breaks triviality because it adds a world-dependent constraint.

### The Deep Theorem (formalized below as `veridical_breaks_triviality`)

Triviality requires ALL THREE conditions:
1. C-distributive
2. Positive valence (TSP)
3. **Non-veridical**

If ANY condition fails, the predicate can embed questions:
- Non-C-dist → Class 1 (takes questions)
- Negative valence → Class 2 (no TSP, takes questions)
- **Veridical → Responsive** (truth requirement breaks triviality)

### Examples

| Predicate | Veridical | C-Dist | Valence | TSP | Takes Q? | Why |
|-----------|-----------|--------|---------|-----|----------|-----|
| hope | ✗ | ✓ | + | ✓ | ✗ | C-dist + TSP → trivial |
| fear | ✗ | ✓ | - | ✗ | ✓ | No TSP |
| worry | ✗ | ✗ | - | ✗ | ✓ | Non-C-dist |
| be happy | ✓ | ✓ | + | ✓ | ✓ | Veridical breaks triviality! |
| be surprised | ✓ | ✓ | + | ✓ | ✓ | Veridical breaks triviality! |
-/

/--
Build a veridical preferential predicate.

Unlike non-veridical predicates, veridical ones require the complement
proposition to be TRUE in the actual world:

⟦x is happy that p⟧(w, C) = p(w) ∧ μ(x, p) > θ(C)
⟦x is happy about Q⟧(w, C) = ∃p ∈ Q. p(w) ∧ μ(x, p) > θ(C)

The truth requirement p(w) is what breaks triviality: even if TSP holds
(some proposition is preferred), the assertion may be false because
the TRUE answer in w might not be the preferred one.
-/
def mkVeridicalPreferential {W E : Type*}
    (name : String) (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  { name := name
  , veridical := true  -- Veridical (unlike non-veridical preferentials)
  , valence := valence
  , μ := μ
  , θ := θ
  -- Propositional: requires p(w) = true (veridical requirement)
  -- Note: We return a function W → Bool to enable world-sensitivity
  , propSemantics := λ x p C => decide (μ x p > θ C)
  -- Question: ∃p ∈ Q. μ(x,p) > θ(C)
  -- The world-sensitivity is handled at usage site via propSemanticsAt
  , questionSemantics := λ x Q C => Q.any λ p => decide (μ x p > θ C)
  }

/--
World-sensitive propositional semantics for veridical predicates.

⟦x V p⟧(w, C) = p(w) ∧ μ(x, p) > θ(C)

The truth requirement p(w) is what distinguishes veridical from non-veridical.
-/
def PreferentialPredicate.propSemanticsAt {W E : Type*}
    (V : PreferentialPredicate W E) (x : E) (p : (W → Bool)) (C : AlternativeList W) (w : W) : Bool :=
  if V.veridical then
    p w && V.propSemantics x p C
  else
    V.propSemantics x p C

/--
World-sensitive question semantics for veridical predicates.

⟦x V Q⟧(w, C) = ∃p ∈ Q. p(w) ∧ μ(x, p) > θ(C)

For veridical predicates, the assertion requires some TRUE answer to be preferred.
-/
def PreferentialPredicate.questionSemanticsAt {W E : Type*}
    (V : PreferentialPredicate W E) (x : E) (Q C : AlternativeList W) (w : W) : Bool :=
  if V.veridical then
    Q.any λ p => p w && V.propSemantics x p C
  else
    V.questionSemantics x Q C

/--
**World-independence contrast**: Non-veridical predicates have world-independent
semantics (`questionSemanticsAt` ignores the world), while veridical predicates
have world-dependent semantics. This is the structural basis for L-analyticity:
for non-veridical predicates, assertion ⊆ presupposition holds at ALL worlds
because the world variable doesn't appear.
-/
theorem nonveridical_worldIndependent {W E : Type*}
    (name : String) (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W) (w₁ w₂ : W) :
    (mkDegreeComparisonPredicate name valence μ θ).questionSemanticsAt x Q C w₁ =
    (mkDegreeComparisonPredicate name valence μ θ).questionSemanticsAt x Q C w₂ := by
  simp [PreferentialPredicate.questionSemanticsAt, mkDegreeComparisonPredicate]

-- Veridical Predicate Instances

/-- "be happy": veridical, positive valence -/
def beHappy {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkVeridicalPreferential "be happy" .positive μ θ

/-- "be surprised": veridical, positive valence (expectation-violation).
    Classified as positive following @cite{uegaki-sudo-2019}: the degree
    function measures how much the true answer exceeds the subject's
    expectations, a positive-direction evaluation. -/
def beSurprised {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkVeridicalPreferential "be surprised" .positive μ θ

/-- "be glad": veridical, positive valence -/
def beGlad {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkVeridicalPreferential "be glad" .positive μ θ

/-- "be sad": veridical, negative valence -/
def beSad {W E : Type*} (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    PreferentialPredicate W E :=
  mkVeridicalPreferential "be sad" .negative μ θ

-- Veridical Breaks Triviality: The Core Theorem

/--
**Core Theorem**: Veridicality breaks triviality.

Even when:
- TSP holds (some proposition is preferred above threshold)
- Q ⊆ C (question answers are in comparison class)

The question assertion can still be FALSE for veridical predicates,
because no TRUE answer in w may be the preferred one.

This is the key insight from @cite{uegaki-sudo-2019}: non-veridicality
is a NECESSARY condition for the triviality that makes predicates
anti-rogative.

### Proof Strategy

We show that under the specified conditions:
1. TSP is satisfied (h_tsp)
2. But for every answer p in Q, if p is true in w, it's not preferred (h_no_true_preferred)
3. Therefore the question assertion is false

This proves that TSP satisfaction does NOT guarantee assertion truth
for veridical predicates — the triviality derivation fails!
-/
theorem veridical_breaks_triviality {W E : Type*}
    (name : String) (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W) (w : W)
    (_h_subset : ∀ p, p ∈ Q → p ∈ C)
    (_h_tsp : tspSatisfied μ θ x C = true)
    (h_no_true_preferred : ∀ p ∈ Q, p w = true → decide (μ x p > θ C) = false) :
    -- Even with TSP satisfied, the question assertion can be FALSE
    (mkVeridicalPreferential name valence μ θ).questionSemanticsAt x Q C w = false := by
  unfold PreferentialPredicate.questionSemanticsAt mkVeridicalPreferential
  simp only [↓reduceIte]
  rw [List.any_eq_false]
  intro p hp
  simp only [Bool.and_eq_true, not_and, decide_eq_true_eq]
  intro hp_true
  have := h_no_true_preferred p hp hp_true
  simp only [decide_eq_false_iff_not] at this
  exact this

/--
**Contrast Theorem**: Non-veridical predicates ARE trivial.

When TSP holds and Q ⊆ C, the assertion is ALWAYS true for non-veridical
C-distributive predicates. This is the triviality that makes them anti-rogative.

Combined with `veridical_breaks_triviality`, this shows the asymmetry:
- Non-veridical + C-dist + positive → trivial → anti-rogative
- Veridical + C-dist + positive → NOT trivial → responsive
-/
theorem nonveridical_is_trivial {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W)
    (h_subset : ∀ p, p ∈ Q → p ∈ C)
    (h_assert : (hope μ θ).questionSemantics x Q C = true) :
    tspSatisfied μ θ x C = true :=
  hope_triviality μ θ x Q C h_subset h_assert

-- C-Distributivity for Veridical Predicates

/--
Veridical predicates ARE C-distributive (at a given world).

The world-sensitive semantics preserves the existential structure:
⟦x V Q⟧(w, C) = ∃p ∈ Q. ⟦x V p⟧(w, C)

Note: This is C-distributivity for the world-sensitive semantics,
which is the relevant notion for veridical predicates.
-/
theorem veridicalPreferential_isCDistributiveAt {W E : Type*}
    (name : String) (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W) (w : W) :
    (mkVeridicalPreferential name valence μ θ).questionSemanticsAt x Q C w = true ↔
    ∃ p ∈ Q, (mkVeridicalPreferential name valence μ θ).propSemanticsAt x p C w = true := by
  simp only [PreferentialPredicate.questionSemanticsAt, PreferentialPredicate.propSemanticsAt,
             mkVeridicalPreferential, ↓reduceIte, List.any_eq_true]

/-- beHappy is C-distributive (at a given world) -/
theorem beHappy_isCDistributiveAt {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W) (w : W) :
    (beHappy μ θ).questionSemanticsAt x Q C w = true ↔
    ∃ p ∈ Q, (beHappy μ θ).propSemanticsAt x p C w = true :=
  veridicalPreferential_isCDistributiveAt "be happy" .positive μ θ x Q C w

/-- beSurprised is C-distributive (at a given world) -/
theorem beSurprised_isCDistributiveAt {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W) (w : W) :
    (beSurprised μ θ).questionSemanticsAt x Q C w = true ↔
    ∃ p ∈ Q, (beSurprised μ θ).propSemanticsAt x p C w = true :=
  veridicalPreferential_isCDistributiveAt "be surprised" .positive μ θ x Q C w

-- The Complete Picture: Why Veridicality Matters

/-!
## The Triviality Conditions (@cite{uegaki-sudo-2019})

For a preferential predicate to be anti-rogative (unable to embed questions),
ALL THREE conditions must hold:

1. **C-distributive**: ⟦x V Q⟧ ↔ ∃p ∈ Q. ⟦x V p⟧
2. **Positive valence**: Predicate has TSP (threshold significance presupposition)
3. **Non-veridical**: Truth of complement is NOT required

### Why Each Condition is Necessary

**If not C-distributive** (worry, qidai):
- Question semantics has additional structure (uncertainty, anticipation)
- Assertion ≠ ∃p ∈ Q. propSemantics, so triviality derivation fails
- Predicate CAN take questions (Class 1)

**If negative valence** (fear, dread):
- No TSP (threat-identification ≠ desire-existence)
- Assertion not entailed by any presupposition
- Predicate CAN take questions (Class 2)

**If veridical** (be happy, be surprised):
- Assertion: ∃p ∈ Q. p(w) ∧ μ(x,p) > θ(C)
- TSP: ∃p ∈ C. μ(x,p) > θ(C)
- TSP does NOT entail assertion (wrong p might be true in w)
- Predicate CAN take questions (Responsive)

### The Formalized Results

- `hope_triviality` / `nonveridical_is_trivial`: Non-veridical predicates
  with C-dist and positive valence yield trivial meanings (assertion ⊆ TSP)

- `veridical_breaks_triviality`: Even with TSP satisfied, veridical
  predicates can have false assertions (truth requirement adds constraint)

Together, these theorems prove that non-veridicality is NECESSARY for
the triviality derivation that creates anti-rogativity.
-/

-- Summary

/-!
## Main Results

### Proved Theorems (no axioms!):

1. `degreeComparisonPredicate_isCDistributive`: Any predicate built with
   `mkDegreeComparisonPredicate` is C-distributive. This follows from the
   semantic structure: questionSemantics = ∃p ∈ Q. propSemantics.

2. `hope_isCDistributive`, `fear_isCDistributive`, `expect_isCDistributive`,
   `wish_isCDistributive`, `dread_isCDistributive`: C-distributivity for
   standard degree-comparison predicates (derived from #1).

3. `worry_not_cDistributive`: Worry with uncertainty requirement is NOT
   C-distributive. Proved by contradiction: global uncertainty breaks
   the equivalence.

4. `degreeComparison_triviality` / `hope_triviality`: Class 3 predicates
   yield trivial meanings with questions (assertion ⊆ presupposition when Q ⊆ C).

5. **`veridical_breaks_triviality`** (NEW): The core @cite{uegaki-sudo-2019} insight —
   veridical predicates break triviality because even when TSP holds, the
   assertion can be false (no TRUE answer is preferred).

6. `veridicalPreferential_isCDistributiveAt`: Veridical predicates preserve
   C-distributivity for their world-sensitive semantics.

### Architecture:

- C-distributivity is a PROVABLE PROPERTY, not a stipulated field
- Each predicate DEFINES its propositional and question semantics
- Veridical predicates use world-sensitive semantics (`propSemanticsAt`, `questionSemanticsAt`)
- The classification follows from proved properties

This gives genuine explanatory force: "hope" is anti-rogative BECAUSE
its degree-comparison semantics makes it C-distributive, and combined
with positive valence (TSP) and non-veridicality, this yields triviality.

"Be happy" takes questions DESPITE being C-distributive and positive BECAUSE
it is veridical — the truth requirement breaks the triviality derivation.
-/

-- ============================================================================
-- Highlighting (@cite{uegaki-2022} Ch 6 §6.6, @cite{pruitt-roelofsen-2011})
-- ============================================================================

/-!
## Highlighted Propositions and hope-whether

@cite{uegaki-2022} Ch 6 addresses apparent counterexamples to the anti-rogativity
of positive NVPs: attested "hope whether" constructions (@cite{white-2021}).

The solution uses **highlighting** (@cite{pruitt-roelofsen-2011}): clauses have both
an ordinary semantic value and a **highlighted value** — a subset of propositions
with privileged status.

### Key Insight

- Polar interrogatives (`whether p`): highlighted value = `{p}` (singleton)
- Constituent interrogatives (`who left`): highlighted value = ordinary value
- Declaratives (`that p`): highlighted value = `{p}` (singleton)

When `hope` is sensitive to the highlighted value rather than the ordinary
semantic value, `hope whether p` reduces to `hope that p` — no triviality!
The anti-rogativity prediction is preserved for constituent interrogatives
(highlighted value = full question = trivial) while allowing polar ones.
-/

/-- Clause types relevant to highlighting. -/
inductive HighlightingClauseType where
  | declarative         -- "that p"
  | polarInterrogative  -- "whether/if p"
  | constituentInterrog -- "who/what/which..."
  deriving DecidableEq, Repr

/--
Highlighted propositions of a clause (@cite{pruitt-roelofsen-2011}).

- Polar interrogatives highlight the overtly-realized proposition (singleton)
- Declaratives highlight the asserted proposition (singleton)
- Constituent interrogatives highlight all alternatives (= ordinary value)

The key asymmetry: polar and declarative both yield singletons,
while constituent interrogatives yield the full question.
-/
def highlightedValue {W : Type*} (ct : HighlightingClauseType) (Q : AlternativeList W) :
    AlternativeList W :=
  match ct with
  | .declarative => Q.take 1
  | .polarInterrogative => Q.take 1
  | .constituentInterrog => Q

/--
Highlighting-sensitive version of hope's denotation.

The Dayal-answer preferred by the subject is restricted to be a
**highlighted** proposition of the complement φ, rather than a member
of the ordinary semantic value.

⟦hope_C φ⟧ = λx: ∃w'[AnsD_w'(⟦φ⟧_H) ∈ C] .
              ∃d ∈ { Pref_w(x,p) | p ∈ C } [d > θ(C)] .
              ∃w''[ AnsD_w''(Q) ∈ ⟦φ⟧_H ∧ Pref_w(x, AnsD_w''(Q)) > θ(C) ]
-/
def hopeHighlightSemantics {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (ct : HighlightingClauseType) (x : E) (Q C : AlternativeList W) : Bool :=
  let highlighted := highlightedValue ct Q
  highlighted.any fun p => decide (μ x p > θ C)

/--
With a declarative complement, highlighting changes nothing:
the highlighted value is {p}, and hopeSemanticsHighlight reduces to
whether μ(x, p) > θ(C). Same as standard hope.
-/
theorem hope_highlight_declarative_equiv {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (p : (W → Bool)) (C : AlternativeList W) :
    hopeHighlightSemantics μ θ .declarative x [p] C =
    decide (μ x p > θ C) := by
  simp [hopeHighlightSemantics, highlightedValue]

/--
With a polar interrogative "whether p", highlighting reduces to the
singleton {p}. So "hope whether p" ≈ "hope that p" — NOT trivial.
-/
theorem hope_highlight_polar_equiv {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (p : (W → Bool)) (neg_p : (W → Bool)) (C : AlternativeList W) :
    hopeHighlightSemantics μ θ .polarInterrogative x [p, neg_p] C =
    decide (μ x p > θ C) := by
  simp [hopeHighlightSemantics, highlightedValue]

/--
With a constituent interrogative "who V", all alternatives are highlighted.
This is identical to the standard (non-highlighting) semantics —
still trivial when combined with TSP and Q ⊆ C.
-/
theorem hope_highlight_constituent_equiv {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W) :
    hopeHighlightSemantics μ θ .constituentInterrog x Q C =
    Q.any (fun p => decide (μ x p > θ C)) := by
  simp [hopeHighlightSemantics, highlightedValue]

/--
Constituent interrogatives with TSP are still trivial under highlighting.
This preserves the anti-rogativity prediction for "*hope who left".
-/
theorem hope_highlight_constituent_trivial {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (Q C : AlternativeList W)
    (h_subset : ∀ p, p ∈ Q → p ∈ C)
    (h_assert : hopeHighlightSemantics μ θ .constituentInterrog x Q C = true) :
    tspSatisfied μ θ x C = true := by
  rw [hope_highlight_constituent_equiv] at h_assert
  unfold tspSatisfied
  simp only [List.any_eq_true, decide_eq_true_eq] at *
  obtain ⟨p, hp_in_Q, hp_holds⟩ := h_assert
  exact ⟨p, h_subset p hp_in_Q, hp_holds⟩

-- ════════════════════════════════════════════════════════════════
-- § Emotive Doxastic Predicates (hope, fear as hybrids)
-- @cite{anand-hacquard-2013} @cite{scheffler-2008}
-- ════════════════════════════════════════════════════════════════

/-!
## Emotive Doxastics: Hybrid Representational + Preferential

@cite{anand-hacquard-2013} show that `hope` and `fear` are not pure
preferential predicates (like `want`). They have three components:

1. **Doxastic assertion**: the attitude holder believes φ is *possible*
   (∃w' ∈ DOX: φ(w') = 1)
2. **Preference assertion**: φ-verifiers are preferred to φ-falsifiers
3. **Uncertainty condition**: the attitude holder is *uncertain* about φ
   (both φ-verifiers and φ-falsifiers exist in DOX)

The doxastic component is what licenses embedded epistemic *possibility*
modals. The uncertainty condition is what blocks epistemic *necessity*:
necessity entails certainty, contradicting the uncertainty requirement.

This hybrid structure distinguishes `hope` from `want`:
- `want` is pure preferential — no doxastic component, no epistemic licensing
- `hope` has a doxastic component — licenses `might` but not `must`

### Evidence for the doxastic component (@cite{scheffler-2008})

`hope` can felicitously answer questions (providing doxastic information):
  A: "Is Peter coming today?"
  B: "I hope/\*want that he is coming today."

`hope` is infelicitous with certainty about the complement:
  "It is raining. #I hope it is raining." (vs. ✓"I want it to be raining.")

### Verifiers and Falsifiers

@cite{anand-hacquard-2013} define φ-verifiers in information state S as
subsets of S that are *certain* about φ — where φ's truth value doesn't
change with (monotonically) increasing information:

  φ-verifiers in S = {S' ⊂ S | ∀S'' ⊂ S': ∀w' ∈ S'': ⟦φ⟧(w') = 1}

For unmodalized φ, this simplifies to pow(S ∩ φ).
For modalized φ (might p, must p), verifiers are still pow(S ∩ p) —
modalized complements raise the same issue as unmodalized ones.
-/

open Semantics.Attitudes.Doxastic (AccessRel diaAt boxAt)

/-- An emotive doxastic predicate: hybrid representational + preferential.

Combines a doxastic accessibility relation (from `Doxastic.lean`)
with a preference function (from `Preferential`). The accessibility
relation provides the information state that epistemics quantify over;
the preference function orders verifiers against falsifiers. -/
structure EmotiveDoxasticPredicate (W E : Type*) where
  /-- Name of the predicate -/
  name : String
  /-- Doxastic accessibility relation: DOX(x, w) -/
  access : AccessRel W E
  /-- Preference function: μ(x, p) → degree -/
  μ : PreferenceFunction W E
  /-- Threshold function: θ(C) → degree -/
  θ : ThresholdFunction W
  /-- Evaluative valence (positive for hope, negative for fear) -/
  valence : AttitudeValence

/-- The doxastic assertion: ∃w' ∈ DOX(x,w) such that φ(w').

This is the component that licenses embedded epistemic possibility modals.
When the complement is `might p`, the doxastic assertion reduces to
`DOX ∩ p ≠ ∅` by vacuous quantification — identical to the unmodalized
case. -/
def EmotiveDoxasticPredicate.doxasticAssertion {W E : Type*}
    (V : EmotiveDoxasticPredicate W E) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W) : Prop :=
  diaAt V.access agent w worlds p

/-- The uncertainty condition: both φ-verifiers and φ-falsifiers exist
in DOX. The attitude holder is genuinely uncertain about φ.

This is what blocks epistemic necessity: `must p` under `hope` would
require ∀w' ∈ DOX: p(w'), which combined with the uncertainty condition
(∃w' ∈ DOX: ¬p(w')) yields a contradiction. -/
def EmotiveDoxasticPredicate.uncertaintyCondition {W E : Type*}
    (V : EmotiveDoxasticPredicate W E) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W) : Prop :=
  -- ∃w' ∈ DOX: p(w') — verifiers exist
  diaAt V.access agent w worlds p ∧
  -- ∃w' ∈ DOX: ¬p(w') — falsifiers exist
  diaAt V.access agent w worlds (fun w' => ¬ p w')

/-- The preference assertion: φ-verifying doxastic alternatives are
preferred to φ-falsifying ones.

For positive valence (hope): μ(x, p) > θ(C) — the agent prefers p.
For negative valence (fear): μ(x, p) > θ(C) — where μ measures dispreference. -/
def EmotiveDoxasticPredicate.preferenceAssertion {W E : Type*}
    (V : EmotiveDoxasticPredicate W E) (agent : E) (p : W → Prop) [DecidablePred p]
    (C : AlternativeList W) : Prop :=
  V.μ agent (fun w => decide (p w)) > V.θ C

/-- Full semantics for an emotive doxastic: all three components must hold.

⟦a hopes_C that φ⟧ is defined iff:
  (i)   φ-verifiers in S' ≠ ∅ ∧ φ-falsifiers in S' ≠ ∅    (uncertainty)
  (ii)  ∃w' ∈ S': ⟦φ⟧(w') = 1                              (doxastic)
  (iii) φ-verifiers >_DES φ-falsifiers                       (preference)

where S' = DOX(a, w).

Note: condition (ii) is entailed by the first conjunct of (i), so it is
redundant in the conjunction. We include it explicitly for clarity and
because it is the component responsible for epistemic licensing — it
provides the information state that embedded epistemics are anaphoric to. -/
def EmotiveDoxasticPredicate.holdsAt {W E : Type*}
    (V : EmotiveDoxasticPredicate W E) (agent : E) (p : W → Prop) [DecidablePred p]
    (w : W) (worlds : List W) (C : AlternativeList W) : Prop :=
  V.uncertaintyCondition agent p w worlds ∧
  V.doxasticAssertion agent p w worlds ∧
  V.preferenceAssertion agent p C

/-- Hope: emotive doxastic with positive valence. -/
def hopeHybrid {W E : Type*} (R : AccessRel W E)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    EmotiveDoxasticPredicate W E :=
  { name := "hope", access := R, μ := μ, θ := θ, valence := .positive }

/-- Fear: emotive doxastic with negative valence. -/
def fearHybrid {W E : Type*} (R : AccessRel W E)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W) :
    EmotiveDoxasticPredicate W E :=
  { name := "fear", access := R, μ := μ, θ := θ, valence := .negative }

-- ════════════════════════════════════════════════════════════════
-- § Epistemic Embedding Theorems
-- ════════════════════════════════════════════════════════════════

/-- Under emotive doxastics, `might p` contributes the same doxastic
assertion as bare `p` — modal concord.

When the complement is `might p`, the doxastic assertion becomes:
  ∃w' ∈ DOX: (∃w'' ∈ DOX: p(w''))
By vacuous quantification over the shared information state, this
reduces to: ∃w'' ∈ DOX: p(w'').
Both yield: DOX ∩ p ≠ ∅.

We model this by showing that the doxastic assertion for `p` and for
the function `λ w. diaAt R x w worlds p` (= "might p" evaluated at
the same DOX) are equivalent when the information state is shared. -/
theorem doxastic_assertion_might_concord {W E : Type*}
    (V : EmotiveDoxasticPredicate W E) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W)
    (h : V.doxasticAssertion agent p w worlds) :
    V.doxasticAssertion agent
      (fun _ => diaAt V.access agent w worlds p) w worlds := by
  simp only [EmotiveDoxasticPredicate.doxasticAssertion, diaAt] at *
  obtain ⟨w', hw'_in, hw'_acc, hw'_p⟩ := h
  exact ⟨w', hw'_in, hw'_acc, ⟨w', hw'_in, hw'_acc, hw'_p⟩⟩

/-- Under emotive doxastics, `must p` contradicts the uncertainty
condition. If ∀w' ∈ DOX: p(w'), then there are no falsifiers in DOX,
violating the uncertainty condition's requirement that
∃w' ∈ DOX: ¬p(w'). -/
theorem must_contradicts_uncertainty {W E : Type*}
    (V : EmotiveDoxasticPredicate W E) (agent : E) (p : W → Prop)
    (w : W) (worlds : List W)
    (h_must : boxAt V.access agent w worlds p) :
    ¬ V.uncertaintyCondition agent p w worlds := by
  simp only [EmotiveDoxasticPredicate.uncertaintyCondition, diaAt, boxAt] at *
  rintro ⟨_, ⟨w', hw'_in, hw'_acc, hw'_np⟩⟩
  exact hw'_np (h_must w' hw'_in hw'_acc)

end Semantics.Attitudes.Preferential
