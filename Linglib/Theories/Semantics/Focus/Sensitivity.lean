import Linglib.Theories.Semantics.Focus.Interpretation
import Linglib.Theories.Semantics.Attitudes.Preferential

/-!
# Focus-Sensitivity and Degree Semantics
@cite{rooth-1992} @cite{villalta-2008} @cite{kennedy-2007} @cite{ozyildiz-etal-2025}

Structural bridge between Rooth's focus alternatives, Villalta's degree
semantics for preferential predicates, and Kennedy's significance
presuppositions.

## The Compositional Chain

```
Focus marking on α produces ⟦α⟧o and ⟦α⟧f          [Rooth 1985/1992]
        ↓
~ resolves C ⊆ ⟦α⟧f with ⟦α⟧o ∈ C                 [Rooth 1992]
        ↓
Degree predicate: μ(x, ⟦α⟧o) > θ(C)                [Villalta 2008]
        ↓
Significance presup: ∃q ∈ C. μ(x,q) > θ(C)         [Kennedy 2007]
        ↓
For positive valence: this = TSP                      [Uegaki & Sudo 2019]
```

## Key Results

- `liftDegreeFS`: degree predicates become focus-sensitive `ClauseEmbedPred`s
- `liftDegreeFS_is_fs`: proves focus-sensitivity when threshold depends on C
- `focusSignificance`: ~ + degree predicate → significance presupposition
- `tsp_from_focus`: for positive valence, focus significance = TSP
- `assertion_entails_tsp`: if the assertion holds, TSP is automatically satisfied
  (the ordinary value, guaranteed in C by ~, is itself the witness)
-/

namespace Semantics.Focus.Sensitivity

open Semantics.FocusInterpretation (PropFocusValue FocusResolution ClauseEmbedPred
  IsFocusSensitive)
open Semantics.Attitudes.Preferential (PreferenceFunction ThresholdFunction QuestionDen
  AttitudeValence tspSatisfied significancePresupSatisfied)

-- ============================================================================
-- §1. Degree Predicates as Focus-Sensitive ClauseEmbedPreds
-- ============================================================================

/-!
## Lifting Degree Predicates via Focus Alternatives

A degree-comparison predicate μ(x,p) > θ(C) becomes a `ClauseEmbedPred`
when the comparison class C is determined by the focus alternatives via
a conversion function `altsToC`.

This models what the ~ operator does: it resolves focus alternatives ⟦α⟧f
to a comparison class C. The `altsToC` parameter abstracts over the
contextual resolution.

Combined with `liftNonFS` (from `Interpretation.lean`), this gives a
complete structural account of focus-sensitivity:
- Degree predicates → focus-sensitive (by `liftDegreeFS_is_fs`)
- Doxastic predicates → not focus-sensitive (by `liftNonFS_not_fs`)
-/

/-- Lift a degree-comparison predicate to `ClauseEmbedPred` by using focus
    alternatives as the comparison class.

    - @cite{rooth-1992}: focus alternatives ⟦α⟧f
    - @cite{villalta-2008}: comparison class C in μ(x,p) > θ(C)
    - Connection: C = altsToC(⟦α⟧f) — the ~ operator's role -/
def liftDegreeFS {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (altsToC : PropFocusValue W → QuestionDen W) : ClauseEmbedPred W E :=
  λ x p f _w => decide (μ x p > θ (altsToC f))

/-- Degree predicates lifted via focus alternatives ARE focus-sensitive,
    provided the threshold depends nontrivially on the comparison class.

    Sufficient condition: two focus-alternative sets yield different
    thresholds, with the preference value falling between them.

    This is THE structural bridge between @cite{rooth-1992} and
    @cite{villalta-2008}: degree truth depends on focus alternatives
    because they determine the comparison class. -/
theorem liftDegreeFS_is_fs {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (altsToC : PropFocusValue W → QuestionDen W)
    (x : E) (p : W → Bool) (w : W)
    (f₁ f₂ : PropFocusValue W)
    (h_above : μ x p > θ (altsToC f₁))
    (h_below : ¬(μ x p > θ (altsToC f₂))) :
    IsFocusSensitive (liftDegreeFS μ θ altsToC) := by
  refine ⟨x, p, f₁, f₂, w, ?_⟩
  unfold liftDegreeFS
  simp [h_above, h_below]

-- ============================================================================
-- §2. Focus Resolution and Significance Presuppositions
-- ============================================================================

/-!
## From ~ to Significance Presuppositions

When the ~ operator resolves focus alternatives to a comparison class C
(via `FocusResolution`), and a degree predicate uses C, Kennedy's
significance generalization produces a presupposition.

### The Derivation

1. ~ introduces C with C ⊆ ⟦α⟧f and ⟦α⟧o ∈ C (`FocusResolution`)
2. Degree predicate asserts: μ(x, ⟦α⟧o) > θ(C)
3. Kennedy significance: the degree scale must be "significant" w.r.t. C
4. For positive valence: significance = ∃q ∈ C. μ(x,q) > θ(C) = TSP

### Why ⟦α⟧o ∈ C Matters

The ordinary-value-in-C constraint (from `FocusResolution.ordinary_in_C`)
ensures that whenever the assertion is true, the TSP is automatically
satisfied — the ordinary value itself is the witness. This is the
compositional reason why TSP is non-vacuous: ~ guarantees a candidate.
-/

/-- Significance presupposition arising from combining a degree predicate
    with a focus-resolved comparison class.

    When ~ resolves ⟦α⟧f to C, and a degree predicate V uses C,
    the presupposition depends on V's valence:
    - Positive (hope, want): ∃q ∈ C. μ(x,q) > θ(C) — this IS TSP
    - Negative (fear): weaker threat-identification condition

    @cite{kennedy-2007}: degree constructions carry significance presuppositions.
    @cite{uegaki-sudo-2019}: significance + positive valence = TSP. -/
def focusSignificance {W E : Type*}
    (valence : AttitudeValence)
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (res : FocusResolution W) : Bool :=
  significancePresupSatisfied valence μ θ x res.comparisonClass

/-- For positive valence, focus significance IS TSP.

    This closes the compositional chain:
    ~ → C → degree predicate → Kennedy significance → TSP.

    The proof is definitional: `significancePresupSatisfied .positive`
    dispatches to `tspSatisfied` by construction. The non-trivial content
    is the ARCHITECTURE — TSP arises compositionally from focus + degree
    semantics rather than being stipulated per-predicate. -/
theorem tsp_from_focus {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (res : FocusResolution W) :
    focusSignificance .positive μ θ x res = tspSatisfied μ θ x res.comparisonClass := rfl

/-- If the degree assertion holds, the TSP is automatically satisfied.

    The ordinary value ⟦α⟧o is guaranteed to be in C (by ~'s second
    constraint, `FocusResolution.ordinary_in_C`). So if μ(x, ⟦α⟧o) > θ(C)
    (the assertion), then ⟦α⟧o witnesses ∃q ∈ C. μ(x,q) > θ(C) (the TSP).

    This is the compositional reason why TSP is a presupposition, not an
    independent requirement: it's entailed by the assertion whenever ~
    resolves properly. -/
theorem assertion_entails_tsp {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (res : FocusResolution W)
    (h_assert : μ x res.ordinary > θ res.comparisonClass) :
    tspSatisfied μ θ x res.comparisonClass = true := by
  simp only [tspSatisfied, List.any_eq_true]
  exact ⟨res.ordinary, res.ordinary_in_C, by simpa using h_assert⟩

/-- Negative valence predicates always satisfy significance (trivially).

    Fear, worry, and other negative-valence predicates have a weaker
    "threat identification" significance condition that is trivially
    true — hence no TSP, hence no triviality with questions, hence
    they CAN take interrogative complements. -/
theorem negative_significance_trivial {W E : Type*}
    (μ : PreferenceFunction W E) (θ : ThresholdFunction W)
    (x : E) (res : FocusResolution W) :
    focusSignificance .negative μ θ x res = true := rfl

end Semantics.Focus.Sensitivity
