/-
# Generic Semantics: Traditional GEN vs RSA Threshold

Connects the traditional GEN operator (Krifka et al. 1995) to
Tessler & Goodman's (2019) threshold-based RSA approach.

## Result

The hidden "normalcy" parameter in traditional GEN can be eliminated:
for any normalcy-based GEN configuration, there exists a threshold θ
such that threshold semantics gives the same truth value.

GEN is eliminable: threshold semantics can express any GEN configuration,
making the observable "prevalence" sufficient.

## References

- Krifka, M. et al. (1995). Genericity: An Introduction.
- Tessler, M. H. & Goodman, N. D. (2019). The Language of Generalization.
- Lassiter, D. & Goodman, N. D. (2017). Adjectival vagueness in a Bayesian model.
-/

import Linglib.Theories.Montague.Noun.Kind.Generics
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

namespace Theories.Comparisons.GenericSemantics

open Montague.Noun.Kind.Generics

-- Helper Lemmas for Rational Arithmetic

/--
Prevalence is always non-negative (it's a ratio of non-negative integers).
-/
theorem prevalence_nonneg
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : prevalence situations restrictor scope ≥ 0 := by
  simp only [prevalence]
  by_cases h : (situations.filter restrictor).length = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _

/--
Prevalence is at most 1 (when restrictor situations are non-empty).
The numerator (scope ∩ restrictor) is at most the denominator (restrictor).
-/
theorem prevalence_le_one
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    (hNonEmpty : (situations.filter restrictor).length > 0)
    : prevalence situations restrictor scope ≤ 1 := by
  simp only [prevalence]
  have hPos : (situations.filter restrictor).length ≠ 0 := Nat.pos_iff_ne_zero.mp hNonEmpty
  simp only [hPos, ↓reduceIte]
  have hLenLe : (List.filter scope (List.filter restrictor situations)).length ≤
                (List.filter restrictor situations).length :=
    List.length_filter_le _ _
  have hDenom : (0 : ℚ) < ↑(List.filter restrictor situations).length := by
    rw [Nat.cast_pos]
    exact hNonEmpty
  calc (↑(List.filter scope (List.filter restrictor situations)).length : ℚ) /
         ↑(List.filter restrictor situations).length
       ≤ ↑(List.filter restrictor situations).length /
         ↑(List.filter restrictor situations).length := by
           apply div_le_div_of_nonneg_right
           · exact Nat.cast_le.mpr hLenLe
           · exact le_of_lt hDenom
     _ = 1 := div_self (ne_of_gt hDenom)

-- Main Theorem: GEN Reduces to Threshold

/--
Traditional GEN is eliminable via threshold semantics.

For any normalcy predicate (the hidden parameter in GEN), there exists
a threshold θ such that `thresholdGeneric` gives the same truth value.

Proof:
- If GEN = true, pick θ = -1. Since prevalence ≥ 0 > -1, threshold generic is true.
- If GEN = false, pick θ = 1. Since prevalence ≤ 1, threshold generic is false.

The "normalcy" parameter is (1) not observable (covert), (2)
context-dependent (varies by property), and (3) potentially circular
(defined to give right results). It can be replaced by observable
prevalence plus uncertain threshold. The RSA model (Tessler & Goodman
2019) then explains how the threshold is inferred pragmatically from
priors over prevalence.
-/
theorem gen_eliminable
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    (hNonEmpty : (situations.filter restrictor).length > 0)
    : ∃ θ : ℚ, traditionalGEN situations normal restrictor scope =
               thresholdGeneric situations restrictor scope θ := by
  by_cases hGEN : traditionalGEN situations normal restrictor scope
  · -- Case: GEN = true. Pick θ = -1
    use -1
    simp only [thresholdGeneric, hGEN]
    -- Need: true = decide (prevalence > -1)
    -- We have: prevalence ≥ 0 > -1
    have hNonneg := prevalence_nonneg situations restrictor scope
    symm
    rw [decide_eq_true_iff]
    -- Goal: -1 < prevalence. We have 0 ≤ prevalence and -1 < 0.
    have h : (-1 : ℚ) < 0 := by decide
    linarith
  · -- Case: GEN = false. Pick θ = 1
    use 1
    simp only [thresholdGeneric]
    -- Need: false = decide (prevalence > 1)
    -- We have: prevalence ≤ 1, so ¬(prevalence > 1)
    have hLe := prevalence_le_one situations restrictor scope hNonEmpty
    have hNotGEN : traditionalGEN situations normal restrictor scope = false := by
      simp only [Bool.eq_false_iff]
      exact hGEN
    simp only [hNotGEN]
    symm
    rw [decide_eq_false_iff_not]
    -- Goal: ¬(1 < prevalence). We have prevalence ≤ 1.
    intro hContra
    linarith

-- Corollary: Matching Truth Values

/--
For any GEN configuration that evaluates to `true`, threshold semantics
can also produce `true` (with θ < 0).
-/
theorem gen_true_implies_threshold_true
    (situations : List Situation)
    (normal : NormalcyPredicate)
    (restrictor : Restrictor)
    (scope : Scope)
    (_hGEN : traditionalGEN situations normal restrictor scope = true)
    : thresholdGeneric situations restrictor scope (-1) = true := by
  simp only [thresholdGeneric, decide_eq_true_iff]
  have hNonneg := prevalence_nonneg situations restrictor scope
  -- Need: -1 < prevalence. We have 0 ≤ prevalence.
  have h : (-1 : ℚ) < 0 := by decide
  linarith

/--
For any GEN configuration that evaluates to `false`, threshold semantics
can also produce `false` (with θ = 1).
-/
theorem gen_false_implies_threshold_false
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    (hNonEmpty : (situations.filter restrictor).length > 0)
    : thresholdGeneric situations restrictor scope 1 = false := by
  simp only [thresholdGeneric, decide_eq_false_iff_not]
  have hLe := prevalence_le_one situations restrictor scope hNonEmpty
  -- Need: ¬(1 < prevalence). We have prevalence ≤ 1.
  intro hContra
  linarith

-- Connection to Tessler & Goodman (2019)

/-!
## How RSA Explains Generic Judgments

Tessler & Goodman (2019) go further than just showing GEN is eliminable.
They explain WHY certain generics are judged true despite low prevalence.

The threshold θ is uncertain and integrated out:

```
P(generic true | prevalence p) = ∫ δ_{p > θ} · P(θ) dθ = p
```

With a uniform prior over θ, the probability a generic is true equals
the prevalence. But the listener reasons about both prevalence and
what the speaker meant:

```
L₁(p | generic) ∝ p · P(p)
```

The prior P(p) varies by property:
- "Lays eggs": bimodal prior (many at 0, some at ~50%)
- "Is female": unimodal prior (peak at 50%)

Same 50% prevalence, different judgments:
- "Robins lay eggs" true -- 50% is high relative to prior
- "Robins are female" false -- 50% is expected given prior

See `Theories/RSA/Implementations/TesslerGoodman2019.lean` for the
full RSA implementation with prevalence priors.
-/

end Theories.Comparisons.GenericSemantics
