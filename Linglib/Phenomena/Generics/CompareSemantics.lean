/-
# Generic Semantics: Traditional GEN vs RSA Threshold

Connects the traditional GEN operator to
@cite{tessler-goodman-2019} threshold-based RSA approach.

## Result

The hidden "normalcy" parameter in traditional GEN can be eliminated:
for any normalcy-based GEN configuration, there exists a threshold θ
such that threshold semantics gives the same truth value.

GEN is eliminable: threshold semantics can express any GEN configuration,
making the observable "prevalence" sufficient.

## Dynamic bridge

This eliminability result also applies to @cite{kirkpatrick-2024}'s dynamic
semantics in discourse-initial position: `fromPredicate_static` (in
`Theories/Semantics/Dynamic/Generics.lean`) proves that discourse-initial
evaluation of a `GenericSentence` constructed via `fromPredicate` equals the
static `traditionalGEN`. Composing with `gen_eliminable`, any discourse-initial
dynamic generic is expressible via threshold semantics. The dynamic theory
diverges from threshold only in multi-sentence discourse.

-/

import Linglib.Theories.Semantics.Lexical.Noun.Kind.Generics
import Linglib.Theories.Semantics.Lexical.CovertQuantifier

namespace Phenomena.Generics.CompareSemantics

open Semantics.Lexical.Noun.Kind.Generics
open Semantics.Lexical.CovertQuantifier

-- Helper Lemmas for Rational Arithmetic

/-- Prevalence is always non-negative (derived from `measure_nonneg`). -/
theorem prevalence_nonneg
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    : prevalence situations restrictor scope ≥ 0 :=
  measure_nonneg situations restrictor scope

/-- Prevalence is at most 1 (derived from `measure_le_one`). -/
theorem prevalence_le_one
    (situations : List Situation)
    (restrictor : Restrictor)
    (scope : Scope)
    (hNonEmpty : (situations.filter restrictor).length > 0)
    : prevalence situations restrictor scope ≤ 1 :=
  measure_le_one situations restrictor scope hNonEmpty

-- Main Theorem: GEN Reduces to Threshold

/--
Traditional GEN is eliminable via threshold semantics for **descriptive** generics.

For any normalcy predicate (the hidden parameter in GEN), there exists
a threshold θ such that `thresholdGeneric` gives the same truth value.

Proof:
- If GEN = true, pick θ = -1. Since prevalence ≥ 0 > -1, threshold generic is true.
- If GEN = false, pick θ = 1. Since prevalence ≤ 1, threshold generic is false.

The "normalcy" parameter is (1) not observable (covert), (2)
context-dependent (varies by property), and (3) potentially circular
(defined to give right results). It can be replaced by observable
prevalence plus uncertain threshold. The RSA model then explains how
the threshold is inferred pragmatically from priors over prevalence.

**Scope limitation** (@cite{krifka-2013}): This result applies only to descriptive
generics (empirical generalizations like "Dogs bark"). Definitional generics
("A madrigal is polyphonic") operate on the interpretation index, restricting
admissible word meanings rather than possible worlds, and cannot be reduced to
prevalence thresholds. See `Phenomena/Generics/Studies/Krifka2013.lean`.
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

-- Connection to @cite{tessler-goodman-2019}

/-!
## How RSA Explains Generic Judgments
@cite{tessler-goodman-2019} @cite{krifka-etal-1995}

@cite{tessler-goodman-2019} go further than just showing GEN is eliminable.
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

See `Phenomena/Generics/Studies/TesslerGoodman2019.lean` for the
full RSA implementation with prevalence priors.
-/

end Phenomena.Generics.CompareSemantics
