import Linglib.Semantics.Degree.Gradability.Adjective
import Linglib.Semantics.Degree.Gradability.Antonymy
import Linglib.Semantics.Degree.Gradability.AntonymPrediction
import Linglib.Studies.Krifka2007
import Linglib.Fragments.English.Predicates.Adjectival
/-!
# [alexandropoulou-gotzner-2024-jos] — The Interpretation of Relative and Absolute Adjectives Under Negation
[alexandropoulou-gotzner-2024-jos]

In: *Journal of Semantics* 41(3), pp. 373–399.

## Thesis

[alexandropoulou-gotzner-2024-jos] (JoS) tests the [horn-1989] R-
implicature account vs. [krifka-2007b]'s complexity-based account of
negative strengthening across **three distinct cases** of negated antonymic
adjectives:

1. **Weak relative** (e.g. *not large* vs. *not small*): both Horn and Krifka
   predict negative strengthening — asymmetric interpretation.
2. **Weak absolute** (e.g. *not clean* vs. *not dirty*): both predict
   symmetric interpretation, since contradictory antonyms partition the scale
   exhaustively (no gap for an implicature to exploit).
3. **Strong gradable** (e.g. *not gigantic* vs. *not tiny*, *not pristine*
   vs. *not filthy*): Horn predicts asymmetric strengthening (since strong
   adjectives are contrary, with a gap). The JoS experimental findings on
   strong adjectives are presented as **prima facie challenges** to Horn's
   account, while not endorsing any specific alternative. Per JoS footnote 2,
   Krifka's account is explicitly restricted to informationally weak
   adjectives and does not commit to a prediction for the strong case.

## Companion paper

The Glossa companion [alexandropoulou-gotzner-2024] formalised in
`AlexandropoulouGotzner2024.lean` extends this work by isolating the role of
overt contextual *competition* in surfacing the asymmetric pattern. The
Glossa paper builds on the JoS findings as established results.

## Substrate consumed

- `Semantics/Gradability/Theory.lean` — `ThresholdPair`,
  `positiveMeaning'`, `contraryNegMeaning`, `notContraryNegMeaning`.
- `Semantics/Degree/Gradability/AntonymPrediction.lean` — `AntonymForm`
  (the four-form quadruplet enum, theory-neutral substrate).
- `Semantics/Gradability/AntonymPrediction.lean` —
  `AntonymForm.contradictoryDenot`, `AntonymForm.strengthenedDenot`,
  `predictionForAntonymy`, `predictionForEntry`, anchor theorems.
- `Semantics/Degree/Basic.lean` — `notPositiveMeaning`.
- `Features/Antonymy.lean` — `NegationType`, `Asymmetry`.
- `Fragments/English/Predicates/Adjectival.lean` — lexical entries
  (transitively, via the Glossa companion file).

## What this file makes Lean-checkable

- A typed three-case taxonomy (`AGCase`).
- Horn 1989's predicted asymmetry direction per cell as a total function
  `AGCase → Asymmetry`.
- Krifka 2007's predicted asymmetry direction per cell as `AGCase → Option
  Asymmetry`, with `none` for `strongGradable` reflecting the paper-faithful
  commitment that Krifka does not extend to strong adjectives.
- The JoS empirical observations as a third such function.
- A theorem witnessing that Horn's prediction *differs* from the JoS
  observation on the `strongGradable` cell — the paper's headline negative
  result, made Lean-checkable.
- The Krifka 2007 hidden-agreement bridge: A&G's lexical commitment to
  contrary semantics for "not positive" coincides definitionally with the
  output of Krifka's pragmatic strengthening procedure on the same input.

## What this file does not formalise

The full Horn 1989 R-implicature derivation, the full Krifka 2007 complexity
calculus, the experimental rating distributions, the participant population
metadata, or the statistical analysis. The prediction signatures are simple
total functions encoding the qualitative direction each theory predicts;
the strength of the falsification claim rides on whether those direction
encodings match the prose of each cited paper, not on a Lean-internal
derivation of the predictions from first principles.
-/

namespace AlexandropoulouGotzner2024JoS

open Degree (Degree Threshold)
open Features (NegationType Asymmetry)
open Degree (GradableAdjective ThresholdPair positiveMeaning'
  contraryNegMeaning notContraryNegMeaning AntonymForm
  predictionForAntonymy predictionForEntry)
open Degree (notPositiveMeaning)
open English.Predicates.Adjectival
  (large clean gigantic)

-- ============================================================================
-- § 1. Three-Case Typology
-- ============================================================================

/-- The JoS paper's three distinct cases of negated antonymic adjectives. -/
inductive AGCase where
  | weakRelative   -- *not large*, *not small*
  | weakAbsolute   -- *not clean*, *not dirty*
  | strongGradable -- *not gigantic*, *not tiny*, *not pristine*, *not filthy*
  deriving Repr, DecidableEq

/-! `Asymmetry` (asymmetric/symmetric direction enum), `predictionForAntonymy`
    (NegationType → Asymmetry skeleton), and `predictionForEntry`
    (GradableAdjective → Asymmetry projection) are now substrate, in
    `Features/Antonymy.lean` and `Semantics/Gradability/AntonymPrediction.lean`
    respectively. The substrate-anchor theorems
    `Degree.contradictoryDenot_synonymy` and
    `Degree.strengthenedDenot_breaks_synonymy` make the
    `.contrary → .asymmetric` / `.contradictory → .symmetric` mapping
    Lean-checkable from the canonical denotations. -/

/-- Each `AGCase` is represented by a canonical Fragment lexical entry. The
    prediction signatures below derive their per-case answers by reading
    `antonymRelation` off this representative — the Fragment is the single
    source of truth, not a parallel hardcoded enum in this file. -/
def AGCase.representative : AGCase → GradableAdjective
  | .weakRelative   => large
  | .weakAbsolute   => clean
  | .strongGradable => gigantic

-- ============================================================================
-- § 3. Horn 1989 Prediction Signature
-- ============================================================================

/-- Horn 1989's R-implicature account predicts asymmetric interpretation
    whenever an extension gap is available between the contrary antonyms,
    and symmetric interpretation when the antonyms are contradictory. The
    per-case answer is derived by reading off the representative Fragment
    entry's `antonymRelation` via `predictionForEntry`. Total over all
    three cases (Horn extends to strong adjectives). -/
def hornPrediction (c : AGCase) : Asymmetry :=
  predictionForEntry c.representative

-- ============================================================================
-- § 4. Krifka 2007 Prediction Signature
-- ============================================================================

/-- Krifka 2007's complexity-based account predicts via the same antonymy
    skeleton as Horn for the weak cases — derived from the Fragment via
    `predictionForEntry` — but is silent on the strong-gradable case (per
    JoS footnote 2: Krifka focuses on informationally weak adjectives only
    and does not extend his account explicitly to strong gradable
    adjectives). The strong-case `none` is the paper-faithful encoding of
    that scope restriction. -/
def krifkaPrediction : AGCase → Option Asymmetry
  | .strongGradable => none
  | c               => some (predictionForEntry c.representative)

-- ============================================================================
-- § 5. JoS Empirical Observations
-- ============================================================================

/-- The JoS paper's reported experimental findings, abstracting from
    response-distribution detail to the qualitative asymmetry direction.
    The strong-gradable cell encodes the paper's headline negative result:
    the observed pattern does NOT match Horn's predicted asymmetric
    behavior. -/
def agObserved : AGCase → Asymmetry
  | .weakRelative   => .asymmetric
  | .weakAbsolute   => .symmetric
  | .strongGradable => .symmetric  -- prima facie challenge to Horn

-- ============================================================================
-- § 6. Horn Falsification Cell
-- ============================================================================

/-- The JoS paper's headline negative result: Horn 1989's account predicts
    asymmetric interpretation for negated strong gradable adjectives, but the
    empirical observations are not asymmetric in the predicted way.

    Theorem-as-stated form (mathlib idiom: name describes the proved
    proposition): `hornPrediction .strongGradable ≠ agObserved .strongGradable`.
    Reading: the JoS paper's "prima facie present challenges for Horn's (1989)
    analysis" claim about strong antonymic adjectives. -/
theorem hornPrediction_ne_observed_on_strong :
    hornPrediction .strongGradable ≠ agObserved .strongGradable := by decide

/-- Horn and the JoS observations *agree* on the weak relative and weak
    absolute cases. The disagreement is localised to the strong-gradable
    cell. -/
theorem horn_agrees_on_weak_cases :
    hornPrediction .weakRelative = agObserved .weakRelative ∧
    hornPrediction .weakAbsolute = agObserved .weakAbsolute :=
  ⟨rfl, rfl⟩

/-- Krifka's account is silent on the strong-gradable case (per JoS fn 2).
    There is therefore no Krifka prediction to falsify on this cell — the
    silence itself is the position the paper attributes to Krifka. -/
theorem krifka_silent_on_strong_gradable :
    krifkaPrediction .strongGradable = none := rfl

/-- On the cells where Krifka does commit, his prediction matches Horn's
    (and matches the JoS observations). The two theories diverge only in
    *whether* they extend to the strong case, not in *what* they predict on
    the cells where they both speak. -/
theorem krifka_agrees_with_horn_where_committed :
    krifkaPrediction .weakRelative = some (hornPrediction .weakRelative) ∧
    krifkaPrediction .weakAbsolute = some (hornPrediction .weakAbsolute) :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- § 7. Krifka 2007 Hidden-Agreement Bridge
-- ============================================================================

/-! Both A&G and Krifka 2007 use the same `ThresholdPair` substrate for the
    *effective* (post-strengthening) semantics of negated contrary antonyms.
    A&G commit to this two-threshold structure as a *lexical* fact; Krifka
    derives it pragmatically from a contradictory base via the M-principle.

    The two views are empirically indistinguishable at the level of their
    composed output: A&G's `notPositiveMeaning d tp.pos` (the literal denotation
    of "not positive" projected through the positive threshold) **is**
    `AntonymForm.strengthenedDenot tp .notPositive d` definitionally.

    The `Iff.rfl` proofs below are **intentional** and load-bearing: their
    fragility under substrate change *is* the point. If `contradictoryNeg`
    ever stops being a `def`-equal alias for `notPositiveMeaning` (e.g. through
    a regression of the Bool→Prop substrate evolution in
    `Semantics/Gradability/Theory.lean`), these theorems will
    break loudly — surfacing the substrate drift at the cross-paper bridge
    rather than letting it propagate silently. -/

/-- **The bridge theorem.** A&G's lexical "not positive" semantics coincides
    with the output of Krifka 2007's pragmatic strengthening procedure on
    the `notPositive` form. Both sides reduce to `d ≤ tp.pos` definitionally
    after the substrate's `def`-to-`abbrev` migration on
    `Theory.lean::contradictoryNeg`. -/
theorem ag_negative_strengthening_eq_krifka {max : Nat}
    (d : Degree max) (tp : ThresholdPair max) :
    notPositiveMeaning d tp.pos ↔
    AntonymForm.strengthenedDenot tp .notPositive d :=
  Iff.rfl

/-- The bridge generalises to the full quadruplet structure: A&G's lexical
    semantics for each of the four forms (positive / not-positive /
    negative / not-negative) coincides with Krifka 2007's `strengthenedQuad`
    output on the corresponding form. -/
theorem ag_quadruplet_eq_krifka_strengthened {max : Nat}
    (d : Degree max) (tp : ThresholdPair max) :
    (positiveMeaning' d tp ↔ AntonymForm.strengthenedDenot tp .positive d) ∧
    (notPositiveMeaning d tp.pos ↔ AntonymForm.strengthenedDenot tp .notPositive d) ∧
    (contraryNegMeaning d tp ↔ AntonymForm.strengthenedDenot tp .negative d) ∧
    (notContraryNegMeaning d tp ↔ AntonymForm.strengthenedDenot tp .notNegative d) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

end AlexandropoulouGotzner2024JoS
