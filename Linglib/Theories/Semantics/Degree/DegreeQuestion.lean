import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core

/-!
# Compositional "How" — Degree Questions
@cite{beck-rullmann-1999} @cite{fox-2007} @cite{rullmann-1995}

Compositional semantics of degree questions ("how tall is Kim?"),
connecting the syntactic structure of degree questions to the
maximality-based analysis in `Theories/Semantics/Questions/DegreeQuestion.lean`
(Fox & Hackl 2007).

## Compositional Structure

    "How tall is Kim?" = [CP [how [DegP d-tall]] [TP Kim is t_d]]

The wh-word "how" is a degree question operator that asks for the
degree d such that the matrix clause is true:

    ⟦how⟧ = λP⟨d,t⟩. ?d. P(d)

In the Hamblin/Karttunen semantics, the answer set is:
    { p | ∃d. p = λw. height_w(Kim) ≥ d }

The maximally informative answer is the one with d = height(Kim)
(Fox & Hackl 2007: max⊨ applied to the answer set).

## Bridge to Fox & Hackl

`Theories/Semantics/Questions/DegreeQuestion.lean` provides:
- The UDM (universal density of measurement)
- Negative island analysis (density blocks max⊨ under negation)
- Modal obviation (universal modal rescues max⊨)

This module provides the compositional structure that feeds into
that analysis.

-/

namespace Semantics.Degree.DegreeQuestion

open Core.Scale (IsMaxInf HasMaxInf)

-- ════════════════════════════════════════════════════
-- § 1. Degree Question Operator
-- ════════════════════════════════════════════════════

/-- The answer set of a degree question: the set of propositions
    of the form "μ(x) ≥ d" for each degree d.

    For "how tall is Kim?", this is:
    { λw. height_w(Kim) ≥ d | d ∈ D }

    The most informative answer has d = height(Kim). -/
def answerSet {W D : Type*} [Preorder D]
    (μ : W → D) : Set (W → Prop) :=
  { p | ∃ d : D, p = fun w => μ w ≥ d }

-- ════════════════════════════════════════════════════
-- § 2. Maximally Informative Answer
-- ════════════════════════════════════════════════════

/-- The maximally informative answer to "how tall is Kim?" is the
    degree d₀ such that "height(Kim) ≥ d₀" is true and entails all
    other true answers.

    This connects to `IsMaxInf` from `Core.Scale`:
    the maximally informative element of the "at least" degree property. -/
def isMaximalAnswer {W D : Type*} [LinearOrder D]
    (μ : W → D) (d₀ : D) (w : W) : Prop :=
  IsMaxInf (Core.Scale.atLeastDeg μ) d₀ w

/-- The maximally informative answer exists iff the degree property
    has max⊨. For "at least d", this always exists (= the true value).
    For "more than d", this fails on dense scales (Fox & Hackl). -/
def hasMaximalAnswer {W D : Type*} [LinearOrder D]
    (μ : W → D) (w : W) : Prop :=
  HasMaxInf (Core.Scale.atLeastDeg μ) w

/-- Simple degree questions always have maximally informative answers
    (because "at least d" is a closed degree property). -/
theorem simple_degree_question_has_answer {W D : Type*} [LinearOrder D]
    (μ : W → D) (w : W) : hasMaximalAnswer μ w :=
  Core.Scale.atLeast_hasMaxInf μ w

end Semantics.Degree.DegreeQuestion
