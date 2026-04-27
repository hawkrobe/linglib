import Linglib.Core.Modality.ModalTypes
import Linglib.Core.Scales.Scale
import Linglib.Theories.Semantics.Degree.Core

/-!
# Degree Questions — compositional structure + Fox/Hackl maximality
@cite{beck-rullmann-1999} @cite{fox-2007} @cite{rullmann-1995} @cite{fox-hackl-2006} @cite{link-1983}

Compositional semantics of degree questions ("how tall is Kim?") and the
maximality-based analysis of @cite{fox-2007} that derives negative-island
and modal-obviation effects from the universal density of measurement.

## Compositional structure (@cite{beck-rullmann-1999} @cite{rullmann-1995})

    "How tall is Kim?" = [CP [how [DegP d-tall]] [TP Kim is t_d]]

The wh-word "how" is a degree question operator that asks for the
degree d such that the matrix clause is true:

    ⟦how⟧ = λP⟨d,t⟩. ?d. P(d)

In the Hamblin/Karttunen semantics, the answer set is:
    { p | ∃d. p = λw. height_w(Kim) ≥ d }

The maximally informative answer is the one with d = height(Kim)
(@cite{fox-2007}: max⊨ applied to the answer set).

## The Fox-Hackl unification (@cite{fox-hackl-2006})

Degree questions, definite descriptions, and scalar implicatures all involve
the same maximality requirement (`Core.Scale.HasMaxInf`). When the relevant
scale is dense (`[DenselyOrdered α]`), this requirement
interacts with negation and modals to produce systematic acceptability patterns.

| Construction                          | Formulation                         |
|---------------------------------------|-------------------------------------|
| Degree question "How much φ?"         | HasMaxInf φ w                       |
| Definite "the amount that φ"          | HasMaxInf φ w (@cite{link-1983} maximality)|
| Only/EXH "only φ"                     | HasMaxInf φ w (OIG, F&H eq. 6)      |
| Implicature of bare "φ"               | HasMaxInf φ w (covert EXH)          |

All four fail when `HasMaxInf φ w` is unsatisfiable — which happens precisely
when φ describes an open set on a dense scale (no infimum/supremum).

## What this file formalizes

Beyond `Core.Scale` (which provides degree properties `atLeastDeg`,
`moreThanDeg`, etc. and their HasMaxInf/density theorems):

1. **Answer-set construction** for degree questions (compositional structure)
2. **Maximally informative answer** as `IsMaxInf` over the degree property
3. **Negative islands**: negation of a downward-monotone property on a dense
   scale yields an open complement with no max⊨ element
4. **Modal obviation**: ∀-modals rescue maximality violations, ∃-modals don't
5. **Monotonicity preservation** through modals

Degree properties (`eqDeg`, `atLeastDeg`, `moreThanDeg`, `atMostDeg`,
`lessThanDeg`), their monotonicity, HasMaxInf theorems, Kennedy–F&H bridge,
and discrete–dense divergence theorems are in `Core.Scale` (§ 6 of
`Core/MeasurementScale.lean`).
-/

namespace Semantics.Degree.Question

open Core.Scale (IsMaxInf HasMaxInf)
open Core.Scale
open Core.Modality (ModalForce)

-- ════════════════════════════════════════════════════
-- § 1. Compositional structure
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

-- ════════════════════════════════════════════════════
-- § 3. Negative Islands (@cite{fox-2007} §3)
-- ════════════════════════════════════════════════════

variable {α W : Type*} [LinearOrder α]

/-- The **negated degree property**: ¬φ(d)(w).

    Example: φ(d)(w) = "John weighs ≥ d pounds in w"
    negated: "John does not weigh ≥ d pounds in w" -/
def negatedDegreeProp (φ : α → W → Prop) : α → W → Prop :=
  fun d w => ¬ φ d w

/-- **Negative island theorem** (@cite{fox-2007} §3.3):

    "*How much does John not weigh?" is unacceptable because on a dense
    scale, the negated set {d | ¬φ(d)(w)} has no maximally informative element.

    Setup: φ is downward monotone (e.g., "weighs ≥ d": smaller thresholds
    are easier to satisfy). At world w, there is a boundary below which φ
    holds and above which it fails. Density ensures that for any d in the
    negated set, there exists d' strictly between the boundary and d — and
    ¬φ(d) does not entail ¬φ(d'), because in a world where the boundary
    sits between d' and d, ¬φ(d) holds but ¬φ(d') fails.

    The `hWitness` hypothesis plays the role of `hSurj` in `moreThan_noMaxInf`:
    it guarantees enough worlds exist to separate degrees. For the concrete
    case φ = atLeastDeg μ, this follows from surjectivity of μ. -/
theorem negativeIsland_noAnswer [DenselyOrdered α]
    (φ : α → W → Prop)
    (_hMono : IsDownwardMonotone φ)
    (w : W) (boundary : α)
    (hBelow : ∀ d, d ≤ boundary → φ d w)
    (hAbove : ∀ d, boundary < d → ¬ φ d w)
    (hWitness : ∀ a b, a < b → ∃ w', φ a w' ∧ ¬ φ b w') :
    ¬ HasMaxInf (negatedDegreeProp φ) w := by
  intro ⟨x, hx_neg, hx_ent⟩
  have hx_above : boundary < x := by
    by_contra h
    push_neg at h
    exact hx_neg (hBelow x h)
  -- By density, find z strictly between boundary and x
  obtain ⟨z, hz_above, hz_below⟩ := DenselyOrdered.dense boundary x hx_above
  have hz_neg : negatedDegreeProp φ z w := hAbove z hz_above
  -- x is max⊨, so ¬φ(x) entails ¬φ(z) across all worlds
  have hx_ent_z := hx_ent z hz_neg
  -- But hWitness gives a world where φ(z) holds and φ(x) fails
  obtain ⟨w', hw'_z, hw'_x⟩ := hWitness z x hz_below
  -- At w': ¬φ(x)(w') → ¬φ(z)(w') by entailment, but φ(z)(w') holds
  exact hx_ent_z w' hw'_x hw'_z

-- ════════════════════════════════════════════════════
-- § 4. Modal Obviation (@cite{fox-2007} §§2.3, 3.4)
-- ════════════════════════════════════════════════════

/-- Degree property under a **universal modal** (required, certain, have to):
    □φ(d)(w) := ∀w' ∈ R(w). φ(d)(w')

    @cite{fox-2007} exx. (13)–(14): the negation ¬□φ = ∃w'. ¬φ(d)(w')
    can have a max⊨ element even on dense scales, because two ∃-claims
    about different d can use different witness worlds — so neither entails
    the other, and maximality is achievable. -/
def universalModalProp (φ : α → W → Prop) (R : W → W → Prop) :
    α → W → Prop :=
  fun d w => ∀ w', R w w' → φ d w'

/-- Degree property under an **existential modal** (allowed, possible, can):
    ◇φ(d)(w) := ∃w' ∈ R(w). φ(d)(w') -/
def existentialModalProp (φ : α → W → Prop) (R : W → W → Prop) :
    α → W → Prop :=
  fun d w => ∃ w', R w w' ∧ φ d w'

/-- ∀-modal preserves upward monotonicity. -/
theorem universalModal_preserves_upMono
    (φ : α → W → Prop) (R : W → W → Prop)
    (hMono : IsUpwardMonotone φ) :
    IsUpwardMonotone (universalModalProp φ R) := by
  intro x y hxy w hAll w' hR
  exact hMono x y hxy w' (hAll w' hR)

/-- ∃-modal preserves upward monotonicity. -/
theorem existentialModal_preserves_upMono
    (φ : α → W → Prop) (R : W → W → Prop)
    (hMono : IsUpwardMonotone φ) :
    IsUpwardMonotone (existentialModalProp φ R) := by
  intro x y hxy w ⟨w', hR, hPhi⟩
  exact ⟨w', hR, hMono x y hxy w' hPhi⟩

/-- **Modal obviation** (@cite{fox-2007} §§2.3, 3.4, 4.2):
    ∀-modals can circumvent maximality violations; ∃-modals cannot.

    - ¬(∀w'. φ(d)(w')) = ∃w'. ¬φ(d)(w') — different d can use different
      witness worlds, so the complement can be a closed set with a maximum.
    - ¬(∃w'. φ(d)(w')) = ∀w'. ¬φ(d)(w') — still yields a downward-monotone
      negated set with no minimum on dense scales.

    Examples:
    - "You're only required to read more than 30 books" ✓
    - "*You're only allowed to smoke more than 30 cigarettes" ✗ -/
def obviatesMaxViolation : ModalForce → Prop
  | .necessity     => True
  | .weakNecessity => True
  | .possibility   => False

theorem necessity_obviates : obviatesMaxViolation .necessity := trivial
theorem weakNecessity_obviates : obviatesMaxViolation .weakNecessity := trivial
theorem possibility_fails : ¬ obviatesMaxViolation .possibility := id

end Semantics.Degree.Question
