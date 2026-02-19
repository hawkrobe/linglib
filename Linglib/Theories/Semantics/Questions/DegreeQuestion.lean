import Linglib.Core.Scale
import Linglib.Core.ModalLogic

/-!
# Degree Questions and the Universal Density of Measurement

Fox & Hackl (2007) "The universal density of measurement"
(*Linguistics and Philosophy* 29:537–586).

## Core Claim

Degree questions, definite descriptions, and scalar implicatures all involve
the same maximality requirement (`Core.Scale.HasMaxInf`). When the relevant
scale is dense (`[DenselyOrdered α]`), this requirement
interacts with negation and modals to produce systematic acceptability patterns.

## The Unification

Fox & Hackl show that four apparently distinct constructions reduce to
`HasMaxInf` applied to a degree property φ:

| Construction                          | Formulation                         |
|---------------------------------------|-------------------------------------|
| Degree question "How much φ?"         | HasMaxInf φ w (Rullmann 1995)       |
| Definite "the amount that φ"          | HasMaxInf φ w (Link 1983 maximality)|
| Only/EXH "only φ"                     | HasMaxInf φ w (OIG, F&H eq. 6)     |
| Implicature of bare "φ"              | HasMaxInf φ w (covert EXH)         |

All four fail when `HasMaxInf φ w` is unsatisfiable — which happens precisely
when φ describes an open set on a dense scale (no infimum/supremum).

## What This File Formalizes

The *new* content beyond `Core.Scale` (which provides degree properties
`atLeastDeg`, `moreThanDeg`, etc. and their HasMaxInf/density theorems):

1. **Negative islands**: negation of an upward-monotone property on a dense
   scale yields an open complement with no max⊨ element
2. **Modal obviation**: ∀-modals rescue maximality violations, ∃-modals don't
3. **Monotonicity preservation** through modals

Degree properties (`eqDeg`, `atLeastDeg`, `moreThanDeg`, `atMostDeg`,
`lessThanDeg`), their monotonicity, HasMaxInf theorems, Kennedy–F&H bridge,
and discrete–dense divergence theorems are in `Core.Scale` (§ 6 of
`Core/MeasurementScale.lean`).

## References

- Fox, D. & Hackl, M. (2007). The universal density of measurement. L&P 29:537–586.
- Rullmann, H. (1995). Maximality in the Semantics of Wh-Constructions. UMass diss.
- Beck, S. & Rullmann, H. (1999). A flexible approach to exhaustivity in questions.
- Link, G. (1983). The logical analysis of plurals and mass terms.
-/

namespace Semantics.Questions.DegreeQuestion

open Core.Scale
open Core.ModalLogic (ModalForce)

variable {α W : Type*} [LinearOrder α]

-- ════════════════════════════════════════════════════
-- § 1. Negative Islands (Fox & Hackl 2007 §3)
-- ════════════════════════════════════════════════════

/-- The **negated degree property**: ¬φ(d)(w).

    Example: φ(d)(w) = "John weighs ≥ d pounds in w"
    negated: "John does not weigh ≥ d pounds in w" -/
def negatedDegreeProp (φ : α → W → Prop) : α → W → Prop :=
  fun d w => ¬ φ d w

/-- **Negative island theorem** (Fox & Hackl 2007 §3.3):

    "*How much does John not weigh?" is unacceptable because on a dense
    scale, the negated set {d | ¬φ(d)(w)} has no maximally informative element.

    Setup: φ is upward monotone (e.g., "weighs ≥ d"). At world w, there is
    a boundary below which φ holds and above which it fails. Density ensures
    that for any d in the negated set, there exists d' strictly between the
    boundary and d that is also in the negated set — and ¬φ(d) does not
    entail ¬φ(d'), because in a world where the boundary moves up past d'
    (but stays below d), ¬φ(d) still holds but ¬φ(d') fails.

    The proof requires constructing witness worlds; the key mathematical
    fact is that open intervals in dense orders have no minimum. -/
theorem negativeIsland_noAnswer [DenselyOrdered α]
    (φ : α → W → Prop)
    (_hMono : IsUpwardMonotone φ)
    (w : W) (boundary : α)
    (hBelow : ∀ d, d ≤ boundary → φ d w)
    (hAbove : ∀ d, boundary < d → ¬ φ d w) :
    ¬ HasMaxInf (negatedDegreeProp φ) w := by
  intro ⟨x, hx_neg, hx_ent⟩
  have hx_above : boundary < x := by
    by_contra h
    push_neg at h
    exact hx_neg (hBelow x h)
  obtain ⟨z, hz_above, hz_below⟩ := DenselyOrdered.dense boundary x hx_above
  have hz_neg : negatedDegreeProp φ z w := hAbove z hz_above
  -- x is max⊨, so ¬φ(x) entails ¬φ(z) across all worlds.
  -- But in a world where the boundary sits between z and x,
  -- ¬φ(x) holds while ¬φ(z) may fail.
  -- Completing this requires constructing such a witness world.
  sorry -- TODO: requires witness world with boundary between z and x

-- ════════════════════════════════════════════════════
-- § 2. Modal Obviation (Fox & Hackl 2007 §§2.3, 3.4)
-- ════════════════════════════════════════════════════

/-- Degree property under a **universal modal** (required, certain, have to):
    □φ(d)(w) := ∀w' ∈ R(w). φ(d)(w')

    Fox & Hackl (2007) exx. (13)–(14): the negation ¬□φ = ∃w'. ¬φ(d)(w')
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

/-- **Modal obviation** (Fox & Hackl 2007 §§2.3, 3.4, 4.2):
    ∀-modals can circumvent maximality violations; ∃-modals cannot.

    - ¬(∀w'. φ(d)(w')) = ∃w'. ¬φ(d)(w') — different d can use different
      witness worlds, so the complement can be a closed set with a maximum.
    - ¬(∃w'. φ(d)(w')) = ∀w'. ¬φ(d)(w') — still yields a downward-monotone
      negated set with no minimum on dense scales.

    Examples:
    - "You're only required to read more than 30 books" ✓
    - "*You're only allowed to smoke more than 30 cigarettes" ✗ -/
def obviatesMaxViolation : ModalForce → Bool
  | .necessity => true
  | .possibility => false

theorem necessity_obviates : obviatesMaxViolation .necessity = true := rfl
theorem possibility_fails : obviatesMaxViolation .possibility = false := rfl

end Semantics.Questions.DegreeQuestion
