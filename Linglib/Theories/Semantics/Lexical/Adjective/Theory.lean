/-
# Gradable Adjective Theory Infrastructure

This module defines the `AdjectiveTheory` structure for organizing semantic
analyses of gradable adjectives (tall, happy, expensive, etc.).

## Key Issues

Gradable adjectives raise several semantic questions:

1. **Vagueness**: What counts as "tall"? Context-dependent threshold.
2. **Comparison**: "John is taller than Mary" — comparative morphology.
3. **Degree modification**: "very tall", "slightly happy" — degree operators.
4. **Antonymy**: Is "short" the contradictory or contrary of "tall"?

## Architecture

Core degree types (`Degree`, `Threshold`) live in `Core.MeasurementScale`.
This module adds adjective-specific infrastructure:
- `NegationType`: Contradictory vs. contrary antonyms
- `ThresholdPair`: Two thresholds for contrary antonyms with gap
- Negation semantics functions
- Degree modifiers

## Relationship to Degree.Core

This module uses concrete `Degree max` (= `Fin (max+1)`) for computation
in RSA models and Fragment entries. `Degree.Core` uses abstract types
(`Entity D : Type*` with `LinearOrder D`) for framework-level theorems.
See also `Degree.Granularity` for granularity-sensitive degree morphology.

## Comparison with ModalTheory

| Aspect        | ModalTheory                        | AdjectiveTheory                    |
|---------------|------------------------------------|------------------------------------|
| Core types    | ModalForce, Proposition            | Degree, Threshold, NegationType    |
| Parameters    | Accessibility relation / backgrounds | Threshold(s), antonym type        |
| Key question  | What's the modal base?             | Where's the threshold? Contrary?   |

-/

import Linglib.Theories.Semantics.Montague.Basic
import Linglib.Core.Scales.Scale
import Linglib.Core.PropertyDomain
import Linglib.Theories.Semantics.Lexical.Adjective.MLScale
import Linglib.Theories.Semantics.Degree.Core

namespace Semantics.Lexical.Adjective

open Core.Scale (Boundedness Degree Threshold Degree.toNat Threshold.toNat
  deg thr allDegrees allThresholds)

-- ════════════════════════════════════════════════════
-- Negation Types: Contradictory vs. Contrary
-- ════════════════════════════════════════════════════

/--
Types of negation for gradable adjectives.

**Contradictories** (e.g., "happy" / "not happy"):
- Cannot both be true AND cannot both be false
- Exactly one must hold for any degree

**Contraries** (e.g., "happy" / "unhappy"):
- Cannot both be true BUT can both be false
- Gap region where neither holds

References:
- @cite{cruse-1986}. Lexical Semantics.
- @cite{horn-1989}. A Natural History of Negation.
- @cite{tessler-franke-2019}. Not unreasonable.
-/
inductive NegationType where
  | contradictory
  | contrary
  deriving Repr, DecidableEq, BEq

-- Two-Threshold Model for Contrary Antonyms

/--
A threshold pair for contrary antonyms.

For contrary pairs like happy/unhappy:
- theta_pos: threshold for positive form (degree > theta_pos -> "happy")
- theta_neg: threshold for negative form (degree < theta_neg -> "unhappy")
- Constraint: theta_neg <= theta_pos (gap exists when theta_neg < theta_pos)
-/
structure ThresholdPair (max : Nat) where
  pos : Threshold max
  neg : Threshold max
  gap_exists : neg ≤ pos := by decide
  deriving Repr

instance {n : Nat} (h : 0 < n := by omega) : Inhabited (ThresholdPair n) :=
  ⟨{ pos := ⟨⟨0, h⟩⟩, neg := ⟨⟨0, h⟩⟩, gap_exists := le_refl _ }⟩

instance {n : Nat} : BEq (ThresholdPair n) where
  beq t1 t2 := t1.pos == t2.pos && t1.neg == t2.neg

instance {n : Nat} : DecidableEq (ThresholdPair n) :=
  λ t1 t2 =>
    if hp : t1.pos = t2.pos then
      if hn : t1.neg = t2.neg then
        .isTrue (by
          rcases t1 with ⟨p1, n1, g1⟩
          rcases t2 with ⟨p2, n2, g2⟩
          dsimp at hp hn
          subst hp; subst hn
          exact congrArg _ (proof_irrel g1 g2))
      else
        .isFalse (λ h => hn (congrArg ThresholdPair.neg h))
    else
      .isFalse (λ h => hp (congrArg ThresholdPair.pos h))

-- ════════════════════════════════════════════════════
-- Negation Semantics
-- ════════════════════════════════════════════════════

/-- Contradictory negation: "not happy" = degree ≤ theta. -/
def contradictoryNeg {max : Nat} (d : Degree max) (θ : Threshold max) : Bool :=
  d ≤ (θ : Degree max)

/-- Contrary negation: "unhappy" = degree < theta_neg. -/
def contraryNeg {max : Nat} (d : Degree max) (θ_neg : Threshold max) : Bool :=
  d < (θ_neg : Degree max)

/-- Check if a degree is in the gap region (neither positive nor negative). -/
def inGapRegion {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  (tp.neg : Degree max) ≤ d && d ≤ (tp.pos : Degree max)

/-- Positive meaning with two-threshold model: degree > theta_pos. -/
def positiveMeaning' {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  (tp.pos : Degree max) < d

/-- Negative meaning with contrary semantics: "unhappy" = degree < theta_neg. -/
def contraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  d < (tp.neg : Degree max)

/-- Negation of contrary negative: "not unhappy" = degree >= theta_neg. -/
def notContraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Bool :=
  (tp.neg : Degree max) ≤ d

-- ════════════════════════════════════════════════════
-- Antonym Relations
-- ════════════════════════════════════════════════════

/-- The relation between a positive form and its antonym. -/
abbrev AntonymRelation := NegationType

-- ════════════════════════════════════════════════════
-- Adjective Lexical Entry
-- ════════════════════════════════════════════════════

/--
A gradable adjective lexical entry.

Bundles surface form, scale structure, and antonym information.
The actual threshold is NOT part of the lexical entry — it's contextual.
-/
structure GradableAdjEntry where
  form : String
  scaleType : Boundedness
  dimension : Core.Dimension
  antonymForm : Option String := none
  antonymRelation : Option AntonymRelation := none
  deriving Repr

-- ════════════════════════════════════════════════════
-- Adjective Theory
-- ════════════════════════════════════════════════════

/--
A semantic theory for gradable adjectives.

1. **Single threshold** (standard): "tall" = degree > θ
2. **Two threshold / Contrary** (Tessler & Franke): gap region
-/
structure AdjectiveTheory (max : Nat) where
  name : String
  citation : String
  supportsContrary : Bool
  positiveMeaning : Degree max → Threshold max → Bool
  contradictoryAntonym : Degree max → Threshold max → Bool
  contraryAntonym : Degree max → ThresholdPair max → Bool := λ _ _ => false

-- Standard Theory: Single Threshold

def standardTheory (max : Nat) : AdjectiveTheory max where
  name := "Standard Threshold"
  citation := "Kennedy (2007), Lassiter & Goodman (2017)"
  supportsContrary := false
  positiveMeaning := λ d θ => d.toNat > θ.toNat
  contradictoryAntonym := λ d θ => d.toNat ≤ θ.toNat

-- Contrary Theory: Two Thresholds

def contraryTheory (max : Nat) : AdjectiveTheory max where
  name := "Contrary Antonyms (Two Threshold)"
  citation := "Tessler & Franke (2020), Cruse (1986)"
  supportsContrary := true
  positiveMeaning := λ d θ => d.toNat > θ.toNat
  contradictoryAntonym := λ d θ => d.toNat ≤ θ.toNat
  contraryAntonym := λ d tp => d.toNat < tp.neg.toNat

-- Derived Operations

def AdjectiveTheory.inGap {max : Nat} (T : AdjectiveTheory max)
    (d : Degree max) (tp : ThresholdPair max) : Bool :=
  if T.supportsContrary then
    inGapRegion d tp
  else
    false

def AdjectiveTheory.negatedAntonym {max : Nat} (T : AdjectiveTheory max)
    (d : Degree max) (tp : ThresholdPair max) : Bool :=
  if T.supportsContrary then
    d.toNat ≥ tp.neg.toNat
  else
    T.positiveMeaning d tp.pos

-- Theorems

theorem standard_no_gap : (standardTheory 4).supportsContrary = false := rfl

theorem contrary_supports_gap : (contraryTheory 4).supportsContrary = true := rfl

def exampleDegree : Degree 4 := ⟨⟨2, by omega⟩⟩
def exampleThresholds : ThresholdPair 4 :=
  { pos := ⟨⟨3, by omega⟩⟩, neg := ⟨⟨2, by omega⟩⟩, gap_exists := by decide }

theorem example_in_gap : inGapRegion exampleDegree exampleThresholds = true := by native_decide

theorem standard_double_neg_cancels :
    (standardTheory 4).negatedAntonym exampleDegree exampleThresholds =
    (standardTheory 4).positiveMeaning exampleDegree exampleThresholds.pos := rfl

theorem contrary_double_neg_differs :
    (contraryTheory 4).negatedAntonym exampleDegree exampleThresholds = true ∧
    (contraryTheory 4).positiveMeaning exampleDegree exampleThresholds.pos = false := by
  native_decide

-- ════════════════════════════════════════════════════
-- Marginality Scales Account (@cite{dinis-jacinto-2026})
-- ════════════════════════════════════════════════════

open Core.Scale

structure GradableMLScale (α : Type*) [LinearOrder α] (W : Type*) extends
    Core.Scale.DirectedMeasure α W where
  ml : Semantics.Lexical.Adjective.MLScale α

def marginalityPositive {α : Type*} [LinearOrder α]
    (ml : Semantics.Lexical.Adjective.MLScale α) (norm degree : α) : Prop :=
  ml.L norm degree

theorem marginality_entails_standard {α : Type*} [LinearOrder α]
    (ml : Semantics.Lexical.Adjective.MLScale α) (norm degree : α)
    (h : marginalityPositive ml norm degree) : norm < degree :=
  h.1

-- ════════════════════════════════════════════════════
-- Degree ↔ DirectedMeasure Bridge
-- ════════════════════════════════════════════════════

/-! ### Connecting concrete `Degree max` to abstract `DirectedMeasure`

`Degree max` has `LinearOrder` and `BoundedOrder` (from `Core.MeasurementScale`),
so the abstract theorems in `MeasurementScale.lean` apply directly to concrete
RSA degree computations. -/

def adjMeasure {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjEntry) : DirectedMeasure (Degree max) W :=
  DirectedMeasure.kennedyAdjective μ entry.scaleType

theorem closedAdj_licensed {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjEntry) (h : entry.scaleType = .closed) :
    (adjMeasure μ entry).licensed = true := by
  simp [adjMeasure, DirectedMeasure.kennedyAdjective,
        DirectedMeasure.licensed, Boundedness.isLicensed, h]

theorem openAdj_blocked {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjEntry) (h : entry.scaleType = .open_) :
    (adjMeasure μ entry).licensed = false := by
  simp [adjMeasure, DirectedMeasure.kennedyAdjective,
        DirectedMeasure.licensed, Boundedness.isLicensed, h]

theorem degree_nontrivial {max : Nat} (h : 1 ≤ max) :
    ∃ x : Degree max, x ≠ ⊤ := by
  refine ⟨⟨⟨0, by omega⟩⟩, ?_⟩
  intro heq
  simp [Top.top, Fin.last, Degree.mk.injEq] at heq
  omega

theorem degree_admits_optimum {max : Nat} (h : 1 ≤ max) :
    ∃ (P : Degree max → Prop),
      (∀ x y : Degree max, x ≤ y → P x → P y) ∧
      ¬ (∀ x y : Degree max, P x ↔ P y) :=
  upperBound_admits_optimum (degree_nontrivial h)

theorem degree_measure_is_id {max : Nat} {W : Type*} (μ : W → Degree max) :
    (DirectedMeasure.kennedyNumeral μ).μ = μ :=
  rfl

end Semantics.Lexical.Adjective
