/-
# Gradable Adjective Infrastructure

Types and operations for gradable adjective semantics (tall, happy, expensive).

## Key Components

- `NegationType`: Contradictory vs. contrary antonyms
- `ThresholdPair`: Two thresholds for contrary antonyms with gap
- `GradableAdjEntry`: Lexical entry bundling form + scale structure + antonym
- `InformationalStrength`: Weak/strong adjective distinction
- Negation and gap-region predicates

## Architecture

Core degree types (`Degree`, `Threshold`) live in `Core.MeasurementScale`.
The canonical threshold semantics (`positiveMeaning`, `negativeMeaning`) live
in `Theories/Semantics/Degree/Core.lean`. This module adds adjective-specific
infrastructure on top: antonymy, two-threshold models, and lexical entries.

For the adjective classification hierarchy (intersective, subsective, privative,
extensional), see `Classification.lean`.
-/

import Linglib.Theories.Semantics.Montague.Types
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

/-- Antonymy type: contradictory (no gap) vs contrary (gap).
    Canonical definition in `Core.PropertyDomain`. -/
abbrev NegationType := Core.NegationType

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

/-- Contradictory negation: "not happy" = degree ≤ theta.
    Alias for `Semantics.Degree.antonymMeaning` — same comparison,
    named for its role in the contradictory/contrary distinction. -/
abbrev contradictoryNeg {max : Nat} (d : Degree max) (θ : Threshold max) : Bool :=
  Semantics.Degree.antonymMeaning d θ

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
-- Informational Strength
-- ════════════════════════════════════════════════════

/--
Informational strength of a gradable adjective within its scale.

Weak adjectives (e.g., "large", "clean") occupy a broader region of the scale.
Strong adjectives (e.g., "gigantic", "pristine") occupy a narrower, more
extreme region.

A strong adjective entails its weak counterpart on the same pole:
"x is gigantic" ⟹ "x is large", but not vice versa.

This distinction is orthogonal to scale structure (relative vs absolute)
and polarity (positive vs negative).

Source: @cite{alexandropoulou-gotzner-2024}, @cite{horn-1972}
-/
inductive InformationalStrength where
  | weak    -- large, small, clean, dirty
  | strong  -- gigantic, tiny, pristine, filthy
  deriving Repr, DecidableEq, BEq

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
-- Multidimensional Adjective Semantics
-- ════════════════════════════════════════════════════

/--
How a multidimensional adjective binds its dimensions (@cite{sassoon-2013}).

- **conjunctive**: entity must meet standard in ALL dimensions (e.g., *healthy*)
- **disjunctive**: entity must meet standard in SOME dimension (e.g., *sick*)
- **mixed**: context determines ∀ vs ∃ (e.g., *intelligent*)
-/
inductive DimensionBindingType where
  | conjunctive
  | disjunctive
  | mixed
  deriving Repr, DecidableEq, BEq

variable {α : Type}

/-- Conjunctive binding: ∀Q ∈ DIM(P,c). Q(x). -/
def conjunctiveBinding (dims : List (α → Bool)) (x : α) : Bool :=
  dims.all (· x)

/-- Disjunctive binding: ∃Q ∈ DIM(P,c). Q(x). -/
def disjunctiveBinding (dims : List (α → Bool)) (x : α) : Bool :=
  dims.any (· x)

private theorem not_all_eq_any_not_map :
    ∀ (dims : List (α → Bool)) (x : α),
      (!dims.all (· x)) = (dims.map λ d a => !d a).any (· x)
  | [], _ => rfl
  | d :: ds, x => by
    simp only [List.all_cons, List.map_cons, List.any_cons]
    cases d x <;> simp [not_all_eq_any_not_map ds x]

private theorem not_any_eq_all_not_map :
    ∀ (dims : List (α → Bool)) (x : α),
      (!dims.any (· x)) = (dims.map λ d a => !d a).all (· x)
  | [], _ => rfl
  | d :: ds, x => by
    simp only [List.any_cons, List.map_cons, List.all_cons]
    cases d x <;> simp [not_any_eq_all_not_map ds x]

/-- De Morgan: negating conjunctive binding yields disjunctive binding
    over negated dimension predicates.
    This is the formal core of @cite{sassoon-2013}'s Hypothesis 2 —
    under a negation theory of antonymy, if the positive form is conjunctive,
    the negative antonym (its negation) is disjunctive. -/
theorem deMorgan_conjunctive_disjunctive
    (dims : List (α → Bool)) (x : α) :
    (!conjunctiveBinding dims x) =
      disjunctiveBinding (dims.map λ d a => !d a) x :=
  not_all_eq_any_not_map dims x

theorem deMorgan_disjunctive_conjunctive
    (dims : List (α → Bool)) (x : α) :
    (!disjunctiveBinding dims x) =
      conjunctiveBinding (dims.map λ d a => !d a) x :=
  not_any_eq_all_not_map dims x

/-- The predicted binding type for a negative antonym,
    given its positive counterpart's binding type.
    Follows from De Morgan under the negation theory of antonymy. -/
def DimensionBindingType.negate : DimensionBindingType → DimensionBindingType
  | .conjunctive => .disjunctive
  | .disjunctive => .conjunctive
  | .mixed       => .mixed

theorem negate_involutive (b : DimensionBindingType) :
    b.negate.negate = b := by cases b <;> rfl

/-- @cite{sassoon-2013} Hypothesis 3: standard type predicts binding type.
    Total (max standard) → conjunctive, partial (min standard) → disjunctive,
    relative (contextual) → mixed. -/
def predictedBinding : Semantics.Degree.PositiveStandard → DimensionBindingType
  | .maxEndpoint => .conjunctive
  | .minEndpoint => .disjunctive
  | .contextual  => .mixed

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
