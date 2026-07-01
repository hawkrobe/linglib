/-
# Gradable Adjective Infrastructure

Types and operations for gradable adjective semantics (tall, happy, expensive).

## Key Components

- `NegationType`: Contradictory vs. contrary antonyms
- `ThresholdPair`: Two thresholds for contrary antonyms with gap
- `GradableAdjective`: the gradable adjective — syntactic `Adjective` + degree semantics
- `InformationalStrength`: Weak/strong adjective distinction
- Negation and gap-region predicates

## Architecture

Core degree types (`Degree`, `Threshold`) live in `Core.MeasurementScale`.
The canonical threshold semantics (`positiveMeaning`, `negativeMeaning`) live
in `Semantics/Degree/Basic.lean`. This module adds adjective-specific
infrastructure on top: antonymy, two-threshold models, and lexical entries.

For the adjective classification hierarchy (intersective, subsective, privative,
extensional), see `Classification.lean`.
-/

import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.DirectedMeasure
import Linglib.Semantics.Degree.Bounds
import Linglib.Semantics.Degree.HasMeasure
import Linglib.Features.PropertyDomain
import Linglib.Semantics.Gradability.Dimension
import Linglib.Features.Antonymy
import Linglib.Features.Valence
import Linglib.Semantics.Gradability.MLScale
import Linglib.Semantics.Degree.Basic
import Linglib.Semantics.Degree.Kennedy
import Linglib.Syntax.Adjective.Basic

namespace Semantics.Gradability

open Core.Order (Boundedness)
open Semantics.Degree (Degree Threshold Degree.toNat Threshold.toNat deg thr allDegrees allThresholds)
open Semantics.Degree (PositiveStandard AdjectiveClass interpretiveEconomy)
open Features (NegationType)

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

instance {n : Nat} [NeZero n] : Inhabited (ThresholdPair n) :=
  have h : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
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
abbrev contradictoryNeg {max : Nat} (d : Degree max) (θ : Threshold max) : Prop :=
  Semantics.Degree.antonymMeaning d θ

/-- Contrary negation: "unhappy" = degree < theta_neg.
    Alias for `Semantics.Degree.negativeMeaning`. -/
abbrev contraryNeg {max : Nat} (d : Degree max) (θ_neg : Threshold max) : Prop :=
  Semantics.Degree.negativeMeaning d θ_neg

/-- Check if a degree is in the gap region (neither positive nor negative). -/
abbrev inGapRegion {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Prop :=
  (tp.neg : Degree max) ≤ d ∧ d ≤ (tp.pos : Degree max)

/-- Positive meaning in the two-threshold model: degree > theta_pos.
    Alias for `Semantics.Degree.positiveMeaning` projected through `tp.pos`. -/
abbrev positiveMeaning' {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Prop :=
  Semantics.Degree.positiveMeaning d tp.pos

/-- Negative meaning in the two-threshold model: degree < theta_neg.
    Alias for `Semantics.Degree.negativeMeaning` projected through `tp.neg`. -/
abbrev contraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Prop :=
  Semantics.Degree.negativeMeaning d tp.neg

/-- Negation of contrary negative: "not unhappy" = degree >= theta_neg. -/
abbrev notContraryNegMeaning {max : Nat} (d : Degree max) (tp : ThresholdPair max) : Prop :=
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

Source: [alexandropoulou-gotzner-2024], [horn-1972]
-/
inductive InformationalStrength where
  | weak    -- large, small, clean, dirty
  | strong  -- gigantic, tiny, pristine, filthy
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- Adjective Lexical Entry
-- ════════════════════════════════════════════════════

/-- Spatial configuration type for adjectives in resultative constructions
    ([levin-2026]). Only adjectives describing spatially instantiated
    states license intr-*push open* resultatives. -/
inductive SpatialConfigType where
  | barrierConfig   -- open, closed, shut: config relative to frame
  | unattachment    -- free, loose: freedom from spatial contiguity
  | surfaceOrient   -- flat: orientation relative to reference surface
  deriving DecidableEq, Repr

/-- A **gradable adjective**: the syntactic `Adjective` (`Syntax/Adjective`) refined
    with the degree-**semantic** layer that becomes relevant in this module — the
    Kennedy `standardOverride`, and the lexical-semantic facets `antonymRelation`,
    resultative `spatialConfigType` ([levin-2026]), and `evaluativeValence`
    ([nouwen-2024]). The scale shape (`scaleType`), positive `standard`, and Kennedy
    `adjectiveClass` are *derived views* below — the fix for the old stored `scaleType`
    that conflated scale shape with pole (`wet`/`dry` share one closed `.wetness`
    scale, differing only in pole). -/
structure GradableAdjective extends Adjective where
  /-- Override the Kennedy default standard (the `good`/MPA residual: an open-shape
      scale that nonetheless takes a functional/contextual standard, [beltrama-2025]).
      `none` = take the derived default. -/
  standardOverride : Option PositiveStandard := none
  /-- Lexical antonym's logical relation (contrary vs contradictory). -/
  antonymRelation : Option AntonymRelation := none
  /-- Resultative spatial-configuration class ([levin-2026]). -/
  spatialConfigType : Option SpatialConfigType := none
  /-- Evaluative valence of the adjective, when applicable.
      Determines intensifier degree class ([nouwen-2024]):
      negative-evaluative bases yield H-degree intensifiers,
      positive-evaluative bases yield M-degree intensifiers. -/
  evaluativeValence : Option Features.EvaluativeValence := none
  deriving Repr

namespace GradableAdjective

/-- The scale's intrinsic shape — read off the `dimension` key, not stored
    (`.open_` for a non-gradable, which has no scale). -/
def scaleType (g : GradableAdjective) : Boundedness :=
  (g.dimension.map Dimension.boundedness).getD .open_

/-- The effective positive standard: the default from (scale shape, pole),
    overridable by `standardOverride`. This is the quantity the old `scaleType` field
    conflated — it separates `wet` (closed + lower ⇒ min) from `dry` (closed + upper ⇒
    max), and lets `good` (open shape) take a contextual standard rather than a bogus
    bound. ([kennedy-2007]'s Interpretive Economy on the open/singly-bounded cases.) -/
def standard (g : GradableAdjective) : PositiveStandard :=
  g.standardOverride.getD <|
    match g.dimension.map Dimension.boundedness, g.isLowerEndpoint with
    | some .closed, true  => .minEndpoint
    | some .closed, false => .maxEndpoint
    | some b,       _     => interpretiveEconomy b
    | none,         _     => .contextual

/-- Kennedy's adjective class — derived from `standard`, not stored; `.nonGradable`
    exactly when there is no `dimension` ([kennedy-2007], [kennedy-mcnally-2005]). -/
def adjectiveClass (g : GradableAdjective) : AdjectiveClass :=
  match g.dimension with
  | none => .nonGradable
  | some _ =>
    match g.standard with
    | .contextual  => .relativeGradable
    | .minEndpoint => .absoluteMinimum
    | .maxEndpoint => .absoluteMaximum
    | .functional  => .mildlyPositive

/-- Comparison-class dependence — the relative/absolute distinction, derived. -/
def IsRelative (g : GradableAdjective) : Prop := g.adjectiveClass.IsRelative

instance (g : GradableAdjective) : Decidable g.IsRelative := by
  unfold IsRelative; infer_instance

end GradableAdjective

-- ════════════════════════════════════════════════════
-- Multidimensional Adjective Semantics
-- ════════════════════════════════════════════════════

/--
How a multidimensional adjective binds its dimensions ([sassoon-2013]).

- **conjunctive**: entity must meet standard in ALL dimensions (e.g., *healthy*)
- **disjunctive**: entity must meet standard in SOME dimension (e.g., *sick*)
- **mixed**: context determines ∀ vs ∃ (e.g., *intelligent*)
-/
inductive DimensionBindingType where
  | conjunctive
  | disjunctive
  | mixed
  deriving Repr, DecidableEq

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
    This is the formal core of [sassoon-2013]'s Hypothesis 2 —
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

/-- [sassoon-2013] Hypothesis 3: standard type predicts binding type.
    Total (max standard) → conjunctive, partial (min standard) → disjunctive,
    relative (contextual) → mixed. -/
def predictedBinding : Semantics.Degree.PositiveStandard → DimensionBindingType
  | .maxEndpoint  => .conjunctive
  | .minEndpoint  => .disjunctive
  | .contextual   => .mixed
  | .functional   => .mixed   -- evaluative; context-dependent like contextual

-- ════════════════════════════════════════════════════
-- Marginality Scales Account ([dinis-jacinto-2026])
-- ════════════════════════════════════════════════════

open Core.Order
open Semantics.Degree
structure GradableMLScale (α : Type*) [LinearOrder α] (W : Type*) extends
    Semantics.Degree.DirectedMeasure α W where
  ml : Semantics.Gradability.MLScale α

def marginalityPositive {α : Type*} [LinearOrder α]
    (ml : Semantics.Gradability.MLScale α) (norm degree : α) : Prop :=
  ml.L norm degree

theorem marginality_entails_standard {α : Type*} [LinearOrder α]
    (ml : Semantics.Gradability.MLScale α) (norm degree : α)
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
    (entry : GradableAdjective) : DirectedMeasure (Degree max) W :=
  DirectedMeasure.adjective μ entry.scaleType

theorem closedAdj_licensed {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjective) (h : entry.scaleType = .closed) :
    (adjMeasure μ entry).IsLicensed := by
  simp [adjMeasure, DirectedMeasure.adjective,
        DirectedMeasure.IsLicensed, Boundedness.IsLicensed, h]

theorem openAdj_blocked {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjective) (h : entry.scaleType = .open_) :
    ¬ (adjMeasure μ entry).IsLicensed := by
  simp [adjMeasure, DirectedMeasure.adjective,
        DirectedMeasure.IsLicensed, Boundedness.IsLicensed, h]

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
    (DirectedMeasure.numeral μ).μ = μ :=
  rfl

end Semantics.Gradability
