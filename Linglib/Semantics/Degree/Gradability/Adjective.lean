import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.DirectedMeasure
import Linglib.Features.ScalarDimension
import Linglib.Features.Antonymy
import Linglib.Features.Valence
import Linglib.Semantics.Degree.Discrete
import Linglib.Semantics.Degree.Kennedy
import Linglib.Syntax.Adjective.Basic

/-!
# Gradable adjectives

Adjective-specific degree semantics, layered on the syntactic `Adjective`
(`Syntax/Adjective`): the `GradableAdjective` lexeme with its derived Kennedy
classification, the two-threshold model for contrary antonyms, multidimensional
binding ([sassoon-2013]), and the bridge from a concrete `Degree` scale to the
abstract `DirectedMeasure`.

## Main definitions

* `GradableAdjective` — a syntactic `Adjective` refined with the degree-semantic
  layer; `scaleType`, `standard`, and `adjectiveClass` are derived views.
* `ThresholdPair` — the two thresholds of a contrary antonym pair, with a gap.
* `InformationalStrength` — the weak/strong distinction ([alexandropoulou-gotzner-2024]).
* `DimensionBindingType` — how a multidimensional adjective binds its dimensions.
* `adjMeasure` — a `GradableAdjective` read as a `DirectedMeasure` over a scale.

Core degree types (`Degree`, `Threshold`) live in `Core.MeasurementScale`; the
threshold semantics (`positiveMeaning`, `negativeMeaning`) in `Semantics/Degree/Basic`.
The intersective/subsective/privative classification lives in `Classification.lean`.
-/

namespace Degree

open Core.Order (Boundedness)
open Features (NegationType ScalarDimension)

/-! ### Two-threshold model for contrary antonyms -/

/-- The two thresholds of a contrary antonym pair (*happy*/*unhappy*): `pos` for the
positive form (true when `degree > pos`) and `neg` for the negative form (true when
`degree < neg`). When `neg < pos` a gap region `[neg, pos]` — "neither" — lies between
them; that strict inequality is taken as a hypothesis where a gap is needed
(`contrary_gap_exists`, `gap_nonempty`), not stored as an invariant. -/
structure ThresholdPair (max : Nat) where
  pos : Threshold max
  neg : Threshold max
  deriving Repr, DecidableEq, BEq

/-! ### Negation semantics

The two-threshold model for contrary antonyms: the general threshold semantics of
`Semantics/Degree/Basic` (`positiveMeaning`/`negativeMeaning`/`notPositiveMeaning`) read
through a `ThresholdPair`'s two poles. -/

section TwoThreshold
variable {max : Nat} (d : Degree max)

/-- Contradictory negation *not happy* — `d ≤ θ` (`Degree.notPositiveMeaning`). -/
abbrev contradictoryNeg (θ : Threshold max) : Prop := Degree.notPositiveMeaning d θ

/-- Contrary negation *unhappy* — `d < θ_neg` (`Degree.negativeMeaning`). -/
abbrev contraryNeg (θ_neg : Threshold max) : Prop := Degree.negativeMeaning d θ_neg

/-- The gap region: `d` is neither positive nor negative (`neg ≤ d ≤ pos`). -/
abbrev inGapRegion (tp : ThresholdPair max) : Prop :=
  (tp.neg : Degree max) ≤ d ∧ d ≤ (tp.pos : Degree max)

/-- Positive form *happy* at the pair's upper threshold — `d > pos`. -/
abbrev positiveMeaning' (tp : ThresholdPair max) : Prop :=
  Degree.positiveMeaning d tp.pos

/-- Negative form *unhappy* at the pair's lower threshold — `d < neg`. -/
abbrev contraryNegMeaning (tp : ThresholdPair max) : Prop :=
  Degree.negativeMeaning d tp.neg

/-- *not unhappy* — the complement of the negative form (`neg ≤ d`). -/
abbrev notContraryNegMeaning (tp : ThresholdPair max) : Prop :=
  (tp.neg : Degree max) ≤ d

end TwoThreshold

/-! ### Antonym relations -/

/-- The relation between a positive form and its antonym. -/
abbrev AntonymRelation := NegationType

/-! ### Informational strength -/

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

/-! ### The gradable adjective -/

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
  (g.dimension.map ScalarDimension.boundedness).getD .open_

/-- The effective positive standard: the default from (scale shape, pole),
    overridable by `standardOverride`. This is the quantity the old `scaleType` field
    conflated — it separates `wet` (closed + lower ⇒ min) from `dry` (closed + upper ⇒
    max), and lets `good` (open shape) take a contextual standard rather than a bogus
    bound. ([kennedy-2007]'s Interpretive Economy on the open/singly-bounded cases.) -/
def standard (g : GradableAdjective) : PositiveStandard :=
  g.standardOverride.getD <|
    match g.dimension.map ScalarDimension.boundedness, g.isLowerEndpoint with
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

/-! ### Multidimensional adjectives ([sassoon-2013]) -/

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

section Binding
variable {α : Type*}

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

end Binding

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
def predictedBinding : Degree.PositiveStandard → DimensionBindingType
  | .maxEndpoint  => .conjunctive
  | .minEndpoint  => .disjunctive
  | .contextual   => .mixed
  | .functional   => .mixed   -- evaluative; context-dependent like contextual

/-! ### Degree–DirectedMeasure bridge

`Degree max` has `LinearOrder` and `BoundedOrder` (from `Core.MeasurementScale`), so the
abstract theorems in `MeasurementScale.lean` apply directly to concrete RSA degree
computations. -/

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

theorem degree_measure_is_id {max : Nat} {W : Type*} (μ : W → Degree max) :
    (DirectedMeasure.numeral μ).μ = μ :=
  rfl

end Degree
