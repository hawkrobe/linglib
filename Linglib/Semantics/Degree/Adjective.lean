import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.Measure.Polar
import Linglib.Features.ScalarDimension
import Linglib.Features.Antonymy
import Linglib.Features.Valence
import Linglib.Semantics.Degree.Discrete
import Linglib.Syntax.Adjective.Basic

/-!
# Gradable adjectives

Adjective-specific degree semantics, layered on the syntactic `Adjective`
(`Syntax/Adjective`): the `GradableAdjective` lexeme with its derived Kennedy
classification, the two-threshold model for contrary antonyms, multidimensional
binding ([sassoon-2013]), and the bridge from a concrete `Degree` scale to the
abstract `PolarMeasure`.

## Main definitions

* `GradableAdjective` — a syntactic `Adjective` refined with the degree-semantic
  layer; `scaleType`, `standard`, and `adjectiveClass` are derived views.
* `ThresholdPair` — the two thresholds of a contrary antonym pair, with a gap.
* `InformationalStrength` — the weak/strong distinction ([alexandropoulou-gotzner-2024]).
* `DimensionBindingType` — how a multidimensional adjective binds its dimensions.
* `adjMeasure` — a `GradableAdjective` read as a `PolarMeasure` over a scale.

Core degree types (`Degree`, `Threshold`) live in `Core.MeasurementScale`; the
threshold semantics (`positiveMeaning`, `negativeMeaning`) in `Semantics/Degree/Basic`.
The intersective/subsective/privative classification lives in `Classification.lean`.
-/

namespace Degree

open Core.Order (Boundedness)
open Features (NegationType ScalarDimension)

/-! ## Standards and Interpretive Economy ([kennedy-2007])

Absorbed from the retired `Standard.lean`: the classification of
gradable adjectives by scale structure and the derivation of standard
type from boundedness. Interpretive Economy ([kennedy-2007] eq. (66))
maximises the contribution of conventional meaning: a scale with an
endpoint rules out the contextual standard; a totally closed scale
admits *both* endpoint standards (`ieAdmits`) with the maximum as the
pragmatically preferred default (`interpretiveEconomy`). -/

/-! ### Classification carriers -/

/-- Positive form standard: how the contextual threshold is determined.
For open scales, the standard is the contextual norm
([kennedy-2007]); for closed scales, it is the relevant endpoint
fixed by Interpretive Economy. -/
inductive PositiveStandard where
  /-- Open-scale: θ = norm relative to comparison class. -/
  | contextual
  /-- Lower-bounded: θ = minimum (e.g., "bent", "wet"). -/
  | minEndpoint
  /-- Upper-bounded / closed: θ = maximum (e.g., "full", "dry"). -/
  | maxEndpoint
  /-- Necessity standard: θ = minimum value for pursuit ([beltrama-2025]). -/
  | functional
  deriving DecidableEq, Repr

/-- Whether the positive standard depends on contextual domain information.

[kennedy-2007] argues the comparison class is not a semantic argument
of *pos* (contra [klein-1980]), replacing it with the standard-fixing
function **s**: `⟦pos⟧ = λg.λx. g(x) ≥ s(g)`. For relative (open-scale)
adjectives, **s** still requires contextual domain information; for
absolute (closed-scale) adjectives the standard comes from scale
endpoints via Interpretive Economy. -/
def PositiveStandard.RequiresComparisonClass : PositiveStandard → Prop
  | .contextual  => True
  | .minEndpoint => False
  | .maxEndpoint => False
  | .functional  => True

instance : DecidablePred PositiveStandard.RequiresComparisonClass
  | .contextual  => inferInstanceAs (Decidable True)
  | .minEndpoint => inferInstanceAs (Decidable False)
  | .maxEndpoint => inferInstanceAs (Decidable False)
  | .functional  => inferInstanceAs (Decidable True)

/-- Kennedy's adjective classification by scale structure and standard
type [kennedy-2007] [kennedy-mcnally-2005], plus a
`nonGradable` case for adjectives outside the degree-based fragment. -/
inductive AdjectiveClass where
  /-- Standard varies with comparison class — *tall*, *expensive*, *big*. -/
  | relativeGradable
  /-- Threshold fixed at scale maximum — *full*, *straight*, *closed*, *dry*. -/
  | absoluteMaximum
  /-- Threshold fixed at scale minimum — *wet*, *bent*, *open*, *dirty*. -/
  | absoluteMinimum
  /-- Necessity-relative threshold — *decent*, *acceptable* ([beltrama-2025]). -/
  | mildlyPositive
  /-- Non-gradable: no degree argument, no scale — *atomic*, *prime*,
  *deceased*, *pregnant*. Outside the gradable (`PolarMeasure`) system;
  consumers that classify a general adjective should map non-gradables
  here rather than coercing them into a gradable class. -/
  | nonGradable
  deriving Repr, DecidableEq

/-- Coarse two-way classification: relative vs absolute. Collapses
`absoluteMaximum` and `absoluteMinimum`. -/
def AdjectiveClass.IsRelative (c : AdjectiveClass) : Prop :=
  c = .relativeGradable

instance : DecidablePred AdjectiveClass.IsRelative :=
  fun c => decEq c .relativeGradable


/-- The positive-form standards that Interpretive Economy *admits* for a scale.
IE maximises the contribution of conventional (scalar) meaning, so the
contextual/relative standard is admitted only on a totally open scale (which has
no endpoint to use). A one-sided closed scale admits its single endpoint; a
*totally closed* scale admits *both* endpoint standards — IE rules out the
relative reading but is silent on the min/max choice ([kennedy-2007] eq. (66),
the *opaque/transparent* and *open/exposed* cases of eq. (67)–(68)). -/
def ieAdmits : Boundedness → PositiveStandard → Prop
  | .open_,        s => s = .contextual
  | .lowerBounded, s => s = .minEndpoint
  | .upperBounded, s => s = .maxEndpoint
  | .closed,       s => s = .minEndpoint ∨ s = .maxEndpoint

instance (b : Boundedness) (s : PositiveStandard) : Decidable (ieAdmits b s) := by
  cases b <;> simp only [ieAdmits] <;> infer_instance

/-- The out-of-context *default* positive standard. Where Interpretive Economy
admits a unique standard (open / one-sided closed scales) this is forced; for a
totally closed scale IE admits both endpoints (`ieAdmits`) and the default is
the **maximum** on pragmatic grounds — a maximum standard entails a minimum one
and stronger meanings are preferred ([kennedy-2007] eq. (66) discussion). So
this is Interpretive Economy *plus* a strengthening default for closed scales,
not IE alone; the genuine (variable) IE claim is `ieAdmits`. -/
def interpretiveEconomy : Boundedness → PositiveStandard
  | .open_        => .contextual
  | .lowerBounded => .minEndpoint
  | .upperBounded => .maxEndpoint
  | .closed       => .maxEndpoint

theorem interpretiveEconomy_open : interpretiveEconomy .open_ = .contextual := rfl
theorem interpretiveEconomy_lowerBounded :
    interpretiveEconomy .lowerBounded = .minEndpoint := rfl
theorem interpretiveEconomy_upperBounded :
    interpretiveEconomy .upperBounded = .maxEndpoint := rfl

/-- The default standard for a totally closed scale is the maximum — a
*pragmatic* preference (stronger meaning), not an Interpretive-Economy
determination; the minimum is equally admitted (`ieAdmits_closed_minEndpoint`). -/
theorem interpretiveEconomy_closed : interpretiveEconomy .closed = .maxEndpoint := rfl

/-- The default standard is always among those Interpretive Economy admits. -/
theorem ieAdmits_interpretiveEconomy (b : Boundedness) :
    ieAdmits b (interpretiveEconomy b) := by
  cases b <;> simp [ieAdmits, interpretiveEconomy]

/-- Interpretive variability of totally closed scales: IE admits the **minimum**
standard, so the `interpretiveEconomy` maximum default is a pragmatic preference,
not a semantic determination ([kennedy-2007] eq. (67)–(68): *opaque/transparent*,
*open/exposed*). -/
theorem ieAdmits_closed_minEndpoint : ieAdmits .closed .minEndpoint := Or.inl rfl

/-- A totally closed scale also admits the maximum standard. -/
theorem ieAdmits_closed_maxEndpoint : ieAdmits .closed .maxEndpoint := Or.inr rfl


/-- Interpretive Economy rules out the relative (contextual) standard whenever
the scale has an endpoint (`Boundedness.IsLicensed`). -/
theorem not_ieAdmits_contextual_of_isLicensed {b : Boundedness}
    (h : b.IsLicensed) : ¬ ieAdmits b .contextual := by
  cases b <;> simp_all [ieAdmits, Boundedness.IsLicensed]

/-- A boundedness is *Class A* (relative) iff its default standard requires a
comparison class — i.e. iff the scale is open. Kennedy's *tall*, *expensive*,
*big*. -/
def IsClassA (b : Boundedness) : Prop :=
  (interpretiveEconomy b).RequiresComparisonClass

instance : DecidablePred IsClassA :=
  fun b => inferInstanceAs (Decidable (interpretiveEconomy b).RequiresComparisonClass)


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

/-- The entry-level selection implements the type-level theory: an
    override-free entry's derived `standard` is always among the standards
    Interpretive Economy admits for its scale shape. The closed-scale
    pole dispatch (min for lower-endpoint, max otherwise) picks within
    IE's admitted pair rather than beyond it. -/
theorem standard_ieAdmits (g : GradableAdjective)
    (h : g.standardOverride = none) :
    ieAdmits g.scaleType g.standard := by
  unfold standard scaleType
  rw [h]
  cases hd : g.dimension with
  | none => simp [ieAdmits]
  | some d =>
    cases hb : d.boundedness <;> cases hl : g.isLowerEndpoint <;>
      simp [ieAdmits, interpretiveEconomy, hd, hb, hl]

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

/-! ### Degree–PolarMeasure bridge

`Degree max` has `LinearOrder` and `BoundedOrder` (from `Core.MeasurementScale`), so the
abstract theorems in `MeasurementScale.lean` apply directly to concrete RSA degree
computations. -/

def adjMeasure {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjective) : PolarMeasure (Degree max) W :=
  PolarMeasure.adjective μ entry.scaleType

theorem closedAdj_licensed {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjective) (h : entry.scaleType = .closed) :
    (adjMeasure μ entry).IsLicensed := by
  simp [adjMeasure, PolarMeasure.adjective,
        PolarMeasure.IsLicensed, Boundedness.IsLicensed, h]

theorem openAdj_blocked {max : Nat} {W : Type*} (μ : W → Degree max)
    (entry : GradableAdjective) (h : entry.scaleType = .open_) :
    ¬ (adjMeasure μ entry).IsLicensed := by
  simp [adjMeasure, PolarMeasure.adjective,
        PolarMeasure.IsLicensed, Boundedness.IsLicensed, h]

theorem degree_measure_is_id {max : Nat} {W : Type*} (μ : W → Degree max) :
    (PolarMeasure.numeral μ).μ = μ :=
  rfl

end Degree
