import Linglib.Semantics.Degree.Boundedness
import Linglib.Semantics.Degree.Scale
import Linglib.Semantics.Degree.Antonymy
import Linglib.Semantics.Degree.Discrete
import Linglib.Syntax.Category.Adjective.Basic

/-!
# Gradable adjectives

Adjective-specific degree semantics, layered on the syntactic `Adjective`
(`Syntax/Category/Adjective`): the `GradableAdjective` lexeme with its derived Kennedy
classification, and multidimensional binding ([sassoon-2013]).

## Main definitions

* `GradableAdjective` — a syntactic `Adjective` refined with the degree-semantic
  layer; `scaleType`, `standard`, and `adjectiveClass` are derived views.
* `AntonymPair` — the two polar adjectives of one scale, entered once.
* `InformationalStrength` — the weak/strong distinction ([alexandropoulou-gotzner-2024b]).
* `DimensionBindingType` — how a multidimensional adjective binds its dimensions.

The finite degree carrier `Bounded`, its `Threshold`, and the threshold semantics
(`positiveMeaning`, `negativeMeaning`) live in `Semantics/Degree/Discrete`; the antonym
pair's polarity, relation and two-threshold model in `Semantics/Degree/Antonymy`.
The intersective/subsective/privative classification lives in
`Semantics/Modification/Classification.lean`.
-/

namespace Degree


/-! ## Standards and Interpretive Economy ([kennedy-2007])

Absorbed from the retired `Standard.lean`: the classification of
gradable adjectives by scale structure and the derivation of standard
type from boundedness. Interpretive Economy ([kennedy-2007] eq. (66))
maximises the contribution of conventional meaning: a scale with an
endpoint rules out the contextual standard; a totally closed scale
admits *both* endpoint standards (`Boundedness.Admits`) with the maximum as the
pragmatically preferred default (`Boundedness.defaultStandard`). -/

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
  *deceased*, *pregnant*. Outside the degree-based system;
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


/-- The positive-form standards Interpretive Economy admits for a scale ([kennedy-2007]
§4.2–§4.3): a maximal degree stands out on a scale with a maximum and a non-minimal degree on
one with a minimum, so an endpoint standard is available exactly where the scale has that
endpoint; the contextual standard, which context must supply, survives IE (66) only on a
totally open scale. A totally closed scale therefore admits both endpoints ((67)–(68)). -/
def Boundedness.Admits (b : Boundedness) : PositiveStandard → Prop
  | .contextual  => b = .open_
  | .minEndpoint => b.HasMin
  | .maxEndpoint => b.HasMax
  | .functional  => False

instance (b : Boundedness) (s : PositiveStandard) : Decidable (b.Admits s) := by
  cases s <;> simp only [Boundedness.Admits] <;> infer_instance

/-- The out-of-context default standard, Interpretive Economy plus a strengthening
preference: where one standard is admitted it is forced, and a totally closed scale takes the
maximum (a maximum standard entails a minimum one). -/
def Boundedness.defaultStandard : Boundedness → PositiveStandard
  | .open_        => .contextual
  | .lowerBounded => .minEndpoint
  | .upperBounded => .maxEndpoint
  | .closed       => .maxEndpoint

/-- The default standard is always admitted. -/
theorem Boundedness.admits_defaultStandard (b : Boundedness) : b.Admits b.defaultStandard := by
  cases b <;> decide

/-- A totally closed scale admits the minimum standard as well as the default maximum
([kennedy-2007] (67)–(68)). -/
theorem Boundedness.closed_admits_minEndpoint : Boundedness.closed.Admits .minEndpoint := trivial

theorem Boundedness.closed_admits_maxEndpoint : Boundedness.closed.Admits .maxEndpoint := trivial

/-- Interpretive Economy rules out the contextual standard whenever the scale has an endpoint. -/
theorem Boundedness.not_admits_contextual_of_ne_open {b : Boundedness} (h : b ≠ .open_) :
    ¬ b.Admits .contextual := h

/-- A scale is relative iff its default standard needs a comparison class, i.e. iff it is open
(*tall*, *expensive*, *big*). -/
def Boundedness.IsRelative (b : Boundedness) : Prop := b.defaultStandard.RequiresComparisonClass

instance : DecidablePred Boundedness.IsRelative :=
  fun b => inferInstanceAs (Decidable b.defaultStandard.RequiresComparisonClass)

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

Source: [alexandropoulou-gotzner-2024b], [horn-1972]
-/
inductive InformationalStrength where
  | weak    -- large, small, clean, dirty
  | strong  -- gigantic, tiny, pristine, filthy
  deriving Repr, DecidableEq

/-! ### Evaluative valence -/

/-- The evaluative valence of a gradable predicate: whether it denotes a good, a bad, or an
evaluatively neutral property ([nouwen-2024]), distinct from scalar polarity. Negative
valence yields high-degree intensifiers and positive valence medium-degree ones, the
Goldilocks effect. -/
inductive EvaluativeValence where
  | positive
  | negative
  | neutral
  deriving Repr, DecidableEq

/-- The valence of the opposite pole of an antonym pair: positive and negative swap, neutral
stays. -/
def EvaluativeValence.flip : EvaluativeValence → EvaluativeValence
  | .positive => .negative
  | .negative => .positive
  | .neutral => .neutral

/-! ### The gradable adjective -/

/-- Spatial configuration type for adjectives in resultative constructions
    ([levin-2026]). Only adjectives describing spatially instantiated
    states license intr-*push open* resultatives. -/
inductive SpatialConfigType where
  | barrierConfig   -- open, closed, shut: config relative to frame
  | unattachment    -- free, loose: freedom from spatial contiguity
  | surfaceOrient   -- flat: orientation relative to reference surface
  deriving DecidableEq, Repr

/-- A **gradable adjective**: the syntactic `Adjective` (`Syntax/Category/Adjective`) refined
    with the degree-**semantic** layer that becomes relevant in this module — the
    Kennedy `standardOverride`, and the lexical-semantic fields `antonymRelation`,
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
  evaluativeValence : Option EvaluativeValence := none
  deriving Repr

namespace GradableAdjective

/-- The scale the adjective measures on: its dimension's, dualized for the negative member of
an antonym pair (`.open_` for a non-gradable, which has no scale). -/
def scaleType (g : GradableAdjective) : Boundedness :=
  (g.dimension.map λ d => g.polarity • d.boundedness).getD .open_

/-- The positive standard: the scale's default, unless overridden (the *good*/MPA residual). -/
def standard (g : GradableAdjective) : PositiveStandard :=
  g.standardOverride.getD g.scaleType.defaultStandard

/-- An override-free entry's standard is one its scale admits. -/
theorem admits_standard (g : GradableAdjective) (h : g.standardOverride = none) :
    g.scaleType.Admits g.standard := by
  simp [standard, h, Boundedness.admits_defaultStandard]

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

/-! ### Antonym pairs -/

/-- An **antonym pair**: the positive and the negative polar adjective of one scale, each the
other's lexical antonym under one relation. The shared data is stored once; the two gradable
adjectives are `AntonymPair.pos` and `AntonymPair.neg`. -/
structure AntonymPair where
  /-- The scale both poles measure on. -/
  dimension : ScalarDimension
  /-- The logical relation between the poles. -/
  relation : AntonymRelation
  /-- The positive pole's surface form. -/
  posForm : String
  /-- The negative pole's surface form. -/
  negForm : String
  /-- The positive pole's comparison paradigm. -/
  posComparison : Adjective.Comparison := .regular
  /-- The negative pole's comparison paradigm. -/
  negComparison : Adjective.Comparison := .regular
  /-- The positive pole's evaluative valence; the negative pole's is its `flip`. -/
  valence : Option EvaluativeValence := none
  /-- The resultative spatial-configuration class the poles share. -/
  spatialConfigType : Option SpatialConfigType := none

namespace AntonymPair

/-- The positive pole. -/
def pos (p : AntonymPair) : GradableAdjective where
  form := p.posForm
  dimension := some p.dimension
  comparison := p.posComparison
  antonymForm := some p.negForm
  antonymRelation := some p.relation
  evaluativeValence := p.valence
  spatialConfigType := p.spatialConfigType

/-- The negative pole, measuring on the dual scale. -/
def neg (p : AntonymPair) : GradableAdjective where
  form := p.negForm
  polarity := .negative
  dimension := some p.dimension
  comparison := p.negComparison
  antonymForm := some p.posForm
  antonymRelation := some p.relation
  evaluativeValence := p.valence.map EvaluativeValence.flip
  spatialConfigType := p.spatialConfigType

@[simp] theorem pos_polarity (p : AntonymPair) : p.pos.polarity = .positive := rfl

@[simp] theorem neg_polarity (p : AntonymPair) : p.neg.polarity = .negative := rfl

/-- The poles name each other as antonyms. -/
@[simp] theorem pos_antonymForm (p : AntonymPair) : p.pos.antonymForm = some p.neg.form := rfl

@[simp] theorem neg_antonymForm (p : AntonymPair) : p.neg.antonymForm = some p.pos.form := rfl

end AntonymPair

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

end Degree
