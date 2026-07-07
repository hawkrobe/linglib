import Linglib.Core.Order.Boundedness

/-!
# Positive-form standards and Interpretive Economy

Kennedy's classification of gradable adjectives by scale structure, and the
derivation of standard type from scale boundedness [kennedy-2007]
[kennedy-mcnally-2005] [rotstein-winter-2004]. Interpretive Economy
([kennedy-2007] eq. (66)) maximises the contribution of conventional (scalar)
meaning: when a scale has the relevant endpoint, the contextual/relative
standard is ruled out in favour of the endpoint. A *totally closed* scale,
however, has both endpoints, and Interpretive Economy is silent on the choice
between them — such adjectives show interpretive variability (eq. (67)–(68),
*opaque/transparent*, *open/exposed*); out of context the maximum is preferred
on pragmatic grounds (a maximum standard entails a minimum one, and stronger
meanings are favoured).

## Main definitions

* `ieAdmits : Boundedness → PositiveStandard → Prop` — the standards
  Interpretive Economy admits for a scale; a totally closed scale admits *both*
  endpoint standards.
* `interpretiveEconomy : Boundedness → PositiveStandard` — the out-of-context
  *default* standard: the unique admitted standard where IE determines one, and
  the pragmatically preferred maximum for totally closed scales.
* `IsClassA` — relative (Class A) adjectives, those whose default standard
  requires a comparison class.

## Main theorems

* `ieAdmits_interpretiveEconomy` — the default standard is always IE-admissible.
* `ieAdmits_closed_minEndpoint`, `ieAdmits_closed_maxEndpoint` — interpretive
  variability of totally closed scales: IE admits *both* endpoints.
* `not_ieAdmits_contextual_of_isLicensed` — IE rules out the relative standard
  whenever the scale has an endpoint.
-/

namespace Degree

open Core.Order (Boundedness)

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

end Degree
