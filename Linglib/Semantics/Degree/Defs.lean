import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.DirectedMeasure
import Linglib.Semantics.Degree.HasMeasure

/-!
# Degree Semantics: Type Definitions

Pure type definitions for degree-based analyses of gradable expressions
[heim-2001] [kennedy-2007] [schwarzschild-2008] [beltrama-2025].
Positive-form semantics is in `Basic.lean`; Kennedy 2007's interpretive
economy classification is in `Kennedy.lean`. Klein-style delineation
[klein-1980] has no measure function and lives in
`Semantics/Gradability/Delineation.lean`.

## Main definitions

* `DegPType`, `StandardType` — DegP compositional taxonomy
* `ModifierDirection` — amplifier / downtoner axis
* `AdjectivalConstruction` — surface-construction type for evaluativity
* `PositiveStandard`, `AdjectiveClass` — Kennedy-style classification carriers
-/

namespace Semantics.Degree

open Core.Order (Boundedness)

/-- The compositional structure of a Degree Phrase (DegP).

In all degree frameworks, DegP is the syntactic locus where degree
comparison happens. The internal structure varies — Kennedy posits
`[DegP [Deg -er/as/est] [DegComplement than-clause]]`, Heim posits a
sentential `-er` operator — but the framework-independent taxonomy is
captured here. -/
inductive DegPType where
  /-- `-er` / *more*. -/
  | comparative
  /-- `as...as`. -/
  | equative
  /-- `-est` / *most*. -/
  | superlative
  /-- *too*. -/
  | excessive
  /-- *enough*. -/
  | sufficiency
  deriving DecidableEq, Repr

/-- The standard of comparison: what the degree is compared to. -/
inductive StandardType where
  /-- "taller than Bill" — explicit standard. -/
  | explicit
  /-- "tall" — contextually determined standard. -/
  | contextual
  /-- "full" — scale endpoint as standard. -/
  | absolute
  deriving DecidableEq, Repr

/-- Degree modifier direction — the same axis as NPI scalar direction.
Lexical instantiations of named modifiers (*slightly*, *very*, *quite*,
etc.) live in consuming Studies files. -/
inductive ModifierDirection where
  /-- *very*, *extremely* — raises the threshold. -/
  | amplifier
  /-- *slightly*, *kind of* — lowers the threshold. -/
  | downtoner
  deriving DecidableEq, Repr

/-- Degree construction type. Used by evaluativity analyses to track which
surface constructions trigger evaluative readings. -/
inductive AdjectivalConstruction where
  /-- "Kim is tall" — unmarked form. -/
  | positive
  /-- "Kim is taller than Sam". -/
  | comparative
  /-- "Kim is as tall as Sam". -/
  | equative
  /-- "Kim is 6 feet tall" — explicit measure phrase. -/
  | measurePhrase
  /-- "How tall is Kim?". -/
  | degreeQuestion
  deriving Repr, DecidableEq

/-- User-facing rendering, distinct from `Repr` (which prefixes the
namespace). Consumed by Studies files that string-interpolate construction
names into diagnostic messages — see e.g.
`Studies/Rett2015Implicature.lean`. -/
instance : ToString AdjectivalConstruction where
  toString
    | .positive => "positive"
    | .comparative => "comparative"
    | .equative => "equative"
    | .measurePhrase => "measurePhrase"
    | .degreeQuestion => "degreeQuestion"

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
  *deceased*, *pregnant*. Outside the gradable (`DirectedMeasure`) system;
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

end Semantics.Degree
