import Linglib.Theories.Syntax.Minimalism.Agree
import Linglib.Core.Polarity

/-!
# Syntactic Polarity: PolP and [±Pol]
@cite{holmberg-2016} @cite{laka-1990}

Syntactic polarity as a formal feature on the PolP functional head,
connecting @cite{laka-1990}'s ΣP and @cite{holmberg-2016}'s analysis
of yes/no answers.

## Key Claims

1. Every finite clause has a polarity head (Pol⁰) projecting PolP in the IP domain
2. In declaratives, [±Pol] is valued: [+Pol] for affirmative, [-Pol] for negative
3. In polar questions, [±Pol] is unvalued — the answer values it
4. "Yes"/"No" are focus-movement remnants of PolP ellipsis under identity

## Connection to Core.Polarity

`Core.Polarity` provides the semantic type (`.positive` / `.negative`).
This file provides the syntactic feature `[±Pol]` that participates in
Agree and maps to `Core.Polarity` at LF.

## Connection to Cat.Pol

`Minimalism.Cat.Pol` is the categorial label for the polarity head.
This file adds the feature infrastructure for what that head carries.
-/

namespace Minimalism.Polarity

open Minimalism
open Core

/-- The polarity feature on Pol⁰, which may be valued or unvalued.

    In declaratives: valued [+Pol] or [-Pol]
    In polar questions: unvalued [uPol] — waiting for an answer to value it -/
inductive PolFeature where
  /-- Valued polarity: [+Pol] (affirmative) or [-Pol] (negative) -/
  | valued : Core.Polarity → PolFeature
  /-- Unvalued polarity: the feature in polar questions that the answer resolves -/
  | unvalued : PolFeature
  deriving DecidableEq, Repr

/-- Convert a `PolFeature` to a `FeatureVal` for use in the Agree system.
    [+Pol] maps to `.pol true`, [-Pol] maps to `.pol false`. -/
def PolFeature.toFeatureVal : PolFeature → GramFeature
  | .valued .positive => .valued (.pol true)
  | .valued .negative => .valued (.pol false)
  | .unvalued         => .unvalued (.pol true)  -- placeholder value for type matching

/-- Recover `Core.Polarity` from a valued syntactic [±Pol] feature. -/
def PolFeature.toPolarity : PolFeature → Option Core.Polarity
  | .valued p => some p
  | .unvalued => none

/-- A Pol⁰ head: the functional head projecting PolP.

    In @cite{holmberg-2016}'s analysis, every finite clause has a Pol⁰
    bearing a [±Pol] feature. The head's category is `Cat.Pol`. -/
structure PolHead where
  /-- The polarity feature on this head -/
  feature : PolFeature
  /-- Is this in a question context (unvalued [±Pol])? -/
  inQuestion : Bool := feature matches .unvalued
  deriving Repr

/-- An affirmative declarative Pol⁰: [+Pol] -/
def PolHead.affirmative : PolHead :=
  { feature := .valued .positive }

/-- A negative declarative Pol⁰: [-Pol] -/
def PolHead.negative : PolHead :=
  { feature := .valued .negative }

/-- A polar question Pol⁰: [uPol] -/
def PolHead.question : PolHead :=
  { feature := .unvalued }

/-- Value an unvalued [±Pol] feature — the core operation in answering
    a polar question. The answer provides a `Core.Polarity` that values
    the feature.

    Returns `none` if the feature is already valued (nothing to do). -/
def PolFeature.value (f : PolFeature) (p : Core.Polarity) : Option PolFeature :=
  match f with
  | .unvalued => some (.valued p)
  | .valued _ => none  -- already valued

/-- Valuing an unvalued feature always succeeds. -/
theorem value_unvalued (p : Core.Polarity) :
    PolFeature.unvalued.value p = some (.valued p) := rfl

/-- Valuing a valued feature always fails. -/
theorem value_valued (p q : Core.Polarity) :
    (PolFeature.valued p).value q = none := rfl

/-- Round-trip: valuing then extracting polarity recovers the answer. -/
theorem value_then_toPolarity (p : Core.Polarity) :
    (PolFeature.unvalued.value p).bind PolFeature.toPolarity = some p := rfl

/-- The [±Pol] feature matches itself in the Agree system. -/
theorem pol_feature_matches :
    FeatureVal.sameType (.pol true) (.pol false) = true := rfl

/-- [±Pol] is distinct from [±neg]: polarity and negation are
    separate features on separate heads (PolP vs NegP). -/
theorem pol_ne_neg :
    FeatureVal.sameType (.pol true) (.neg true) = false := rfl

end Minimalism.Polarity
