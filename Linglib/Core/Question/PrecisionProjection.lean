import Linglib.Core.Question.QUD

/-!
# Precision Projection for Numeric QUDs

A `PrecisionProjection N` rounds/approximates values of type `N`. Composing
it with a numeric projection yields a `QUD` that distinguishes meanings only
up to that precision — the formal device behind granularity-coarsened
questions ("about a hundred" vs. "exactly 103").
-/

/-- Precision projection for numeric meanings (approximate vs exact). -/
structure PrecisionProjection (N : Type) where
  /-- Round/approximate the value -/
  round : N → N
  /-- Name -/
  name : String := ""

namespace PrecisionProjection

/-- Exact precision: no rounding -/
def exact {N : Type} : PrecisionProjection N where
  round := id
  name := "exact"

/-- Round to nearest multiple of k -/
def roundTo (k : Nat) : PrecisionProjection Nat where
  round n := (n / k) * k
  name := s!"round{k}"

/-- Compose precision with a QUD. Delegates to `QUD.ofProject`. -/
@[reducible] def applyToQUD {M N : Type} [BEq N] [LawfulBEq N]
    (prec : PrecisionProjection N) (proj : M → N) : QUD M :=
  QUD.ofProject (prec.round ∘ proj) prec.name

end PrecisionProjection
