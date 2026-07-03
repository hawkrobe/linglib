/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Semantics.Questions.Partition.QUD

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

/-- Round down to the enclosing multiple of `k` — the lower representative
`⌊n/k⌋·k` of the width-`k` bucket partition; finer `k` refines the induced
QUD (`Nat.ker_div_le_of_dvd`). -/
def roundTo (k : Nat) : PrecisionProjection Nat where
  round n := n / k * k
  name := s!"round{k}"

/-- Compose precision with a QUD. Delegates to `QUD.ofProject`. -/
@[reducible] def applyToQUD {M N : Type} [BEq N] [LawfulBEq N]
    (prec : PrecisionProjection N) (proj : M → N) : QUD M :=
  QUD.ofProject (prec.round ∘ proj) prec.name

end PrecisionProjection
