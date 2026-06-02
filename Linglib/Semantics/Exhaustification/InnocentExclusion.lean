import Linglib.Semantics.Exhaustification.Excluder
import Linglib.Semantics.Exhaustification.Operators.Decidable

/-!
# Innocent Exclusion (Fox 2007) — concrete `Excluder` instance
[fox-2007] [spector-2016]

Wraps Fox 2007's innocent-exclusion algorithm as an `Excluder`.

The Finset-typed substrate (`IsCompatible` / `IsMCSet` / `IE` /
`innocentlyExcludable` over `Finset (Finset W)`) lives in
`Operators/Decidable.lean` (mathlib pattern: abstract spec + computable
refinement, with `Decidable` instances for downstream use). This file
is the **concrete `Excluder` instance** that consumes that substrate —
sibling to `Tolerant.lean` (Chierchia 2013) and `Relevance.lean` (Magri
2009), each of which packages a different choice of which alternatives
to negate.

Consumers call `innocent.exh ALT φ` for the exhaustified meaning.
-/

namespace Exhaustification

/-- The Fox 2007 innocent-exclusion excluder. The `Excluder` package
    around `Innocent.innocentlyExcludable`; `innocent.exh ALT φ` is the
    exhaustified meaning. -/
def innocent {W : Type*} [Fintype W] [DecidableEq W] : Excluder W where
  excluded := Innocent.innocentlyExcludable
  excluded_subset := Innocent.innocentlyExcludable_subset

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Vacuity**: when no alternative is innocently excludable,
    `innocent.exh` returns the prejacent unchanged. -/
theorem innocent_exh_eq_phi_of_innocentlyExcludable_empty
    {ALT : Finset (Finset W)} {φ : Finset W}
    (h : Innocent.innocentlyExcludable ALT φ = ∅) :
    innocent.exh ALT φ = φ := by
  show φ \ ((Innocent.innocentlyExcludable ALT φ).biUnion id) = φ
  rw [h]
  simp

end Exhaustification
