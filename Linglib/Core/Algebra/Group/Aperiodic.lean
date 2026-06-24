/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Group.Defs

/-!
# Aperiodic monoids

A monoid is **aperiodic** (group-free) when some power stabilises every element:
`∃ n, ∀ x, x ^ (n + 1) = x ^ n`. [schutzenberger-1965] introduced these as the monoids
with only trivial subgroups (his condition `γ fⁿ = γ fⁿ⁺¹`); they are the algebraic side
of the star-free / counter-free / `FO[<]`-definable languages ([pin-mfa],
[mcnaughton-papert-1971]).

`[UPSTREAM]`: mathlib has `Monoid.IsTorsion` but no aperiodicity notion; this is a
candidate for `Mathlib/Algebra/Group/`.
-/

namespace Monoid

variable (M : Type*) [Monoid M]

/-- A monoid is **aperiodic** when some uniform power stabilises every element:
`∃ n, ∀ x, x ^ (n + 1) = x ^ n` — equivalently, it has only trivial subgroups
([schutzenberger-1965]). -/
def IsAperiodic : Prop := ∃ n : ℕ, ∀ x : M, x ^ (n + 1) = x ^ n

variable {M}

/-- A subsingleton monoid is aperiodic (take `n = 0`). -/
theorem IsAperiodic.of_subsingleton [Subsingleton M] : IsAperiodic M :=
  ⟨0, fun _ => Subsingleton.elim _ _⟩

end Monoid
