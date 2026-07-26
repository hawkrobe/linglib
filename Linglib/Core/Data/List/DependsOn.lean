/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Restrict
import Mathlib.Logic.Function.Basic
import Linglib.Core.Data.List.EqOn

/-!
# Dependence of output coordinates on input positions

`OutputDependsOn f i K` states that output coordinate `i` of the string function `f`
is determined by the input positions in `K`: equal-length inputs agreeing on `K` agree
at output `i`. It is the length-stratified sibling of `Function.DependsOn`, with the
same congruence form as primary definition and the same factor-through
characterization (`outputDependsOn_iff_factorsThrough`). `LeftDetermined f i` fixes
coordinate `i` by the prefix `Set.Iic i`.

## Implementation notes

The output coordinate and the input window are indexed separately, which is
informative for length-preserving functions; for block-emitting transducers the two
drift apart.
-/

namespace Subregular

open Set

variable {α β : Type*} {f : List α → List β}

/-- Output coordinate `i` of `f` is determined by the input positions in `K`:
equal-length inputs agreeing on `K` agree at output `i`. -/
def OutputDependsOn (f : List α → List β) (i : ℕ) (K : Set ℕ) : Prop :=
  ∀ ⦃u v : List α⦄, u.length = v.length → EqOn (u[·]?) (v[·]?) K →
    (f u)[i]? = (f v)[i]?

theorem OutputDependsOn.mono {i : ℕ} {K K' : Set ℕ}
    (hKK' : K ⊆ K') (h : OutputDependsOn f i K) : OutputDependsOn f i K' :=
  fun _ _ hl hag => h hl (hag.mono hKK')

/-- Coordinate `i` of the output factors through the input's length and its
restriction to `K`. -/
theorem outputDependsOn_iff_factorsThrough {i : ℕ} {K : Set ℕ} :
    OutputDependsOn f i K ↔
      Function.FactorsThrough (fun u => (f u)[i]?)
        (fun u : List α => (u.length, K.restrict (u[·]?))) := by
  constructor
  · intro h u v huv
    rw [Prod.mk.injEq] at huv
    exact h huv.1 fun k hk => congrFun huv.2 ⟨k, hk⟩
  · intro h u v hlen hag
    exact h (Prod.ext hlen (funext fun k => hag k.2))

/-- Output coordinate `i` is fixed by the prefix `Set.Iic i`. -/
def LeftDetermined (f : List α → List β) (i : ℕ) : Prop := OutputDependsOn f i (Iic i)

end Subregular
