/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Multiset.Powerset
import Mathlib.Data.Multiset.Antidiagonal

/-!
# Counting pairs in `Multiset.antidiagonal`

`Multiset.antidiagonal w` enumerates the ordered splits `w = p.1 + p.2` *with
multiplicities*; this file computes those multiplicities: `(u, v)` occurs
`∏ x, (w.count x).choose (v.count x)` times when `u + v = w`, and `0` times otherwise.

## Main results

* `Multiset.antidiagonal_add`: `(F + G).antidiagonal` as a bind/map product of the
  summands' antidiagonals — the `+` analogue of `Multiset.antidiagonal_cons`.
* `Multiset.powerset_partition_swap`: a partition sum over `C.powerset` is invariant
  under the involution `C₁ ↦ C - C₁`.
* `Multiset.count_antidiagonal`: the closed form for `(antidiagonal w).count (u, v)`.
* `Multiset.count_antidiagonal_eq_count_powerset`: the guard-free bridge to
  `Multiset.count_powerset_of_le`.
* `Multiset.count_antidiagonal_swap`: the multiplicity is symmetric in the two slots.

`[UPSTREAM]` candidate; eventual mathlib home `Mathlib.Data.Multiset.Antidiagonal`, where
the closed form also evaluates `Finsupp.antidiagonal'`.

-/

namespace Multiset

variable {α : Type*}

/-- `antidiagonal` is invariant under `Prod.swap`: commutativity of `+` permutes the
    ordered splits. -/
theorem antidiagonal_swap (s : Multiset α) :
    s.antidiagonal.map Prod.swap = s.antidiagonal := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a t ih =>
    simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.map_map,
      ← Prod.map_comp_swap, ← Multiset.map_map _ Prod.swap, ih, add_comm]

variable [DecidableEq α]

/-- The antidiagonal of a sum decomposes as the bind/map product of the summands'
    antidiagonals: transport of `powerset_add` through
    `antidiagonal_eq_map_powerset`, closed by
    `(F + G) - (F₁ + G₁) = (F - F₁) + (G - G₁)` for `F₁ ≤ F, G₁ ≤ G`. The `+` analogue
    of `antidiagonal_cons`. -/
theorem antidiagonal_add (F G : Multiset α) :
    (F + G).antidiagonal =
      F.antidiagonal.bind (fun p =>
        G.antidiagonal.map (fun q => (p.1 + q.1, p.2 + q.2))) := by
  rw [antidiagonal_eq_map_powerset, powerset_add, map_bind,
      antidiagonal_eq_map_powerset, bind_map]
  refine bind_congr fun F₁ hF₁ => ?_
  have hF₁_le : F₁ ≤ F := mem_powerset.mp hF₁
  rw [map_map, antidiagonal_eq_map_powerset, map_map]
  refine map_congr rfl fun G₁ hG₁ => ?_
  have hG₁_le : G₁ ≤ G := mem_powerset.mp hG₁
  show ((F + G) - (F₁ + G₁), F₁ + G₁) = ((F - F₁) + (G - G₁), F₁ + G₁)
  rw [tsub_add_tsub_comm hF₁_le hG₁_le]

/-- Reindex a partition-sum over `C.powerset` by the involution `C₁ ↦ C - C₁`: summing
    `f C₁ (C - C₁)` equals summing `f (C - C₁) C₁`. Specialisation of
    `antidiagonal_swap` to the `(C₁, C - C₁)` parametrisation. -/
theorem powerset_partition_swap {β : Type*} [AddCommMonoid β] (C : Multiset α)
    (f : Multiset α → Multiset α → β) :
    (C.powerset.map fun C₁ => f C₁ (C - C₁)).sum =
      (C.powerset.map fun C₁ => f (C - C₁) C₁).sum := by
  -- Mathlib's convention: `s.antidiagonal = s.powerset.map (fun t => (s - t, t))`
  -- (complement first, subset second). So a powerset sum of `f C₁ (C - C₁)` lifts
  -- to an antidiagonal sum of `f p.2 p.1` (subset = p.2, complement = p.1).
  have h_lift_lhs : (C.powerset.map fun C₁ => f C₁ (C - C₁)).sum =
      (C.antidiagonal.map fun p => f p.2 p.1).sum := by
    rw [antidiagonal_eq_map_powerset, map_map]; rfl
  have h_lift_rhs : (C.powerset.map fun C₁ => f (C - C₁) C₁).sum =
      (C.antidiagonal.map fun p => f p.1 p.2).sum := by
    rw [antidiagonal_eq_map_powerset, map_map]; rfl
  -- The two antidiagonal forms agree by `antidiagonal_swap`.
  have h_swap : (C.antidiagonal.map fun p => f p.2 p.1).sum =
      (C.antidiagonal.map fun p => f p.1 p.2).sum := by
    conv_lhs => rw [show (fun p : Multiset α × Multiset α => f p.2 p.1) =
                      ((fun p => f p.1 p.2) ∘ Prod.swap) from funext fun _ => rfl,
                    ← map_map _ Prod.swap, antidiagonal_swap]
  rw [h_lift_lhs, h_swap, ← h_lift_rhs]

/-- The multiplicity of `(s, t)` in `antidiagonal (s + t)` is the number of ways to
    select the sub-multiset `t` from `s + t`. -/
theorem count_antidiagonal_eq_count_powerset (s t : Multiset α) :
    (antidiagonal (s + t)).count (s, t) = (s + t).powerset.count t := by
  rw [antidiagonal_eq_map_powerset,
      show (s, t) = (s + t - t, t) by rw [Multiset.add_sub_cancel_right]]
  exact count_map_eq_count' _ _ (fun _ _ h => congrArg Prod.snd h) t

/-- Closed form for the multiplicities of `Multiset.antidiagonal`: an ordered split
    `(u, v)` of `w` occurs `∏ x, (w.count x).choose (v.count x)` times. -/
theorem count_antidiagonal (u v w : Multiset α) :
    (antidiagonal w).count (u, v) =
      if u + v = w then ∏ x ∈ w.toFinset, (w.count x).choose (v.count x) else 0 := by
  split_ifs with h
  · subst h
    rw [count_antidiagonal_eq_count_powerset, count_powerset_of_le (le_add_left v u)]
  · exact count_eq_zero.mpr fun hmem => h (mem_antidiagonal.mp hmem)

/-- The antidiagonal multiplicity is symmetric in the two slots. -/
theorem count_antidiagonal_swap (u v w : Multiset α) :
    (antidiagonal w).count (u, v) = (antidiagonal w).count (v, u) := by
  conv_lhs => rw [← antidiagonal_swap w]
  exact count_map_eq_count' _ _ Prod.swap_injective (v, u)

end Multiset
