/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Restrict
import Mathlib.Order.Interval.Set.Basic

/-!
# Positionwise agreement and dependence for lists

Two lists agree on a window of positions when their `getElem?` functions are
`Set.EqOn` that window. Agreement on `Set.Iic j` transports truncations
(`Set.EqOn.take_eq`), and agreement on `Set.Ici j` transports suffixes
(`Set.EqOn.drop_eq`). `List.DependsOn g K` states that `g : List α → γ` is
determined by the positions in `K`: equal-length inputs agreeing on `K` have equal
images — the length-stratified sibling of `Function.DependsOn`, with the same
congruence form as primary definition and the same factor-through characterization
(`List.dependsOn_iff_factorsThrough`).
-/

namespace List

variable {α γ : Type*} {u v : List α} {i j : ℕ} {g : List α → γ} {K K' : Set ℕ}

/-- Prefixes agreeing below `i` have equal `i`-truncations. -/
theorem take_eq_of_agree (h : ∀ k, k < i → u[k]? = v[k]?) : u.take i = v.take i := by
  apply List.ext_getElem?
  intro k
  rcases lt_or_ge k i with hk | hk
  · simpa only [List.getElem?_take_of_lt hk] using h k hk
  · simp [List.getElem?_take_eq_none hk]

/-- Lists agreeing from `i` upward have equal `i`-suffixes. -/
theorem drop_eq_of_agree (h : ∀ k, i ≤ k → u[k]? = v[k]?) : u.drop i = v.drop i := by
  apply List.ext_getElem?
  intro k
  simpa only [List.getElem?_drop] using h (i + k) (Nat.le_add_right i k)

/-- `g` is determined by the input positions in `K`: equal-length inputs agreeing on
`K` have equal images. The length-stratified sibling of `Function.DependsOn`. -/
def DependsOn (g : List α → γ) (K : Set ℕ) : Prop :=
  ∀ ⦃u v : List α⦄, u.length = v.length → Set.EqOn (u[·]?) (v[·]?) K → g u = g v

theorem DependsOn.mono (hKK' : K ⊆ K') (h : DependsOn g K) : DependsOn g K' :=
  fun _ _ hl hag => h hl (hag.mono hKK')

/-- `g` factors through the input's length and its restriction to `K`. -/
theorem dependsOn_iff_factorsThrough :
    DependsOn g K ↔
      Function.FactorsThrough g (fun u : List α => (u.length, K.restrict (u[·]?))) := by
  constructor
  · intro h u v huv
    rw [Prod.mk.injEq] at huv
    exact h huv.1 fun k hk => congrFun huv.2 ⟨k, hk⟩
  · intro h u v hlen hag
    exact h (Prod.ext hlen (funext fun k => hag k.2))

end List

namespace Set.EqOn

variable {α : Type*} {u v : List α} {i j : ℕ}

/-- The pointwise application of window agreement, stated in `getElem?` form so it
rewrites cleanly. -/
theorem getElem?_eq {s : Set ℕ} {k : ℕ} (h : Set.EqOn (u[·]?) (v[·]?) s) (hk : k ∈ s) :
    u[k]? = v[k]? := h hk

/-- Agreement on positions up to `j` transports truncations: `h.take_eq` for
`h : Set.EqOn (u[·]?) (v[·]?) (Set.Iic j)`. -/
theorem take_eq (h : Set.EqOn (u[·]?) (v[·]?) (Set.Iic j)) (hij : i ≤ j + 1) :
    u.take i = v.take i :=
  List.take_eq_of_agree fun _ hk => h (Set.mem_Iic.mpr (by omega))

/-- Agreement on positions from `j` transports suffixes: `h.drop_eq` for
`h : Set.EqOn (u[·]?) (v[·]?) (Set.Ici j)`. -/
theorem drop_eq (h : Set.EqOn (u[·]?) (v[·]?) (Set.Ici j)) (hij : j ≤ i) :
    u.drop i = v.drop i :=
  List.drop_eq_of_agree fun _ hk => h (Set.mem_Ici.mpr (by omega))

end Set.EqOn
