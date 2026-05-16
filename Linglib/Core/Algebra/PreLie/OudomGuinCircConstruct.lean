/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.LinearAlgebra.SymmetricPower.Lift
import Linglib.Core.LinearAlgebra.SymmetricPower.ToSymmetricAlgebra
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false

/-!
# Construction of OG `T ○ A` for `T ∈ L`, `A ∈ Sym[R]^n L` (Q1b)

For a pre-Lie algebra `L` and `T ∈ L`, this file constructs the OG
`T ○ ·` operation on each symmetric power `Sym[R]^n L → L` via
Oudom-Guin Definition 2.4's recursion:

```
T ○_(0) (·) := T                                              -- input from Fin 0
T ○_(n+1) (a₁, …, aₙ, aₙ₊₁) := (T ○_(n) (a₁, …, aₙ)) * aₙ₊₁
                              - Σᵢ T ○_(n) (a₁, …, aᵢ * aₙ₊₁, …, aₙ)
```

where `*` is the pre-Lie product on `L`.

Oudom-Guin Lemma 2.5 shows `T ○_(n)` is symmetric in the `n` arguments —
the key fact making this descend to `Sym[R]^n L → L`.

## Main definitions

* `circTMultilinear T n` — `T ○_(n) (·)` as a `MultilinearMap R (Fin n → L) L`.
* `circT T n` — the lift to `Sym[R]^n L →ₗ[R] L` via `SymmetricPower.lift`,
  using `circTMultilinear_symm` (Lemma 2.5).

## Status

**Q1b: `circT T n` sorry-free (2026-05-16).** Symmetry
(`circTMultilinear_symm`) closed via three helpers:

* `circTMultilinear_symm_interior` — swap of two `Fin.castSucc` indices;
  uses IH on `prev`.
* `circTMultilinear_symm_exterior` — swap of one `Fin.castSucc` with
  `Fin.last n`; case-splits adjacent / non-adjacent. Non-adjacent reduces
  to adjacent via interior-swap conjugation (`Equiv.swap_apply_apply`).
  Adjacent (`circTMultilinear_symm_exterior_adj`) goes via the six-term
  decomposition (`circT_succ_succ_snoc_eval` — three `circTMultilinear_succ`
  unfolds) and algebraic symmetry (`sixTerm_symm` — pre-Lie identity for
  pair 1, per-degree OG identity (2.3) `prev_action_pre_lie_identity` for
  pair 2, `add_comm` for pair 3).
* `circTMultilinear_symm_swap` / `circTMultilinear_symm` — dispatcher +
  main theorem.

Q1b can now proceed to combine per-degree pieces via the TensorAlgebra
detour.

## References

* @cite{oudom-guin-2008} Def 2.4 + Lemma 2.5.
-/

namespace PreLie

namespace OudomGuinCircConstruct

open Equiv Finset
open scoped TensorProduct

variable {R : Type} {L : Type}
variable [CommRing R] [RightPreLieRing L] [RightPreLieAlgebra R L]

/-! ## §1: The recursive multilinear `T ○_(n) (·)`

Per OG Def 2.4. We use mathlib's `MultilinearMap.constOfIsEmpty` for
the base case (`n = 0`) and a recursive construction for `n + 1` using
the formula above. -/

/-- The OG `T ○_(n) (·)` as a multilinear map `(Fin n → L) → L`,
    defined recursively per Def 2.4.

    Note: `R` is made explicit (rather than implicit) so that recursive
    calls within the definition can resolve typeclasses. -/
noncomputable def circTMultilinear (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L] (T : L) :
    ∀ n : ℕ, MultilinearMap R (fun _ : Fin n ↦ L) L
  | 0 =>
    -- `Fin 0` is empty: the multilinear map is a constant `T`.
    MultilinearMap.constOfIsEmpty R _ T
  | n + 1 =>
    -- For `f : Fin (n+1) → L`:
    --   `T ○_(n+1) f = (T ○_(n) f_init) * f_last
    --                  - Σ i ∈ Fin n, T ○_(n) (f_init.update i (f_init i * f_last))`
    -- where `f_init = Fin.init f`, `f_last = f (Fin.last n)`.
    let prev := circTMultilinear R T n
    MultilinearMap.mk'
      (fun f =>
        let f_init := Fin.init f
        let f_last := f (Fin.last n)
        prev f_init * f_last -
          ∑ i : Fin n, prev (Function.update f_init i (f_init i * f_last)))
      (fun m i x y => by
        induction i using Fin.lastCases with
        | last =>
          -- i = Fin.last n: updates `f_last` only; `f_init = Fin.init m` unchanged.
          simp only [Fin.init_update_last, Function.update_self]
          rw [mul_add]
          have h : ∀ j : Fin n,
              prev (Function.update (Fin.init m) j (Fin.init m j * (x + y))) =
              prev (Function.update (Fin.init m) j (Fin.init m j * x)) +
              prev (Function.update (Fin.init m) j (Fin.init m j * y)) := by
            intro j
            rw [mul_add]
            exact prev.map_update_add _ j _ _
          simp_rw [h, Finset.sum_add_distrib]
          abel
        | cast i' =>
          -- i = Fin.castSucc i': updates `f_init` at i'; `f_last` unchanged.
          classical
          -- 1. Unfold `Fin.init` over the update; `f_last` unchanged at last.
          have h_last : ∀ z,
              (Function.update m (Fin.castSucc i') z) (Fin.last n) = m (Fin.last n) :=
            fun z => Function.update_of_ne (Fin.castSucc_ne_last i').symm z m
          simp only [Fin.init_update_castSucc, h_last]
          -- 2. Distribute prev's multilinearity at i' for the leading term.
          rw [prev.map_update_add (Fin.init m) i' x y, add_mul]
          -- 3. Case-split each `(update fi i' z) j` term.
          have h_term : ∀ z (j : Fin n),
              Function.update (Function.update (Fin.init m) i' z) j
                  ((Function.update (Fin.init m) i' z) j * m (Fin.last n)) =
              if j = i' then
                Function.update (Fin.init m) i' (z * m (Fin.last n))
              else
                Function.update (Function.update (Fin.init m) j
                    (Fin.init m j * m (Fin.last n))) i' z := by
            intros z j
            by_cases hj : j = i'
            · subst hj; rw [if_pos rfl, Function.update_self, Function.update_idem]
            · rw [if_neg hj, Function.update_of_ne hj, Function.update_comm hj]
          simp_rw [h_term, apply_ite prev]
          -- 4. Split each sum at j = i' via `Finset.sum_ite`.
          simp_rw [Finset.sum_ite, Finset.filter_eq' Finset.univ i',
                   Finset.mem_univ, if_true, Finset.sum_singleton]
          -- 5. For the i'-singleton term (z = x+y), distribute via mul_add +
          --    prev's multilinearity at i'.
          rw [show (x + y) * m (Fin.last n) = x * m (Fin.last n) + y * m (Fin.last n)
                from add_mul x y _,
              prev.map_update_add (Fin.init m) i' _ _]
          -- 6. For the residual sum (j ≠ i'), distribute via prev's
          --    multilinearity at i' + `Finset.sum_add_distrib`.
          rw [show (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j = i'),
                    prev (Function.update (Function.update (Fin.init m) j
                      (Fin.init m j * m (Fin.last n))) i' (x + y))) =
                  (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j = i'),
                    prev (Function.update (Function.update (Fin.init m) j
                      (Fin.init m j * m (Fin.last n))) i' x)) +
                  (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j = i'),
                    prev (Function.update (Function.update (Fin.init m) j
                      (Fin.init m j * m (Fin.last n))) i' y)) from by
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl
                  (fun j _ => prev.map_update_add _ i' x y)]
          -- 7. Algebraic rearrangement.
          abel)
      (fun m i c x => by
        induction i using Fin.lastCases with
        | last =>
          -- i = Fin.last n: scales f_last.
          simp only [Fin.init_update_last, Function.update_self]
          rw [mul_smul_comm]
          have h : ∀ j : Fin n,
              prev (Function.update (Fin.init m) j (Fin.init m j * (c • x))) =
              c • prev (Function.update (Fin.init m) j (Fin.init m j * x)) := by
            intro j
            rw [mul_smul_comm]
            exact prev.map_update_smul _ j _ _
          simp_rw [h]
          rw [← Finset.smul_sum, ← smul_sub]
        | cast i' =>
          -- i = Fin.castSucc i': scales f_init at i'. Symmetric to add's cast.
          classical
          have h_last : ∀ z,
              (Function.update m (Fin.castSucc i') z) (Fin.last n) = m (Fin.last n) :=
            fun z => Function.update_of_ne (Fin.castSucc_ne_last i').symm z m
          simp only [Fin.init_update_castSucc, h_last]
          rw [prev.map_update_smul (Fin.init m) i' c x, smul_mul_assoc]
          have h_term : ∀ z (j : Fin n),
              Function.update (Function.update (Fin.init m) i' z) j
                  ((Function.update (Fin.init m) i' z) j * m (Fin.last n)) =
              if j = i' then
                Function.update (Fin.init m) i' (z * m (Fin.last n))
              else
                Function.update (Function.update (Fin.init m) j
                    (Fin.init m j * m (Fin.last n))) i' z := by
            intros z j
            by_cases hj : j = i'
            · subst hj; rw [if_pos rfl, Function.update_self, Function.update_idem]
            · rw [if_neg hj, Function.update_of_ne hj, Function.update_comm hj]
          simp_rw [h_term, apply_ite prev]
          simp_rw [Finset.sum_ite, Finset.filter_eq' Finset.univ i',
                   Finset.mem_univ, if_true, Finset.sum_singleton]
          -- For the i'-singleton term (z = c • x): smul_mul_assoc + prev.map_update_smul.
          rw [show (c • x) * m (Fin.last n) = c • (x * m (Fin.last n)) from smul_mul_assoc c x _,
              prev.map_update_smul (Fin.init m) i' c _]
          -- For the residual sum (j ≠ i'): prev's multilinearity at i' + Finset.smul_sum.
          rw [show (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j = i'),
                    prev (Function.update (Function.update (Fin.init m) j
                      (Fin.init m j * m (Fin.last n))) i' (c • x))) =
                  c • ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ j = i'),
                    prev (Function.update (Function.update (Fin.init m) j
                      (Fin.init m j * m (Fin.last n))) i' x) from by
                rw [Finset.smul_sum]
                exact Finset.sum_congr rfl
                  (fun j _ => prev.map_update_smul _ i' c x)]
          rw [smul_sub, smul_add])

/-- Recursive equation: `circTMultilinear T 0 _ = T`. -/
@[simp]
theorem circTMultilinear_zero (T : L) (f : Fin 0 → L) :
    circTMultilinear R T 0 f = T :=
  rfl

/-- Recursive equation: `circTMultilinear T (n+1) f` follows Def 2.4. -/
theorem circTMultilinear_succ (T : L) (n : ℕ) (f : Fin (n + 1) → L) :
    circTMultilinear R T (n + 1) f =
      circTMultilinear R T n (Fin.init f) * f (Fin.last n) -
        ∑ i : Fin n, circTMultilinear R T n
          (Function.update (Fin.init f) i (Fin.init f i * f (Fin.last n))) := by
  rfl

/-! ## §2: Symmetry (Lemma 2.5)

The key OG Lemma 2.5: `T ○_(n) (·)` is symmetric in the `n` arguments,
i.e., `(circTMultilinear T n).domDomCongr σ = circTMultilinear T n` for
any `σ : Equiv.Perm (Fin n)`.

**Proof decomposition** (this section). We split into three sub-claims:

1. **Interior swap invariance** (`circTMultilinear_symm_interior`):
   for `i, j : Fin n`, invariance of `circTMultilinear R T (n+1)` under
   `Equiv.swap (Fin.castSucc i) (Fin.castSucc j)`. Proved by IH on `n`
   (the swap acts within `Fin.init`; `f_last` is unchanged).

2. **Exterior swap invariance** (`circTMultilinear_symm_exterior`):
   for `i : Fin n`, invariance of `circTMultilinear R T (n+1)` under
   `Equiv.swap (Fin.castSucc i) (Fin.last n)`. Reduces to the
   adjacent case `i = Fin.last (n-1)` via conjugation by interior
   swaps; the adjacent case uses `RightPreLieRing.assoc_symm'`.

3. **Any-swap invariance** (`circTMultilinear_symm_swap`): combines
   (1) and (2) via a case-split on whether either of `x, y : Fin (n+1)`
   is `Fin.last n`.

4. **Main theorem** (`circTMultilinear_symm`): reduces general `σ`
   to (3) via `Equiv.Perm.swap_induction_on`.

**Status (Lemma 2.5 — closed sorry-free 2026-05-16)**. All four pieces
are sorry-free. The substantive content lives in
`circTMultilinear_symm_exterior_adj` (adjacent case via six-term
decomposition + algebraic symmetry); other pieces are structural. -/

/-- **Lemma 2.5 — Interior swap invariance**: for `i, j : Fin n`,
    `circTMultilinear R T (n+1)` is invariant under
    `Equiv.swap (Fin.castSucc i) (Fin.castSucc j)`.

    **Proof idea**: such a swap fixes `Fin.last n` and acts via
    `Equiv.swap i j` on the `Fin.init`-side. By IH on `n`,
    `circTMultilinear R T n` is symmetric under `Perm (Fin n)`, so the
    leading term `prev (Fin.init f) * f_last` and the residual sum
    (after reindexing by `k' = Equiv.swap i j k`) are both invariant. -/
private theorem circTMultilinear_symm_interior (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    (T : L) (n : ℕ) (i j : Fin n)
    (ih : ∀ τ : Perm (Fin n),
      (circTMultilinear R T n).domDomCongr τ = circTMultilinear R T n) :
    (circTMultilinear R T (n + 1)).domDomCongr
        (Equiv.swap (Fin.castSucc i) (Fin.castSucc j)) =
      circTMultilinear R T (n + 1) := by
  classical
  -- σ : Perm (Fin (n+1)) — the swap on the lifted indices.
  set σ : Perm (Fin (n+1)) := Equiv.swap (Fin.castSucc i) (Fin.castSucc j) with hσ_def
  -- τ : Perm (Fin n) — the corresponding swap on Fin.init.
  set τ : Perm (Fin n) := Equiv.swap i j with hτ_def
  -- Key facts about σ.
  have hσ_last : σ (Fin.last n) = Fin.last n := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact (Fin.castSucc_ne_last i).symm
    · exact (Fin.castSucc_ne_last j).symm
  have hσ_cast : ∀ k : Fin n, σ (Fin.castSucc k) = Fin.castSucc (τ k) := by
    intro k
    rcases eq_or_ne k i with hki | hki
    · subst hki
      simp [hσ_def, hτ_def, Equiv.swap_apply_left]
    rcases eq_or_ne k j with hkj | hkj
    · subst hkj
      simp [hσ_def, hτ_def, Equiv.swap_apply_right]
    have hci : Fin.castSucc k ≠ Fin.castSucc i := fun h => hki (Fin.castSucc_injective _ h)
    have hcj : Fin.castSucc k ≠ Fin.castSucc j := fun h => hkj (Fin.castSucc_injective _ h)
    rw [hσ_def, Equiv.swap_apply_of_ne_of_ne hci hcj]
    rw [hτ_def, Equiv.swap_apply_of_ne_of_ne hki hkj]
  -- Reduce to pointwise.
  ext f
  simp only [MultilinearMap.domDomCongr_apply, circTMultilinear_succ]
  -- Rewrite `f_last` and `Fin.init` of the σ-composed input.
  have h_last_val : f (σ (Fin.last n)) = f (Fin.last n) := by rw [hσ_last]
  have h_init_eq : (Fin.init fun k : Fin (n+1) => f (σ k)) = (Fin.init f) ∘ τ := by
    funext k
    show f (σ (Fin.castSucc k)) = Fin.init f (τ k)
    rw [hσ_cast]
    rfl
  rw [h_last_val, h_init_eq]
  -- Leading term: prev (Fin.init f ∘ τ) = prev (Fin.init f) by IH on τ.
  have h_lead : (circTMultilinear R T n) ((Fin.init f) ∘ τ) =
                (circTMultilinear R T n) (Fin.init f) := by
    have := congr_fun (congr_arg (·.toFun) (ih τ)) (Fin.init f)
    exact this
  rw [h_lead]
  -- Sum: each summand at k matches the summand at τ k after applying IH on τ,
  -- then reindex via τ.
  congr 1
  apply Finset.sum_equiv τ (fun _ => by simp)
  intro k _
  -- Summand at k (LHS) = summand at τ k (RHS).
  -- LHS = prev (update (Fin.init f ∘ τ) k ((Fin.init f ∘ τ) k * f_last))
  --     = prev (update (Fin.init f ∘ τ) k (Fin.init f (τ k) * f_last))
  --     = prev ((update (Fin.init f) (τ k) (Fin.init f (τ k) * f_last)) ∘ τ)
  --     [by update-comp-equiv identity]
  --     = prev (update (Fin.init f) (τ k) (Fin.init f (τ k) * f_last))  [by IH on τ]
  --     = RHS.
  have h_upd : Function.update ((Fin.init f) ∘ τ) k
                  ((Fin.init f) (τ k) * f (Fin.last n)) =
               (Function.update (Fin.init f) (τ k)
                  ((Fin.init f) (τ k) * f (Fin.last n))) ∘ τ := by
    funext x
    rcases eq_or_ne x k with hxk | hxk
    · subst hxk; simp [Function.update_self]
    · simp [Function.update_of_ne hxk,
            Function.update_of_ne (fun h => hxk (τ.injective h))]
  show (circTMultilinear R T n) (Function.update ((Fin.init f) ∘ τ) k
          (((Fin.init f) ∘ τ) k * f (Fin.last n))) =
       (circTMultilinear R T n) (Function.update (Fin.init f) (τ k)
          ((Fin.init f) (τ k) * f (Fin.last n)))
  show (circTMultilinear R T n) (Function.update ((Fin.init f) ∘ τ) k
          ((Fin.init f) (τ k) * f (Fin.last n))) = _
  rw [h_upd]
  exact congr_fun (congr_arg (·.toFun) (ih τ))
    (Function.update (Fin.init f) (τ k) ((Fin.init f) (τ k) * f (Fin.last n)))

/-! ### §2.0: Small-arity evaluation lemmas

Direct evaluation of `circTMultilinear R T n` for `n = 1, 2`. Useful for
the `n = 1` base case of the exterior swap closure (Lemma 2.5). -/

/-- `circTMultilinear R T 1 g = T * g 0`. -/
@[simp]
lemma circTMultilinear_one_eval (T : L) (g : Fin 1 → L) :
    circTMultilinear R T 1 g = T * g 0 := by
  show circTMultilinear R T (0 + 1) g = _
  rw [circTMultilinear_succ, Fin.sum_univ_zero, sub_zero, circTMultilinear_zero]
  rfl

/-- `circTMultilinear R T 2 g = (T * g 0) * g 1 - T * (g 0 * g 1)`. -/
lemma circTMultilinear_two_eval (T : L) (g : Fin 2 → L) :
    circTMultilinear R T 2 g = (T * g 0) * g 1 - T * (g 0 * g 1) := by
  show circTMultilinear R T (1 + 1) g = _
  rw [circTMultilinear_succ, Fin.sum_univ_one,
      circTMultilinear_one_eval, circTMultilinear_one_eval,
      Function.update_self]
  rfl

/-! ### §2.A: OG identity (2.3) at per-degree level

For any multilinear `prev : MultilinearMap R (Fin n → L) L`, the identity
`prev (a ○ (X·Y)) − prev ((a ○ X) ○ Y) = prev (a ○ (Y·X)) − prev ((a ○ Y) ○ X)`
holds, where `prev (g ○ X) := Σ_i prev (Function.update g i (g i * X))`.

This follows from the L pre-Lie identity applied to each tuple position
plus a relabel symmetry on the off-diagonal `(i ≠ j)` terms.

Proved as a substrate lemma here for use in the exterior swap invariance
(Lemma 2.5) closure. -/

/-- Helper: split the inner sum `∑_j prev (update (update a i (a_i * W)) j (… * Z))`
    into a diagonal term `j = i` (uses `update_idem`) and an off-diagonal sum
    `j ≠ i` (uses `update_of_ne` + `update_comm` to put the W-update outside). -/
private lemma split_inner_sum_at_diag (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    {n : ℕ} (prev : MultilinearMap R (fun _ : Fin n ↦ L) L)
    (a : Fin n → L) (W Z : L) (i : Fin n) :
    (∑ j : Fin n, prev (Function.update (Function.update a i (a i * W)) j
        ((Function.update a i (a i * W)) j * Z))) =
    prev (Function.update a i ((a i * W) * Z)) +
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i),
      prev (Function.update (Function.update a j (a j * Z)) i (a i * W)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j = i)]
  congr 1
  · -- Diagonal: j = i singleton.
    rw [Finset.filter_eq' Finset.univ i, if_pos (Finset.mem_univ i),
        Finset.sum_singleton, Function.update_self, Function.update_idem]
  · -- Off-diagonal: j ≠ i. Apply `update_of_ne` then `update_comm`.
    apply Finset.sum_congr rfl
    intros j hj
    rw [Finset.mem_filter] at hj
    have hji : j ≠ i := hj.2
    rw [Function.update_of_ne hji, Function.update_comm hji]

/-- **OG identity (2.3)** at per-degree level. For multilinear `prev`,
    `a : Fin n → L`, and `X Y : L`, the "${}_n$-th degree" version of OG's
    right-action symmetry holds.

    Proof: split each inner sum into diagonal + off-diagonal via
    `split_inner_sum_at_diag`; the diagonal differences cancel via pre-Lie
    on L (applied with `MultilinearMap.map_update_sub`), the off-diagonal
    sums are equal by relabeling `(i, j) ↔ (j, i)`. -/
private theorem prev_action_pre_lie_identity (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    {n : ℕ} (prev : MultilinearMap R (fun _ : Fin n ↦ L) L)
    (a : Fin n → L) (X Y : L) :
    (∑ i : Fin n, prev (Function.update a i (a i * (X * Y)))) -
    (∑ i : Fin n, ∑ j : Fin n, prev (Function.update
        (Function.update a i (a i * X)) j
        ((Function.update a i (a i * X)) j * Y))) =
    (∑ i : Fin n, prev (Function.update a i (a i * (Y * X)))) -
    (∑ i : Fin n, ∑ j : Fin n, prev (Function.update
        (Function.update a i (a i * Y)) j
        ((Function.update a i (a i * Y)) j * X))) := by
  classical
  -- Step 1: Split each inner sum at j = i.
  simp_rw [split_inner_sum_at_diag R prev a X Y, split_inner_sum_at_diag R prev a Y X,
           Finset.sum_add_distrib]
  -- Goal now has the form:
  -- LHS_diag_X*Y − (LHS_diag_(X)*Y + LHS_offdiag_XY) =
  -- RHS_diag_Y*X − (RHS_diag_(Y)*X + RHS_offdiag_YX)
  -- where LHS_diag_X*Y = Σ_i prev (update a i (a i * (X*Y))) [from the original LHS first sum]
  --       LHS_diag_(X)*Y = Σ_i prev (update a i ((a i * X) * Y)) [from h_split's diagonal part]
  --       LHS_offdiag_XY = Σ_i Σ_{j ≠ i} prev (update (update a j (a j * Y)) i (a i * X))
  -- Rearranging: (LHS_diag_X*Y − LHS_diag_(X)*Y) − LHS_offdiag_XY
  --            = (RHS_diag_Y*X − RHS_diag_(Y)*X) − RHS_offdiag_YX

  -- Step 2: The diagonal-difference parts match via pre-Lie + multilinearity.
  have h_diag_diff :
      (∑ i : Fin n, prev (Function.update a i (a i * (X * Y)))) -
      (∑ i : Fin n, prev (Function.update a i ((a i * X) * Y))) =
      (∑ i : Fin n, prev (Function.update a i (a i * (Y * X)))) -
      (∑ i : Fin n, prev (Function.update a i ((a i * Y) * X))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intros i _
    -- prev (update a i p) - prev (update a i q) = prev (update a i (p - q))
    rw [← MultilinearMap.map_update_sub, ← MultilinearMap.map_update_sub]
    apply congrArg prev
    apply congrArg (Function.update a i)
    -- Goal: a i * (X * Y) - a i * X * Y = a i * (Y * X) - a i * Y * X
    have key := RightPreLieRing.assoc_symm' (a i) X Y
    simp only [associator] at key
    -- key : a i * X * Y - a i * (X * Y) = a i * Y * X - a i * (Y * X)
    -- Goal: negate both sides of key.
    rw [show a i * (X * Y) - a i * X * Y = -(a i * X * Y - a i * (X * Y)) from
          (neg_sub _ _).symm,
        show a i * (Y * X) - a i * Y * X = -(a i * Y * X - a i * (Y * X)) from
          (neg_sub _ _).symm,
        key]
  -- Step 3: The off-diagonal sums match via relabel (i, j) ↔ (j, i).
  have h_offdiag :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i),
          prev (Function.update (Function.update a j (a j * Y)) i (a i * X))) =
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i),
          prev (Function.update (Function.update a j (a j * X)) i (a i * Y))) := by
    -- Step 3a: Rewrite LHS using `update_comm` (since j ≠ i): swap outer/inner update order.
    rw [show (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i),
              prev (Function.update (Function.update a j (a j * Y)) i (a i * X))) =
            (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i),
              prev (Function.update (Function.update a i (a i * X)) j (a j * Y))) from
         Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => by
           rw [Finset.mem_filter] at hj
           rw [Function.update_comm hj.2]]
    -- Step 3b: Apply `sum_comm'` to swap the outer/inner summation order.
    -- After alpha-renaming (which Lean handles automatically), the result matches RHS.
    rw [Finset.sum_comm' (s := Finset.univ) (t' := Finset.univ)
          (t := fun i : Fin n => Finset.univ.filter (fun j : Fin n => j ≠ i))
          (s' := fun j : Fin n => Finset.univ.filter (fun i : Fin n => i ≠ j))
          (h := fun x y => by
            simp only [Finset.mem_univ, Finset.mem_filter, true_and, and_true]
            exact ne_comm)]
  -- Step 4: Combine via additive rearrangement.
  -- Goal: A - (Diag + OffDiag) = A' - (Diag' + OffDiag')
  -- where A - Diag = A' - Diag' (h_diag_diff), OffDiag = OffDiag' (h_offdiag).
  rw [show ∀ (A B C : L), A - (B + C) = (A - B) - C from
        fun A B C => sub_add_eq_sub_sub A B C]
  rw [show ∀ (A B C : L), A - (B + C) = (A - B) - C from
        fun A B C => sub_add_eq_sub_sub A B C]
  rw [h_diag_diff, h_offdiag]

/-! ### §2.A2: Six-term decomposition + symmetry

The OG paper unfolds `T ○_{n+2}` twice via Def 2.4 to get a six-term
expression in `(prev, A, X, Y)`. Lemma 2.5 reduces to showing that
this six-term form is symmetric under `X ↔ Y`, which follows from
the L pre-Lie identity (for the `pA·X·Y` and `pA·(X·Y)` terms) and
the per-degree OG identity (2.3) (`prev_action_pre_lie_identity`)
for the inner-sum terms. -/

/-- The six-term form of `circTMultilinear R T (n+2) (Fin.snoc (Fin.snoc A X) Y)`,
    as an explicit polynomial in `(prev, A, X, Y)`.

    Per OG 2008 Lemma 2.5 proof on page 5. -/
private noncomputable def sixTerm {R : Type} [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    {n : ℕ} (prev : MultilinearMap R (fun _ : Fin n ↦ L) L)
    (A : Fin n → L) (X Y : L) : L :=
  prev A * X * Y
  - (∑ i : Fin n, prev (Function.update A i (A i * X))) * Y
  - (∑ i' : Fin n, prev (Function.update A i' (A i' * Y))) * X
  + (∑ i' : Fin n, ∑ j : Fin n,
       prev (Function.update (Function.update A i' (A i' * Y)) j
              ((Function.update A i' (A i' * Y)) j * X)))
  - prev A * (X * Y)
  + (∑ j : Fin n, prev (Function.update A j (A j * (X * Y))))

/-- **Algebraic symmetry of `sixTerm`**: invariant under `X ↔ Y`.

    Three-pair proof:
    - **Pair 1** `(p A · X · Y − p A · (X · Y))` ↔ same with `Y · X`:
      `RightPreLieRing.assoc_symm'`.
    - **Pair 2** `(Σ p(…·(X·Y))) + (Σ Σ p(…·Y·…·X))` ↔ same with X ↔ Y:
      `prev_action_pre_lie_identity` (rearranged from `A − B = C − D`
      to `B + C = A + D`).
    - **Pair 3** `(Σ p(…·X))·Y + (Σ p(…·Y))·X` ↔ same with X ↔ Y:
      `add_comm` (the two summands literally swap roles). -/
private lemma sixTerm_symm {R : Type} [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    {n : ℕ} (prev : MultilinearMap R (fun _ : Fin n ↦ L) L)
    (A : Fin n → L) (X Y : L) :
    sixTerm prev A X Y = sixTerm prev A Y X := by
  simp only [sixTerm]
  -- Pair 1: pre-Lie identity at (p A, X, Y).
  have h_assoc :
      prev A * X * Y - prev A * (X * Y) = prev A * Y * X - prev A * (Y * X) := by
    have := RightPreLieRing.assoc_symm' (prev A) X Y
    simp only [associator] at this
    exact this
  -- Pair 2: per-degree OG identity (2.3).
  have h_og := prev_action_pre_lie_identity R prev A X Y
  -- h_og : (Σ p(…·(X·Y))) - (Σ Σ p(…·X·…·Y))
  --      = (Σ p(…·(Y·X))) - (Σ Σ p(…·Y·…·X))
  -- Convert to additive form: (Σ Σ p(…·Y·…·X)) + (Σ p(…·(X·Y)))
  --                         = (Σ Σ p(…·X·…·Y)) + (Σ p(…·(Y·X))).
  have h_og_rearr :
      (∑ i' : Fin n, ∑ j : Fin n,
         prev (Function.update (Function.update A i' (A i' * Y)) j
                ((Function.update A i' (A i' * Y)) j * X)))
      + (∑ j : Fin n, prev (Function.update A j (A j * (X * Y)))) =
      (∑ i' : Fin n, ∑ j : Fin n,
         prev (Function.update (Function.update A i' (A i' * X)) j
                ((Function.update A i' (A i' * X)) j * Y)))
      + (∑ j : Fin n, prev (Function.update A j (A j * (Y * X)))) := by
    have h := sub_eq_zero.mpr h_og
    have eq :
        ((∑ i' : Fin n, ∑ j : Fin n,
           prev (Function.update (Function.update A i' (A i' * Y)) j
                  ((Function.update A i' (A i' * Y)) j * X)))
         + (∑ j : Fin n, prev (Function.update A j (A j * (X * Y)))))
        - ((∑ i' : Fin n, ∑ j : Fin n,
             prev (Function.update (Function.update A i' (A i' * X)) j
                    ((Function.update A i' (A i' * X)) j * Y)))
           + (∑ j : Fin n, prev (Function.update A j (A j * (Y * X))))) =
        ((∑ j : Fin n, prev (Function.update A j (A j * (X * Y))))
         - (∑ i' : Fin n, ∑ j : Fin n,
             prev (Function.update (Function.update A i' (A i' * X)) j
                    ((Function.update A i' (A i' * X)) j * Y))))
        - ((∑ j : Fin n, prev (Function.update A j (A j * (Y * X))))
           - (∑ i' : Fin n, ∑ j : Fin n,
               prev (Function.update (Function.update A i' (A i' * Y)) j
                      ((Function.update A i' (A i' * Y)) j * X)))) := by
      abel
    have : ((∑ i' : Fin n, ∑ j : Fin n,
              prev (Function.update (Function.update A i' (A i' * Y)) j
                     ((Function.update A i' (A i' * Y)) j * X)))
            + (∑ j : Fin n, prev (Function.update A j (A j * (X * Y)))))
           - ((∑ i' : Fin n, ∑ j : Fin n,
                prev (Function.update (Function.update A i' (A i' * X)) j
                       ((Function.update A i' (A i' * X)) j * Y)))
              + (∑ j : Fin n, prev (Function.update A j (A j * (Y * X))))) = 0 := by
      rw [eq]; exact h
    exact sub_eq_zero.mp this
  -- Pair 3: add_comm on the two `(Σ ...) * (X or Y)` terms.
  have h_pair3 :
      (∑ i : Fin n, prev (Function.update A i (A i * X))) * Y
      + (∑ i' : Fin n, prev (Function.update A i' (A i' * Y))) * X =
      (∑ i : Fin n, prev (Function.update A i (A i * Y))) * X
      + (∑ i' : Fin n, prev (Function.update A i' (A i' * X))) * Y := by
    rw [add_comm]
  -- Combine via abel and the three pair identities.
  -- LHS = [(1)-(5)] + [(4)+(6)] - [(2)+(3)]
  -- RHS = [(1')-(5')] + [(4')+(6')] - [(2')+(3')]
  have lhs_rearr :
      prev A * X * Y
      - (∑ i : Fin n, prev (Function.update A i (A i * X))) * Y
      - (∑ i' : Fin n, prev (Function.update A i' (A i' * Y))) * X
      + (∑ i' : Fin n, ∑ j : Fin n,
           prev (Function.update (Function.update A i' (A i' * Y)) j
                  ((Function.update A i' (A i' * Y)) j * X)))
      - prev A * (X * Y)
      + (∑ j : Fin n, prev (Function.update A j (A j * (X * Y))))
      =
      (prev A * X * Y - prev A * (X * Y))
      + ((∑ i' : Fin n, ∑ j : Fin n,
            prev (Function.update (Function.update A i' (A i' * Y)) j
                   ((Function.update A i' (A i' * Y)) j * X)))
         + (∑ j : Fin n, prev (Function.update A j (A j * (X * Y)))))
      - ((∑ i : Fin n, prev (Function.update A i (A i * X))) * Y
         + (∑ i' : Fin n, prev (Function.update A i' (A i' * Y))) * X) := by
    abel
  have rhs_rearr :
      prev A * Y * X
      - (∑ i : Fin n, prev (Function.update A i (A i * Y))) * X
      - (∑ i' : Fin n, prev (Function.update A i' (A i' * X))) * Y
      + (∑ i' : Fin n, ∑ j : Fin n,
           prev (Function.update (Function.update A i' (A i' * X)) j
                  ((Function.update A i' (A i' * X)) j * Y)))
      - prev A * (Y * X)
      + (∑ j : Fin n, prev (Function.update A j (A j * (Y * X))))
      =
      (prev A * Y * X - prev A * (Y * X))
      + ((∑ i' : Fin n, ∑ j : Fin n,
            prev (Function.update (Function.update A i' (A i' * X)) j
                   ((Function.update A i' (A i' * X)) j * Y)))
         + (∑ j : Fin n, prev (Function.update A j (A j * (Y * X)))))
      - ((∑ i : Fin n, prev (Function.update A i (A i * Y))) * X
         + (∑ i' : Fin n, prev (Function.update A i' (A i' * X))) * Y) := by
    abel
  rw [lhs_rearr, rhs_rearr, h_assoc, h_og_rearr, h_pair3]

/-- **Decomposition lemma**: `circT (m+3)` evaluated at a snoc-snoc tuple
    `Fin.snoc (Fin.snoc A X) Y` equals the explicit six-term polynomial in
    `(prev = circT (m+1), A, X, Y)`.

    This is OG 2008 Lemma 2.5's "unfold three times" step (the leading
    `circT (m+2)` and the inner summands all unfold via Def 2.4). The
    `Fin.snoc` form makes the `Fin.init` / `Fin.last` simplifications
    clean (`Fin.init_snoc`, `Fin.snoc_last`, `Fin.snoc_castSucc`). -/
private lemma circT_succ_succ_snoc_eval (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    (T : L) (m : ℕ) (A : Fin (m + 1) → L) (X Y : L) :
    circTMultilinear R T (m + 3) (Fin.snoc (Fin.snoc A X) Y) =
      sixTerm (circTMultilinear R T (m + 1)) A X Y := by
  classical
  -- Setup: per-summand sub-evaluation lemmas (each is one `circTMultilinear_succ`
  -- unfold plus snoc/init simplifications).
  -- (a) Leading: `circT (m+2) (Fin.snoc A X)`.
  have h_lead :
      circTMultilinear R T (m + 2) (Fin.snoc A X) =
        circTMultilinear R T (m + 1) A * X -
        ∑ i : Fin (m + 1),
          circTMultilinear R T (m + 1) (Function.update A i (A i * X)) := by
    show circTMultilinear R T ((m + 1) + 1) (Fin.snoc A X) = _
    rw [circTMultilinear_succ]
    simp only [Fin.init_snoc, Fin.snoc_last]
  -- (b) The `Fin.last (m+1)` summand: `circT (m+2) (update (Fin.snoc A X) (Fin.last (m+1)) (X*Y))`.
  have h_last :
      circTMultilinear R T (m + 2)
          (Function.update (Fin.snoc A X) (Fin.last (m + 1)) (X * Y)) =
        circTMultilinear R T (m + 1) A * (X * Y) -
        ∑ j : Fin (m + 1),
          circTMultilinear R T (m + 1)
            (Function.update A j (A j * (X * Y))) := by
    show circTMultilinear R T ((m + 1) + 1)
        (Function.update (Fin.snoc A X) (Fin.last (m + 1)) (X * Y)) = _
    rw [circTMultilinear_succ]
    -- `Fin.init (update q (last (m+1)) z) = Fin.init q`; result `= A`.
    -- `(update q (last (m+1)) z) (last (m+1)) = z = X*Y`.
    simp only [Fin.init_update_last, Fin.init_snoc, Function.update_self]
  -- (c) Each `Fin.castSucc i'` summand: `circT (m+2) (update (Fin.snoc A X) (Fin.castSucc i') (A i' * Y))`.
  have h_castSucc : ∀ i' : Fin (m + 1),
      circTMultilinear R T (m + 2)
          (Function.update (Fin.snoc A X) (Fin.castSucc i') (A i' * Y)) =
        circTMultilinear R T (m + 1) (Function.update A i' (A i' * Y)) * X -
        ∑ j : Fin (m + 1),
          circTMultilinear R T (m + 1)
            (Function.update (Function.update A i' (A i' * Y)) j
              ((Function.update A i' (A i' * Y)) j * X)) := by
    intro i'
    show circTMultilinear R T ((m + 1) + 1)
        (Function.update (Fin.snoc A X) (Fin.castSucc i') (A i' * Y)) = _
    rw [circTMultilinear_succ]
    -- `Fin.init (update q (castSucc i') y) = update (Fin.init q) i' y`; result `= update A i' (A i' * Y)`.
    -- `(update q (castSucc i') y) (last (m+1)) = q (last (m+1)) = X` (since castSucc i' ≠ last (m+1)).
    have h_last_pos :
        (Function.update (Fin.snoc A X : Fin (m + 2) → L)
          (Fin.castSucc i') (A i' * Y)) (Fin.last (m + 1)) = X := by
      rw [Function.update_of_ne (Fin.castSucc_ne_last _).symm, Fin.snoc_last]
    simp only [Fin.init_update_castSucc, Fin.init_snoc, h_last_pos]
  -- Main combine.
  simp only [sixTerm]
  show circTMultilinear R T ((m + 2) + 1) (Fin.snoc (Fin.snoc A X) Y) = _
  rw [circTMultilinear_succ]
  -- Outer simplification: `Fin.init (snoc (snoc A X) Y) = snoc A X`; `(snoc (snoc A X) Y) (last (m+2)) = Y`.
  simp only [Fin.init_snoc, Fin.snoc_last]
  -- Split the outer Σ via `Fin.sum_univ_castSucc`.
  rw [Fin.sum_univ_castSucc]
  -- Evaluate `(Fin.snoc A X)` at castSucc i' and at last (m+1) within update arguments.
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  -- Rewrite leading and last-summand and each castSucc i' summand.
  rw [h_lead, h_last]
  rw [show (∑ i' : Fin (m + 1),
              circTMultilinear R T (m + 2)
                (Function.update (Fin.snoc A X) (Fin.castSucc i') (A i' * Y)))
          = ∑ i' : Fin (m + 1),
              (circTMultilinear R T (m + 1) (Function.update A i' (A i' * Y)) * X
              - ∑ j : Fin (m + 1),
                  circTMultilinear R T (m + 1)
                    (Function.update (Function.update A i' (A i' * Y)) j
                      ((Function.update A i' (A i' * Y)) j * X)))
       from Finset.sum_congr rfl (fun i' _ => h_castSucc i')]
  -- Distribute Σ over subtraction; pull X out of inner sum.
  simp only [Finset.sum_sub_distrib, sub_mul, ← Finset.sum_mul]
  abel

/-! ### §2.B: Adjacent-exterior swap helper

The substantive content of Lemma 2.5's exterior case lives here, in the
"adjacent" case: invariance of `circT (m+3)` under the swap of the last
two positions `(m+1, m+2)`. The general exterior swap reduces to this
via conjugation by an interior swap (see `circTMultilinear_symm_exterior`).

This split lets the non-adjacent case appeal to the adjacent case as a
plain hypothesis rather than mutually-recursing inside the dispatcher. -/

/-- **Adjacent-exterior swap helper**: for `m : ℕ`, `circT (m+3)` is
    invariant under `swap (Fin.castSucc (Fin.last (m+1))) (Fin.last (m+2))`
    (the swap of the last two positions).

    Proof (per OG 2008 Lemma 2.5 page 5): unfold `circT (m+3) f` via
    `circTMultilinear_succ` twice to get a 6-term expansion. Pair the
    terms three ways: (1)-(5) via L's pre-Lie identity, (4)+(6) via
    `prev_action_pre_lie_identity` (the per-degree OG identity 2.3),
    (2)+(3) trivially by `X ↔ Y` symmetry. -/
private theorem circTMultilinear_symm_exterior_adj (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    (T : L) (m : ℕ)
    (_ih : ∀ τ : Perm (Fin (m + 2)),
      (circTMultilinear R T (m + 2)).domDomCongr τ =
        circTMultilinear R T (m + 2)) :
    (circTMultilinear R T (m + 3)).domDomCongr
        (Equiv.swap (Fin.castSucc (Fin.last (m + 1))) (Fin.last (m + 2))) =
      circTMultilinear R T (m + 3) := by
  classical
  ext f
  simp only [MultilinearMap.domDomCongr_apply]
  -- Reconstruct both `f` and `f ∘ sw` as `Fin.snoc (Fin.snoc A ?) ?` and apply the
  -- six-term decomposition lemma `circT_succ_succ_snoc_eval` to each. The result
  -- is `sixTerm ... X Y` for `f` and `sixTerm ... Y X` for `f ∘ sw`; conclude via
  -- `sixTerm_symm`.
  set sw : Perm (Fin (m + 3)) :=
    Equiv.swap (Fin.castSucc (Fin.last (m + 1))) (Fin.last (m + 2)) with hsw_def
  -- f = Fin.snoc (Fin.snoc (Fin.init (Fin.init f)) X) Y, where
  -- X = f (Fin.castSucc (Fin.last (m+1))) and Y = f (Fin.last (m+2)).
  have hf_eq : f = Fin.snoc (Fin.snoc (Fin.init (Fin.init f))
                              (f (Fin.castSucc (Fin.last (m + 1)))))
                            (f (Fin.last (m + 2))) := by
    have h_init_eq : (Fin.init f) (Fin.last (m + 1)) =
                      f (Fin.castSucc (Fin.last (m + 1))) := rfl
    have h_inner : Fin.snoc (Fin.init (Fin.init f))
                            (f (Fin.castSucc (Fin.last (m + 1)))) = Fin.init f := by
      rw [← h_init_eq]; exact Fin.snoc_init_self (Fin.init f)
    rw [h_inner]
    exact (Fin.snoc_init_self f).symm
  -- (fun k => f (sw k)) = Fin.snoc (Fin.snoc A Y) X, with X, Y swapped.
  have hf_sw_eq : (fun k => f (sw k)) =
      Fin.snoc (Fin.snoc (Fin.init (Fin.init f))
                (f (Fin.last (m + 2))))
              (f (Fin.castSucc (Fin.last (m + 1)))) := by
    funext k
    induction k using Fin.lastCases with
    | last =>
      -- sw (last (m+2)) = castSucc (last (m+1)); RHS at last (m+2) = X.
      show f (sw (Fin.last (m + 2))) =
        ((Fin.snoc (Fin.snoc (Fin.init (Fin.init f))
                    (f (Fin.last (m + 2))))
                  (f (Fin.castSucc (Fin.last (m + 1)))) :
                Fin (m + 3) → L)) (Fin.last (m + 2))
      rw [Fin.snoc_last, hsw_def, Equiv.swap_apply_right]
    | cast k' =>
      induction k' using Fin.lastCases with
      | last =>
        -- sw (castSucc (last (m+1))) = last (m+2); RHS at castSucc (last (m+1)) = Y.
        show f (sw (Fin.castSucc (Fin.last (m + 1)))) =
          ((Fin.snoc (Fin.snoc (Fin.init (Fin.init f))
                      (f (Fin.last (m + 2))))
                    (f (Fin.castSucc (Fin.last (m + 1)))) :
                  Fin (m + 3) → L))
            (Fin.castSucc (Fin.last (m + 1)))
        rw [Fin.snoc_castSucc, Fin.snoc_last, hsw_def, Equiv.swap_apply_left]
      | cast k'' =>
        -- sw fixes castSucc (castSucc k''); both sides reduce to f (castSucc (castSucc k'')).
        show f (sw (Fin.castSucc (Fin.castSucc k''))) =
          ((Fin.snoc (Fin.snoc (Fin.init (Fin.init f))
                      (f (Fin.last (m + 2))))
                    (f (Fin.castSucc (Fin.last (m + 1)))) :
                  Fin (m + 3) → L))
            (Fin.castSucc (Fin.castSucc k''))
        have h_fix : sw (Fin.castSucc (Fin.castSucc k'')) =
                      Fin.castSucc (Fin.castSucc k'') := by
          rw [hsw_def]
          apply Equiv.swap_apply_of_ne_of_ne
          · intro h
            exact (Fin.castSucc_ne_last k'') (Fin.castSucc_injective _ h)
          · exact Fin.castSucc_ne_last _
        rw [h_fix, Fin.snoc_castSucc, Fin.snoc_castSucc]
        rfl
  -- Apply decomposition + algebraic symmetry.
  rw [hf_sw_eq]
  conv_rhs => rw [hf_eq]
  rw [circT_succ_succ_snoc_eval, circT_succ_succ_snoc_eval]
  exact sixTerm_symm _ _ _ _

/-- **Lemma 2.5 — Exterior swap invariance**: for `i : Fin n`,
    `circTMultilinear R T (n+1)` is invariant under
    `Equiv.swap (Fin.castSucc i) (Fin.last n)`.

    **OG-paper-derived plan** (after reading @cite{oudom-guin-2008} Lemma 2.5
    proof, page 5). Substantially cleaner than the recursive-cancellation
    approach. Outline:

    1. **Structural reduction**: non-adjacent `i ≠ Fin.last (n-1)` reduces
       to adjacent `i = Fin.last (n-1)` via conjugation by interior swap
       (handled by `circTMultilinear_symm_interior`).

    2. **Adjacent case** (`i = Fin.last (n-1)`, viewed as the
       `(n, n+1)`-position swap): unfolds `circTMultilinear T (n+2)` via
       `circTMultilinear_succ` applied **twice** to get six terms, then
       pairs:

       - **Pair 1** `±((T ○_n A) ○ X) ○ Y ∓ (T ○_n A) ○ (X ○ Y)`:
         pre-Lie identity on `(T ○_n A, X, Y)` → symmetric in `X ↔ Y`.
       - **Pair 2** `+T ○_n ((A ○ Y) ○ X) + T ○_n (A ○ (X ○ Y))`:
         OG identity (2.3) at per-degree level applied via `T ○_n`'s
         linearity → symmetric in `X ↔ Y`.
       - **Pair 3** `−(T ○_n (A ○ X)) ○ Y − (T ○_n (A ○ Y)) ○ X`:
         trivially symmetric in `X ↔ Y`.

    3. **Full S_{n+2} action** by combining the adjacent (n+1, n+2) swap
       with IH (symmetry of `circT n+1` on the first n+1 positions).

    **OG identity (2.3) at per-degree level** — landed sorry-free as
    `prev_action_pre_lie_identity` above. Statement:
    For `a : Fin n → L`, `X Y : L`:
    `prev (a ○ (X*Y)) - prev ((a ○ X) ○ Y) = prev (a ○ (Y*X)) - prev ((a ○ Y) ○ X)`
    where `prev (g ○ X) := Σ_i prev (Function.update g i (g i * X))`.
    Follows from the L pre-Lie identity applied to each tuple position
    plus relabel symmetry for off-diagonal sums.

    The adjacent case is now closed in `circTMultilinear_symm_exterior_adj`
    via `circT_succ_succ_snoc_eval` (six-term decomposition) +
    `sixTerm_symm` (algebraic symmetry).

    Reference: @cite{oudom-guin-2008} Lemma 2.5 proof, p. 5. -/
private theorem circTMultilinear_symm_exterior (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    (T : L) (n : ℕ) (i : Fin n)
    (ih : ∀ τ : Perm (Fin n),
      (circTMultilinear R T n).domDomCongr τ = circTMultilinear R T n) :
    (circTMultilinear R T (n + 1)).domDomCongr
        (Equiv.swap (Fin.castSucc i) (Fin.last n)) =
      circTMultilinear R T (n + 1) := by
  match n, i with
  | 0, i => exact Fin.elim0 i
  | 1, i =>
    -- n = 1: i = 0 (only element of Fin 1). One direct pre-Lie application.
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    ext f
    rw [MultilinearMap.domDomCongr_apply,
        circTMultilinear_two_eval, circTMultilinear_two_eval]
    have h0 : Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1) 0 = 1 :=
      Equiv.swap_apply_left _ _
    have h1 : Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1) 1 = 0 :=
      Equiv.swap_apply_right _ _
    show (T * f (Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1) 0)) *
         f (Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1) 1) -
         T * (f (Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1) 0) *
              f (Equiv.swap (Fin.castSucc (0 : Fin 1)) (Fin.last 1) 1)) =
         (T * f 0) * f 1 - T * (f 0 * f 1)
    rw [h0, h1]
    -- Goal: (T * f 1) * f 0 - T * (f 1 * f 0) = (T * f 0) * f 1 - T * (f 0 * f 1)
    have key := RightPreLieRing.assoc_symm' T (f 0) (f 1)
    simp only [associator] at key
    exact key.symm
  | m + 2, i =>
    -- n ≥ 2: general case via OG 6-term proof. See docstring above.
    -- Case-split: adjacent (`i = Fin.last (m+1)`) vs non-adjacent.
    classical
    induction i using Fin.lastCases with
    | last =>
      -- Adjacent case: swap exchanges positions m+1, m+2 of Fin (m+3).
      -- Direct appeal to the substantive helper.
      exact circTMultilinear_symm_exterior_adj R T m ih
    | cast j' =>
      -- Non-adjacent: i = Fin.castSucc j' with j' : Fin (m+1).
      -- Reduce to adjacent via conjugation by interior swap g, where
      -- g sends the non-adjacent position `Fin.castSucc (Fin.castSucc j')`
      -- to the adjacent position `Fin.castSucc (Fin.last (m+1))` and fixes
      -- `Fin.last (m+2)`. The conjugation identity
      --   swap (g a) (g b) = g * swap a b * g⁻¹
      -- (mathlib `Equiv.swap_apply_apply`) gives the rewrite.
      -- Normalize `m + 2 + 1` to `m + 3` for `rw` to fire syntactically.
      show (circTMultilinear R T (m + 3)).domDomCongr
              (Equiv.swap (Fin.castSucc (Fin.castSucc j')) (Fin.last (m + 2))) =
            circTMultilinear R T (m + 3)
      set g : Perm (Fin (m + 3)) :=
        Equiv.swap (Fin.castSucc (Fin.castSucc j'))
          (Fin.castSucc (Fin.last (m + 1))) with hg_def
      -- (a) g is self-inverse.
      have hg_inv : g⁻¹ = g := Equiv.swap_inv _ _
      -- (b) g fixes `Fin.last (m+2)`.
      have hg_last : g (Fin.last (m + 2)) = Fin.last (m + 2) := by
        apply Equiv.swap_apply_of_ne_of_ne
        · exact (Fin.castSucc_ne_last _).symm
        · exact (Fin.castSucc_ne_last _).symm
      -- (c) g sends the non-adjacent position to the adjacent position.
      have hg_a : g (Fin.castSucc (Fin.castSucc j')) =
                    Fin.castSucc (Fin.last (m + 1)) :=
        Equiv.swap_apply_left _ _
      -- (d) interior-swap invariance applies to g.
      have h_int :
          (circTMultilinear R T (m + 3)).domDomCongr g =
            circTMultilinear R T (m + 3) :=
        circTMultilinear_symm_interior R T (m + 2)
          (Fin.castSucc j') (Fin.last (m + 1)) ih
      -- (e) adjacent-exterior invariance from the helper.
      have h_adj :
          (circTMultilinear R T (m + 3)).domDomCongr
              (Equiv.swap (Fin.castSucc (Fin.last (m + 1)))
                (Fin.last (m + 2))) =
            circTMultilinear R T (m + 3) :=
        circTMultilinear_symm_exterior_adj R T m ih
      -- (f) conjugation: swap_target = g⁻¹ * swap_adj * g.
      have h_conj :
          Equiv.swap (Fin.castSucc (Fin.castSucc j')) (Fin.last (m + 2)) =
          g⁻¹ * Equiv.swap (Fin.castSucc (Fin.last (m + 1)))
                  (Fin.last (m + 2)) * g := by
        have h := Equiv.swap_apply_apply g
          (Fin.castSucc (Fin.castSucc j')) (Fin.last (m + 2))
        rw [hg_a, hg_last] at h
        -- h : swap_adj = g * swap_target * g⁻¹
        -- Need: swap_target = g⁻¹ * swap_adj * g = g⁻¹ * (g * swap_target * g⁻¹) * g
        rw [h, mul_assoc g _ g⁻¹, inv_mul_cancel_left, inv_mul_cancel_right]
      -- (g) Combine via `domDomCongr_mul` (twice) + h_int + h_adj + hg_inv.
      rw [h_conj, MultilinearMap.domDomCongr_mul, h_int,
          MultilinearMap.domDomCongr_mul, h_adj, hg_inv]
      exact h_int

/-- **Lemma 2.5 — Any-swap invariance**: combines interior and exterior
    cases via a case-split on whether either of `x, y : Fin (n+1)` is
    `Fin.last n`. -/
private theorem circTMultilinear_symm_swap (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    (T : L) (n : ℕ) (x y : Fin (n + 1)) (hxy : x ≠ y)
    (ih : ∀ τ : Perm (Fin n),
      (circTMultilinear R T n).domDomCongr τ = circTMultilinear R T n) :
    (circTMultilinear R T (n + 1)).domDomCongr (Equiv.swap x y) =
      circTMultilinear R T (n + 1) := by
  -- Case-split each of x, y as either `Fin.castSucc _` or `Fin.last n`.
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => exact absurd rfl hxy
    | cast j' =>
      -- swap (Fin.last n) (Fin.castSucc j') = swap (Fin.castSucc j') (Fin.last n)
      rw [Equiv.swap_comm]
      exact circTMultilinear_symm_exterior R T n j' ih
  | cast i' =>
    induction y using Fin.lastCases with
    | last =>
      exact circTMultilinear_symm_exterior R T n i' ih
    | cast j' =>
      exact circTMultilinear_symm_interior R T n i' j' ih

/-- **OG Lemma 2.5**: `T ○_(n) (·)` is symmetric in its `n` arguments. -/
theorem circTMultilinear_symm (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    (T : L) (n : ℕ) (σ : Perm (Fin n)) :
    (circTMultilinear R T n).domDomCongr σ =
      circTMultilinear R T n := by
  induction n with
  | zero =>
    -- `Perm (Fin 0)` is the trivial group.
    have : σ = 1 := Subsingleton.elim _ _
    rw [this]
    rfl
  | succ n ih =>
    -- Reduce σ to a product of swaps via `swap_induction_on`; each swap
    -- is closed by `circTMultilinear_symm_swap` (which dispatches to
    -- interior / exterior cases).
    induction σ using Equiv.Perm.swap_induction_on with
    | one => rfl
    | swap_mul τ x y hxy ih_τ =>
      rw [MultilinearMap.domDomCongr_mul, ih_τ]
      exact circTMultilinear_symm_swap R T n x y hxy ih

/-! ## §3: Lift to `Sym[R]^n L → L`

Using `SymmetricPower.lift` (Q1b.0a) and `circTMultilinear_symm` (Lemma 2.5),
we obtain the OG operation on each symmetric power. -/

/-- **OG `T ○_(n) (·)`** lifted to `Sym[R]^n L →ₗ[R] L` via the universal
    property of the symmetric power. -/
noncomputable def circT (T : L) (n : ℕ) :
    Sym[R] (Fin n) L →ₗ[R] L :=
  SymmetricPower.lift (circTMultilinear R T n) (circTMultilinear_symm R T n)

@[simp]
theorem circT_tprod (T : L) (n : ℕ) (f : Fin n → L) :
    circT (R := R) T n (SymmetricPower.tprod R f) =
      circTMultilinear R T n f := by
  rw [circT, SymmetricPower.lift_tprod]

/-- For `n = 0`: `circT T 0` sends the unit `tprod R Fin.elim0` to `T`. -/
@[simp]
theorem circT_zero_tprod (T : L) (f : Fin 0 → L) :
    circT (R := R) T 0 (SymmetricPower.tprod R f) = T := by
  rw [circT_tprod, circTMultilinear_zero]

end OudomGuinCircConstruct

end PreLie
