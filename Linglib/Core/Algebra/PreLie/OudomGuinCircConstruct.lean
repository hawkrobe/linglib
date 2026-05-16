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
* `circT T n` — the lift to `Sym[R]^n L →ₗ[R] L` via `SymmetricPower.lift`
  (sorry-fenced on symmetry).

## Status

**Q1b in progress (2026-05-16).** Definition + multilinear structure
landed. Symmetry (`circTMultilinear_symm`) is decomposed into three
helper claims:

* `circTMultilinear_symm_interior` — **closed sorry-free**. Swap of two
  `Fin.castSucc` indices; uses IH on `prev`.
* `circTMultilinear_symm_exterior` — **sorry-fenced**. Swap of one
  `Fin.castSucc` with `Fin.last n`; substantively uses the right pre-Lie
  identity. Substantive remaining work (~150-300 LOC across adjacent +
  non-adjacent cases, both unfolding `prev`'s recursion).
* `circTMultilinear_symm_swap` / `circTMultilinear_symm` —
  **dispatcher + main theorem, sorry-free modulo the two helpers**.

Once `circTMultilinear_symm_exterior` lands, `circT T n` becomes
sorry-free and Q1b can proceed to combine per-degree pieces via the
TensorAlgebra detour.

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

**Status (Lemma 2.5 — substantive work pending)**.
Pieces (1), (2) are sorry-fenced; (3) and (4) are wired sorry-free
modulo (1) and (2). Each piece is independently tractable. -/

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

/-- **Lemma 2.5 — Exterior swap invariance**: for `i : Fin n`,
    `circTMultilinear R T (n+1)` is invariant under
    `Equiv.swap (Fin.castSucc i) (Fin.last n)`.

    **Substantive case**. The swap exchanges an interior argument with
    `f_last`, requiring the right pre-Lie identity. Setting
    `a := Fin.init f`, `b := f (Fin.last n)`, `c := a i`, and unfolding
    both sides via `circTMultilinear_succ` + `update_idem`/`update_comm`,
    the equation reduces (after split-at-i-position) to:

    ```
    prev a * b - prev (update a i (c*b)) - Σ_{k≠i} prev (update a k (a k * b))
    = prev (update a i b) * c - prev (update a i (b*c))
        - Σ_{k≠i} prev (update (update a k (a k * c)) i b)
    ```

    Applying `prev`'s recursion further exposes the right pre-Lie identity
    at the innermost level (verified for n = 1: the equation reduces
    exactly to `(T*c)*b - T*(c*b) = (T*b)*c - T*(b*c)`, the pre-Lie axiom).

    For n ≥ 2, the residual sums (from prev's recursion on top-level + the
    k ≠ i residual) interleave with opposite signs; full closure requires
    deep nested unfolding (each level uses pre-Lie + inner-sum cancellation).

    **Effort estimate**: ~300-500 LOC, multi-session. Alternative routes:

    1. **Stronger inductive bundle**: state Lemma 2.5 together with a
       structural update-commutation lemma to make the recursive cancellation
       provable in one go.
    2. **Bialgebra route**: define `oudomGuinCirc` via the bialgebra
       structure of `S(L)` (Q1a) directly using Sweedler notation. This
       requires extending the L × S(L) → L pre-Lie action via Δ; OG paper
       Sec 3 sketches this but it requires non-trivial substrate.

    -/
private theorem circTMultilinear_symm_exterior (R : Type) [CommRing R]
    {L : Type} [RightPreLieRing L] [RightPreLieAlgebra R L]
    (T : L) (n : ℕ) (i : Fin n)
    (ih : ∀ τ : Perm (Fin n),
      (circTMultilinear R T n).domDomCongr τ = circTMultilinear R T n) :
    (circTMultilinear R T (n + 1)).domDomCongr
        (Equiv.swap (Fin.castSucc i) (Fin.last n)) =
      circTMultilinear R T (n + 1) := by
  sorry

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
