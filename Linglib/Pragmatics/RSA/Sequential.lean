import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Field.Rat

/-!
# Sequential RSA: prefix-meaning composition

@cite{cohn-gordon-goodman-potts-2019} @cite{degen-etal-2020} @cite{waldon-degen-2021} @cite{schlotterbeck-wang-2023}

The Product-of-Experts (PoE) prefix meaning underlying noisy / incremental
RSA models: a per-word lex function `lex : U → W → R` is composed
multiplicatively over a list of tokens. Higher layers (`Noisy.lean`,
`Incremental.lean`) bundle this with `RSAConfig` builders.

The substrate exists because two distinct study files
(@cite{waldon-degen-2021}, @cite{schlotterbeck-wang-2023}) independently
restipulated `lexContinuousQ`, `prefixMeaningQ`, and the order-independence
swap lemmas. With this file, both reduce to corollaries of
`List.Perm.prod_eq` from mathlib.

## Generality

`prefixMeaning` is polymorphic over any `[CommMonoid R]`. The default
arithmetic instance is ℚ for computable studies (S&W, W&D), but the same
operator applies over ℝ (proof studies) or PMF-valued semantics (future
mathlib-PMF migration, see MEMORY.md). Order-related lemmas
(`prefixMeaning_nonneg`, `_pos`) require the additional structure that
ℚ and ℝ both provide.
-/

namespace RSA

variable {U W : Type} {R : Type*}

section CommMonoid

variable [CommMonoid R]

/-- Prefix-meaning: the per-word lex composed multiplicatively over a list.
    Generic over any commutative monoid `R`. -/
def prefixMeaning (lex : U → W → R) (pfx : List U) (w : W) : R :=
  (pfx.map (lex · w)).prod

@[simp] theorem prefixMeaning_nil (lex : U → W → R) (w : W) :
    prefixMeaning lex [] w = 1 := rfl

@[simp] theorem prefixMeaning_cons (lex : U → W → R) (u : U) (pfx : List U)
    (w : W) :
    prefixMeaning lex (u :: pfx) w = lex u w * prefixMeaning lex pfx w := by
  simp [prefixMeaning]

theorem prefixMeaning_append (lex : U → W → R) (pfx₁ pfx₂ : List U) (w : W) :
    prefixMeaning lex (pfx₁ ++ pfx₂) w =
      prefixMeaning lex pfx₁ w * prefixMeaning lex pfx₂ w := by
  simp [prefixMeaning, List.prod_append]

theorem prefixMeaning_singleton (lex : U → W → R) (u : U) (w : W) :
    prefixMeaning lex [u] w = lex u w := by
  simp [prefixMeaning]

/-- **Order-independence of prefix-meaning.** Any permutation of the prefix
    yields the same product — the headline structural fact behind the noisy
    sequential RSA "swap" theorems. -/
theorem prefixMeaning_perm {lex : U → W → R} {pfx pfx' : List U}
    (h : pfx.Perm pfx') (w : W) :
    prefixMeaning lex pfx w = prefixMeaning lex pfx' w :=
  (h.map _).prod_eq

/-- Two-element swap — canonical instance of `prefixMeaning_perm`. -/
theorem prefixMeaning_swap (lex : U → W → R) (a b : U) (w : W) :
    prefixMeaning lex [a, b] w = prefixMeaning lex [b, a] w :=
  prefixMeaning_perm (List.Perm.swap b a []) w

/-- Swap the first two elements of a prefix (any tail). Generalized
    head-swap for n-element prefixes. -/
theorem prefixMeaning_swap_head (lex : U → W → R) (a b : U) (rest : List U)
    (w : W) :
    prefixMeaning lex (a :: b :: rest) w =
    prefixMeaning lex (b :: a :: rest) w :=
  prefixMeaning_perm (List.Perm.swap b a rest) w

/-- **Foldl-prod bridge.** `prefixMeaning` agrees with the imperative
    `foldl (· * lex ·)` form, generalized over any starting accumulator.
    Polymorphic version of the W&D study-file helper. -/
theorem foldl_mul_lex_eq_acc_mul_prefixMeaning (lex : U → W → R)
    (w : W) : ∀ (acc : R) (pfx : List U),
      pfx.foldl (fun a u => a * lex u w) acc = acc * prefixMeaning lex pfx w
  | acc, [] => by simp
  | acc, u :: us => by
    simp only [List.foldl, prefixMeaning_cons]
    rw [foldl_mul_lex_eq_acc_mul_prefixMeaning lex w (acc * lex u w) us, mul_assoc]

/-- The PoE prefix product, expressed as a `foldl` from the unit
    accumulator. The form W&D and S&W's original code used. -/
theorem prefixMeaning_eq_foldl_mul (lex : U → W → R) (pfx : List U) (w : W) :
    prefixMeaning lex pfx w = pfx.foldl (fun a u => a * lex u w) 1 := by
  rw [foldl_mul_lex_eq_acc_mul_prefixMeaning lex w 1 pfx, one_mul]

end CommMonoid

section Order

variable [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]

theorem prefixMeaning_nonneg [PosMulMono R] {lex : U → W → R}
    (h : ∀ u w, 0 ≤ lex u w) (pfx : List U) (w : W) :
    0 ≤ prefixMeaning lex pfx w := by
  induction pfx with
  | nil => exact zero_le_one
  | cons u us ih => rw [prefixMeaning_cons]; exact mul_nonneg (h u w) ih

theorem prefixMeaning_pos [PosMulStrictMono R] [NeZero (1 : R)]
    {lex : U → W → R} (h : ∀ u w, 0 < lex u w) (pfx : List U) (w : W) :
    0 < prefixMeaning lex pfx w := by
  induction pfx with
  | nil => exact zero_lt_one
  | cons u us ih => rw [prefixMeaning_cons]; exact mul_pos (h u w) ih

end Order

end RSA
