import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Prefix meaning in sequential RSA

Sequential RSA models with continuous semantics interpret a token sequence by
multiplying per-word lexical values: [degen-etal-2020]'s continuous lexical
interpretation assigns each word a value in `[0, 1]`, and [waldon-degen-2021]
scores an utterance as the product of those values over its words.
`prefixMeaning` is this composition for a per-word lex function
`lex : U → W → R`, stated over any `CommMonoid R` so that both the ℚ-valued
chain of [waldon-degen-2021] and the ℚ≥0-valued chain of
[schlotterbeck-wang-2023] instantiate it. `prefixMeaning_perm` — the composed
meaning is independent of token order — is the listener-level sanity check of
[schlotterbeck-wang-2023].
-/

namespace RSA

variable {U W R : Type*}

section CommMonoid

variable [CommMonoid R]

/-- Prefix meaning: the per-word lex composed multiplicatively over a list,
`prefixMeaning lex pfx w = (pfx.map (lex · w)).prod`. -/
def prefixMeaning (lex : U → W → R) (pfx : List U) (w : W) : R :=
  (pfx.map (lex · w)).prod

@[simp] theorem prefixMeaning_nil (lex : U → W → R) (w : W) :
    prefixMeaning lex [] w = 1 := rfl

@[simp] theorem prefixMeaning_cons (lex : U → W → R) (u : U) (pfx : List U)
    (w : W) :
    prefixMeaning lex (u :: pfx) w = lex u w * prefixMeaning lex pfx w := by
  simp [prefixMeaning]

/-- Any permutation of the prefix yields the same meaning. -/
theorem prefixMeaning_perm {lex : U → W → R} {pfx pfx' : List U}
    (h : pfx.Perm pfx') (w : W) :
    prefixMeaning lex pfx w = prefixMeaning lex pfx' w :=
  (h.map _).prod_eq

end CommMonoid

section Order

variable [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]

theorem prefixMeaning_nonneg [PosMulMono R] {lex : U → W → R}
    (h : ∀ u w, 0 ≤ lex u w) (pfx : List U) (w : W) :
    0 ≤ prefixMeaning lex pfx w :=
  List.prod_nonneg (List.forall_mem_map.2 fun u _ => h u w)

end Order

end RSA
