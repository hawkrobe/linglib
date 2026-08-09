import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Multiplicative composition of graded word meanings

Graded approaches to meaning ([erk-2022]'s "probabilistic turn") assign each
word a graded value rather than a Boolean; an utterance meaning is then
composed by multiplying the word values, treating words as independent
constraints: [degen-etal-2020]'s continuous semantics scores a referring
expression as the product of per-word values, and the incremental models of
[waldon-degen-2021] (ℚ-valued) and [schlotterbeck-wang-2023] (ℚ≥0-valued)
apply the same composition to utterance prefixes. `prodMeaning` is this
composition for a per-word lex function `lex : U → W → R`, stated over any
`CommMonoid R`. `prodMeaning_perm` — the composed meaning is independent of
token order — is the listener-level sanity check of
[schlotterbeck-wang-2023].

The normalized counterpart on `PMF` is the Product of Experts
(`Core/Probability/ProductOfExperts.lean`), the combination rule of
[erk-herbelot-2024]'s situation description systems.
-/

namespace Semantics.Probabilistic

variable {U W R : Type*}

section CommMonoid

variable [CommMonoid R]

/-- Product meaning: the per-word lex composed multiplicatively over a token
list, `prodMeaning lex us w = (us.map (lex · w)).prod`. -/
def prodMeaning (lex : U → W → R) (us : List U) (w : W) : R :=
  (us.map (lex · w)).prod

@[simp] theorem prodMeaning_nil (lex : U → W → R) (w : W) :
    prodMeaning lex [] w = 1 := rfl

@[simp] theorem prodMeaning_cons (lex : U → W → R) (u : U) (us : List U)
    (w : W) :
    prodMeaning lex (u :: us) w = lex u w * prodMeaning lex us w := by
  simp [prodMeaning]

/-- Any permutation of the token list yields the same meaning. -/
theorem prodMeaning_perm {lex : U → W → R} {us us' : List U}
    (h : us.Perm us') (w : W) :
    prodMeaning lex us w = prodMeaning lex us' w :=
  (h.map _).prod_eq

end CommMonoid

section Order

variable [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R]

theorem prodMeaning_nonneg [PosMulMono R] {lex : U → W → R}
    (h : ∀ u w, 0 ≤ lex u w) (us : List U) (w : W) :
    0 ≤ prodMeaning lex us w :=
  List.prod_nonneg (List.forall_mem_map.2 fun u _ => h u w)

end Order

end Semantics.Probabilistic
