/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Incremental RSA: prefix meanings

Incremental RSA ([cohn-gordon-goodman-potts-2019]) runs the pipeline word by word, so the
literal listener needs the meaning of an utterance *prefix*. With the graded lexical semantics of
[degen-etal-2020] each word contributes a value in a commutative monoid and the prefix meaning is
their product, treating words as independent constraints — the composition of
[waldon-degen-2021] and of [schlotterbeck-wang-2023]'s context-independent case, an instance of
the probabilistic turn surveyed in [erk-2022].

## Main definitions

* `RSA.prodMeaning lex us w`: the product over the tokens `us` of the per-word values `lex u w`.

## Main results

* `RSA.prodMeaning_perm`: the prefix meaning is independent of token order — the listener-level
  sanity check of [schlotterbeck-wang-2023].
* `RSA.prodMeaning_nonneg`, `RSA.prodMeaning_le_one`: bounds inherited from the lexicon.

## References

* [R. Cohn-Gordon, N. D. Goodman, C. Potts, *An incremental iterated response model of
  pragmatics*][cohn-gordon-goodman-potts-2019]
* [J. Degen et al., *When redundancy is useful: a Bayesian approach to "overinformative"
  referring expressions*][degen-etal-2020]
* [B. Waldon, J. Degen, *Modeling cross-linguistic production of referring expressions*
  ][waldon-degen-2021]
* [F. Schlotterbeck, H. Wang, *An incremental RSA model for adjective ordering preferences in
  referential visual context*][schlotterbeck-wang-2023]
-/

@[expose] public section

namespace RSA

variable {U W R : Type*}

section CommMonoid

variable [CommMonoid R]

/-- The prefix meaning: the per-word lexicon composed multiplicatively over a token list,
`prodMeaning lex us w = (us.map (lex · w)).prod`. -/
def prodMeaning (lex : U → W → R) (us : List U) (w : W) : R :=
  (us.map (lex · w)).prod

@[simp] theorem prodMeaning_nil (lex : U → W → R) (w : W) : prodMeaning lex [] w = 1 := rfl

@[simp] theorem prodMeaning_cons (lex : U → W → R) (u : U) (us : List U) (w : W) :
    prodMeaning lex (u :: us) w = lex u w * prodMeaning lex us w := by
  simp [prodMeaning]

/-- Any permutation of the token list yields the same meaning. -/
theorem prodMeaning_perm {lex : U → W → R} {us us' : List U} (h : us.Perm us') (w : W) :
    prodMeaning lex us w = prodMeaning lex us' w :=
  (h.map _).prod_eq

end CommMonoid

section Order

variable [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem prodMeaning_nonneg {lex : U → W → R} (h : ∀ u w, 0 ≤ lex u w) (us : List U) (w : W) :
    0 ≤ prodMeaning lex us w :=
  List.prod_nonneg (List.forall_mem_map.2 fun u _ => h u w)

end Order

section Bounded

variable [CommMonoid R] [Preorder R] [MulLeftMono R]

theorem prodMeaning_le_one {lex : U → W → R} (h : ∀ u w, lex u w ≤ 1) (us : List U) (w : W) :
    prodMeaning lex us w ≤ 1 := by
  induction us with
  | nil => exact (prodMeaning_nil lex w).le
  | cons u us ih => exact (prodMeaning_cons lex u us w).trans_le (Left.mul_le_one (h u w) ih)

end Bounded

end RSA
