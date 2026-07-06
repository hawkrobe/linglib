/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Computability.Language
import Linglib.Core.Computability.Subregular.Language.Boundary
import Linglib.Core.Data.List.Factors

/-!
# Strictly local languages (SL_k)

A language `L` is **strictly `k`-local** when membership is determined by the
length-`k` substrings of the boundary-augmented input: a grammar is a set `G` of
permitted `k`-factors, and `w ∈ L` iff every `k`-factor of `boundary k w` lies in
`G`. The forbidden-factor dual (`G = Fᶜ`) is finite even over an infinite alphabet.

## Main definitions

* `Subregular.SLGrammar α` — a grammar is just a set of permitted factors over
  `Augmented α`; the locality width `k` is supplied to `language`, not baked in.
* `Subregular.SLGrammar.language k` — the `Language α` it generates at width `k`.
* `Subregular.SLGrammar.ofForbidden` — the grammar of a forbidden-factor set (its
  complement).
* `Language.IsStrictlyLocal L k` — `L` is strictly `k`-local.
-/

namespace Subregular

variable {α : Type*}

/-- A **strictly-local grammar** over `α`: a set of *permitted* factors over the
boundary-augmented alphabet `Option α` (`none` the boundary). The locality width
`k` is supplied to `language`, not baked into the carrier. -/
abbrev SLGrammar (α : Type*) := Set (Augmented α)

namespace SLGrammar

/-- The language generated at width `k`: strings whose boundary-augmented form has
every `k`-factor permitted. -/
def language (k : ℕ) (G : SLGrammar α) : Language α :=
  {w | ∀ f ∈ List.kFactors k (boundary k w), f ∈ G}

@[simp] lemma mem_language (k : ℕ) (G : SLGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ f ∈ List.kFactors k (boundary k w), f ∈ G :=
  Iff.rfl

/-- The grammar of a **forbidden**-factor set is its complement: a string is
accepted iff none of its `k`-factors are forbidden. -/
def ofForbidden (forbidden : Set (Augmented α)) : SLGrammar α := forbiddenᶜ

@[simp] lemma mem_ofForbidden_language (forbidden : Set (Augmented α)) (k : ℕ)
    (w : List α) :
    w ∈ (ofForbidden forbidden).language k
      ↔ ∀ f ∈ List.kFactors k (boundary k w), f ∉ forbidden :=
  Iff.rfl

/-! ### Count-vector characterisation

Membership in a forbidden-factor SL language is a zero-test of a single
linear functional of the word's `k`-factor count vector — the total count of
forbidden factors — with unit margin on nonmembers. Strict locality is thus
linearly detectable on the factor-count (cue) representation. -/

variable [DecidableEq α]

/-- SL membership is the vanishing of the forbidden-factor count. -/
theorem mem_ofForbidden_language_iff_sum_count_eq_zero
    (F : Finset (Augmented α)) (k : ℕ) (w : List α) :
    w ∈ (ofForbidden ↑F).language k
      ↔ ∑ f ∈ F, (List.kFactors k (boundary k w)).count f = 0 := by
  simp only [mem_ofForbidden_language, Finset.mem_coe, Finset.sum_eq_zero_iff,
             List.count_eq_zero]
  exact ⟨fun h f hf hmem => h f hmem hf, fun h f hmem hf => h f hf hmem⟩

/-- Nonmembers score at least `1` on the forbidden-factor count: the linear
    detector has unit margin. -/
theorem one_le_sum_count_of_not_mem_ofForbidden_language
    {F : Finset (Augmented α)} {k : ℕ} {w : List α}
    (h : w ∉ (ofForbidden ↑F).language k) :
    1 ≤ ∑ f ∈ F, (List.kFactors k (boundary k w)).count f :=
  Nat.one_le_iff_ne_zero.mpr fun h0 =>
    h ((mem_ofForbidden_language_iff_sum_count_eq_zero F k w).mpr h0)

end SLGrammar

end Subregular

namespace Language

variable {α : Type*}

open Subregular

/-- A language `L` is **strictly `k`-local** iff some `SLGrammar α` generates it at
width `k`. Witness-style, mirroring `Language.IsRegular`/`Language.IsContextFree`
("L is regular iff some DFA accepts L"). -/
def IsStrictlyLocal (L : Language α) (k : ℕ) : Prop :=
  ∃ G : SLGrammar α, G.language k = L

end Language
