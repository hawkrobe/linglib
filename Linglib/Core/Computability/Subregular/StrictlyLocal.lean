/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Linglib.Core.Computability.Subregular.Defs
import Linglib.Core.Data.List.Factors

/-!
# Strictly Local Languages (SL_k)

A language `L` is **strictly `k`-local** when membership is determined by the
length-`k` substrings of the boundary-augmented input [rogers-pullum-2011]
[lambert-2022]: a grammar is a set `G` of permitted `k`-factors, and `w ∈ L` iff
every `k`-factor of `boundary k w` lies in `G`. Phonology usually states the
*forbidden* dual (`G = Fᶜ`), finite even over an infinite alphabet.

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

end SLGrammar

/-- A language `L` is **strictly `k`-local** iff some `SLGrammar α` generates it at
width `k`. Witness-style, mirroring `Language.IsRegular`/`Language.IsContextFree`
("L is regular iff some DFA accepts L"). -/
def _root_.Language.IsStrictlyLocal (L : Language α) (k : ℕ) : Prop :=
  ∃ G : SLGrammar α, G.language k = L

/-- Every SL grammar witnesses `Language.IsStrictlyLocal` for its language. -/
lemma SLGrammar.isStrictlyLocal_language (k : ℕ) (G : SLGrammar α) :
    (G.language k).IsStrictlyLocal k :=
  ⟨G, rfl⟩

end Subregular
