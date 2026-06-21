/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.Sublists

/-!
# Strictly Piecewise Languages (SP_k)

A language `L` is **strictly `k`-piecewise** when membership is determined by which
length-`k` *subsequences* (scattered, non-contiguous selections) the input contains
[rogers-pullum-2011] [lambert-2022]. Whereas SL_k constrains adjacent material via
*factors* (contiguous infixes), SP_k constrains long-distance co-occurrence via
*subsequences*.

## Why subsequences (not factors)

The two locality dimensions in the subregular hierarchy are *adjacency-based*
(SL/LT/LTT, contiguous `k`-factors) and *precedence-based* (SP, `k`-element
subsequences). A long-distance pattern such as sibilant harmony — *sasi* but not
*saʃi* — is naturally SP_2: the forbidden length-2 subsequence is `[s, ʃ]`,
regardless of intervening material. No boundary augmentation is needed: subsequences
are blind to position, so edge markers add no information [heinz-rogers-2010].

## Main definitions

* `Subregular.SPGrammar α` — a grammar is a set of permitted length-`k`
  subsequences; the width `k` is supplied to `language`.
* `Subregular.SPGrammar.language k` — the `Language α` it generates: every length-`k`
  subsequence of `w` must be permitted.
* `Language.IsStrictlyPiecewise L k` — `L` is strictly `k`-piecewise.

The relation `List.Sublist` (`<+`) is mathlib's "is a (non-contiguous) subsequence
of" — exactly what SP needs.
-/

namespace Subregular

open List

variable {α : Type*}

/-- A **strictly-piecewise grammar** over `α`: a set of *permitted* subsequences.
Unlike SL grammars no boundary alphabet is used — subsequences are insensitive to
position. The width `k` is supplied to `language`, not baked into the carrier. -/
abbrev SPGrammar (α : Type*) := Set (List α)

namespace SPGrammar

/-- The language generated at width `k`: strings whose every length-`k` subsequence
is permitted. -/
def language (k : ℕ) (G : SPGrammar α) : Language α :=
  {w | ∀ s, s.length = k → s <+ w → s ∈ G}

@[simp] lemma mem_language (k : ℕ) (G : SPGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ s, s.length = k → s <+ w → s ∈ G :=
  Iff.rfl

/-- SP membership reduces to a check against `List.sublists` — a `decide`-friendly
characterisation used by the decidable-membership instance below. -/
lemma mem_language_iff_forall_sublists (k : ℕ) (G : SPGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ s ∈ w.sublists, s.length = k → s ∈ G := by
  refine ⟨fun h s hs hlen => h s hlen (List.mem_sublists.mp hs),
          fun h s hlen hs => h s (List.mem_sublists.mpr hs) hlen⟩

instance decidableMemLanguage (k : ℕ) (G : SPGrammar α)
    [DecidablePred (· ∈ G)] (w : List α) : Decidable (w ∈ G.language k) :=
  decidable_of_iff _ (mem_language_iff_forall_sublists k G w).symm

end SPGrammar

/-- A language `L` is **strictly `k`-piecewise** iff some `SPGrammar α` generates it
at width `k`. -/
def _root_.Language.IsStrictlyPiecewise (L : Language α) (k : ℕ) : Prop :=
  ∃ G : SPGrammar α, G.language k = L

/-- Every SP grammar witnesses `Language.IsStrictlyPiecewise` for its language. -/
lemma SPGrammar.isStrictlyPiecewise_language (k : ℕ) (G : SPGrammar α) :
    (G.language k).IsStrictlyPiecewise k :=
  ⟨G, rfl⟩

end Subregular
