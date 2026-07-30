/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.Sublists

/-!
# Strictly piecewise languages (SP_k)

A language `L` is **strictly `k`-piecewise** when membership is determined by which
*subsequences* (scattered, non-contiguous selections) of length at most `k` the input
contains [rogers-heinz-et-al-2010]. Where SL_k constrains adjacent material via contiguous
factors, SP_k constrains long-distance co-occurrence via subsequences.

## Main definitions

* `Subregular.SPGrammar α`: a set of permitted subsequences; the width `k` is
  supplied to `language`, not baked into the carrier.
* `Subregular.SPGrammar.language k`: the `Language α` it generates: every subsequence of
  `w` of length at most `k` must be permitted.
* `Language.IsStrictlyPiecewise L k`: `L` is strictly `k`-piecewise.

## Main results

* `Language.IsStrictlyPiecewise.mem_of_sublist`: SP languages are subsequence-closed.
* `Language.IsStrictlyPiecewise.succ`: `SP_k ⊆ SP_(k+1)`.

## Implementation notes

`List.Sublist` (`<+`) is mathlib's non-contiguous "is a subsequence of", exactly the
SP primitive. Unlike SL no boundary augmentation is needed, since subsequences are blind
to position; the "≤ k" (rather than "exactly k") bound is instead what keeps words shorter
than `k` distinguishable, matching `Subregular.subseqSet`.
-/

namespace Subregular

open List

/-- A **strictly-piecewise grammar** over `α`: a set of *permitted* subsequences.
Unlike SL grammars no boundary alphabet is used — subsequences are insensitive to
position. The width `k` is supplied to `language`, not baked into the carrier. -/
abbrev SPGrammar (α : Type*) := Set (List α)

namespace SPGrammar

variable {α : Type*}

/-- The language generated at width `k`: strings whose every subsequence of length at
most `k` is permitted. -/
def language (k : ℕ) (G : SPGrammar α) : Language α :=
  {w | ∀ s, s.length ≤ k → s <+ w → s ∈ G}

@[simp] lemma mem_language (k : ℕ) (G : SPGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ s, s.length ≤ k → s <+ w → s ∈ G :=
  Iff.rfl

/-- SP languages are **subsequence-closed**: deleting symbols cannot create a subsequence
that was not already there. -/
theorem mem_language_of_sublist {k : ℕ} {G : SPGrammar α} {v w : List α}
    (hvw : v <+ w) (hw : w ∈ G.language k) : v ∈ G.language k :=
  fun s hlen hs => hw s hlen (hs.trans hvw)

/-- Conjoining grammars conjoins their languages. -/
theorem language_inter (k : ℕ) (G₁ G₂ : SPGrammar α) :
    (G₁ ∩ G₂).language k = G₁.language k ⊓ G₂.language k := by
  ext w
  exact ⟨fun h => ⟨fun s hl hs => (h s hl hs).1, fun s hl hs => (h s hl hs).2⟩,
    fun h s hl hs => ⟨h.1 s hl hs, h.2 s hl hs⟩⟩

/-- SP membership reduces to a check against `List.sublistsLen` — a `decide`-friendly
characterisation used by the decidable-membership instance below. -/
theorem mem_language_iff_forall_mem_sublistsLen (k : ℕ) (G : SPGrammar α) (w : List α) :
    w ∈ G.language k ↔ ∀ j ≤ k, ∀ s ∈ w.sublistsLen j, s ∈ G := by
  refine ⟨fun h j hj s hs => ?_, fun h s hlen hs => h s.length hlen s ?_⟩
  · obtain ⟨hsub, rfl⟩ := List.mem_sublistsLen.mp hs
    exact h s hj hsub
  · exact List.mem_sublistsLen.mpr ⟨hs, rfl⟩

instance decidableMemLanguage (k : ℕ) (G : SPGrammar α)
    [DecidablePred (· ∈ G)] (w : List α) : Decidable (w ∈ G.language k) :=
  decidable_of_iff' _ (mem_language_iff_forall_mem_sublistsLen k G w)

end SPGrammar

end Subregular

namespace Language

variable {α : Type*} {L : Language α} {k : ℕ}

open List Subregular

/-- A language `L` is **strictly `k`-piecewise** iff some `SPGrammar α` generates it
at width `k`. -/
def IsStrictlyPiecewise (L : Language α) (k : ℕ) : Prop :=
  ∃ G : SPGrammar α, G.language k = L

/-- SP languages are subsequence-closed. -/
theorem IsStrictlyPiecewise.mem_of_sublist (h : L.IsStrictlyPiecewise k) {v w : List α}
    (hvw : v <+ w) (hw : w ∈ L) : v ∈ L := by
  obtain ⟨G, rfl⟩ := h; exact SPGrammar.mem_language_of_sublist hvw hw

/-- A nonempty SP language contains the empty word. -/
theorem IsStrictlyPiecewise.nil_mem (h : L.IsStrictlyPiecewise k) {w : List α}
    (hw : w ∈ L) : [] ∈ L :=
  h.mem_of_sublist (List.nil_sublist w) hw

/-- **`SP_k ⊆ SP_(k+1)`**: widening the window loses nothing, since the width-`(k+1)`
grammar can demand exactly that all length-`≤ k` subsequences be permitted. -/
theorem IsStrictlyPiecewise.succ (h : L.IsStrictlyPiecewise k) :
    L.IsStrictlyPiecewise (k + 1) := by
  obtain ⟨G, rfl⟩ := h
  refine ⟨{s | ∀ t, t.length ≤ k → t <+ s → t ∈ G}, ?_⟩
  ext w
  exact ⟨fun hw s hlen hs => hw s (hlen.trans (Nat.le_succ k)) hs s hlen (List.Sublist.refl s),
    fun hw s _ hs t hlen ht => hw t hlen (ht.trans hs)⟩

end Language
