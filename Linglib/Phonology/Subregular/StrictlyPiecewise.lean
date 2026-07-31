/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.ShuffleIdeal
import Linglib.Core.Computability.PiecewiseTestable

/-!
# Strictly piecewise languages (SP_k)

A language `L` is **strictly `k`-piecewise** when membership is determined by which
*subsequences* (scattered, non-contiguous selections) of length at most `k` the input
contains [rogers-heinz-et-al-2010]. Where SL_k constrains adjacent material via contiguous
factors, SP_k constrains long-distance co-occurrence — the subregular class of
unbounded-distance phonotactics. The class is the program's vocabulary for the sublist-closed
languages of `Linglib.Core.Computability.ShuffleIdeal`: a language is SP at *some* width iff
it is sublist-closed.

## Main definitions

* `SPGrammar α`: a set of permitted subsequences; the width `k` is supplied to `language`,
  not baked into the carrier.
* `SPGrammar.language k`: the `Language α` it generates: every subsequence of `w` of length
  at most `k` must be permitted.
* `Language.IsStrictlyPiecewise L k`: `L` is a fixed point of the width-`k` test with itself
  as grammar; `isStrictlyPiecewise_iff` recovers the ∃-grammar form.

## Main results

* `Language.IsStrictlyPiecewise.mem_of_sublist`: SP languages are subsequence-closed.
* `Language.IsStrictlyPiecewise.succ`: `SP_k ⊆ SP_(k+1)`.
* `Language.IsStrictlyPiecewise.toIsPiecewiseTestable`: `SP_k ⊆ PT_k`.
* `Language.isStrictlyPiecewise_avoid`: shuffle-ideal complements are SP.
* `Language.exists_isStrictlyPiecewise_iff_isSublistClosed`: SP at some width is exactly
  sublist-closure [rogers-heinz-et-al-2010].

## Implementation notes

`List.Sublist` (`<+`) is mathlib's non-contiguous "is a subsequence of", exactly the SP
primitive. Unlike SL no boundary augmentation is needed, since subsequences are blind to
position; the "≤ k" (rather than "exactly k") bound is instead what keeps words shorter than
`k` distinguishable, matching `subseqSet`.
-/

open List

/-- A **strictly-piecewise grammar** over `α`: a set of *permitted* subsequences
[rogers-heinz-et-al-2010]. Unlike SL grammars no boundary alphabet is used — subsequences
are insensitive to position. The width `k` is supplied to `language`, not baked into the
carrier. -/
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

namespace Language

variable {α : Type*} {L : Language α} {k : ℕ}

open List

/-- A language `L` is **strictly `k`-piecewise** when the width-`k` subsequence test with
`L` itself as the permitted set recovers `L` — the canonical-grammar fixed point;
`isStrictlyPiecewise_iff` recovers the ∃-grammar form. -/
def IsStrictlyPiecewise (L : Language α) (k : ℕ) : Prop :=
  SPGrammar.language k L = L

/-- Some grammar generates `L` at width `k` iff `L` is its own grammar. -/
theorem isStrictlyPiecewise_iff :
    L.IsStrictlyPiecewise k ↔ ∃ G : SPGrammar α, G.language k = L := by
  refine ⟨fun h => ⟨L, h⟩, ?_⟩
  rintro ⟨G, rfl⟩
  show SPGrammar.language k _ = _
  exact le_antisymm (fun w hw s hlen hs => hw s hlen hs s hlen (Sublist.refl s))
    fun w hw s hlen hs => SPGrammar.mem_language_of_sublist hs hw

/-- SP languages are subsequence-closed. -/
theorem IsStrictlyPiecewise.mem_of_sublist (h : L.IsStrictlyPiecewise k) {v w : List α}
    (hvw : v <+ w) (hw : w ∈ L) : v ∈ L := by
  rw [← h] at hw ⊢
  exact SPGrammar.mem_language_of_sublist hvw hw

/-- A nonempty SP language contains the empty word. -/
theorem IsStrictlyPiecewise.nil_mem (h : L.IsStrictlyPiecewise k) {w : List α}
    (hw : w ∈ L) : [] ∈ L :=
  h.mem_of_sublist (List.nil_sublist w) hw

/-- **Avoiding one pattern**: the complement of a shuffle ideal is strictly `k`-piecewise
as soon as the forbidden pattern fits in the window. -/
theorem isStrictlyPiecewise_avoid {p : List α} (hp : p.length ≤ k) :
    (shuffleIdeal p)ᶜ.IsStrictlyPiecewise k :=
  le_antisymm (fun _ hw hpw => hw p hp hpw (Sublist.refl p))
    fun _ hw _ _ hs hps => hw (hps.trans hs)

/-- **`SP_k ⊆ SP_(k+1)`**: widening the window loses nothing. -/
theorem IsStrictlyPiecewise.succ (h : L.IsStrictlyPiecewise k) :
    L.IsStrictlyPiecewise (k + 1) := by
  refine le_antisymm (fun w hw => ?_) fun w hw s _ hs => h.mem_of_sublist hs hw
  rw [← h]
  exact fun s hlen hs => hw s (hlen.trans (Nat.le_succ k)) hs

/-- **`SP_k ⊆ PT_k`**: the strictly-piecewise test ("every subsequence of length at most `k`
is permitted") depends only on `subseqSet k`. -/
theorem IsStrictlyPiecewise.toIsPiecewiseTestable (h : L.IsStrictlyPiecewise k) :
    L.IsPiecewiseTestable k := by
  obtain ⟨G, rfl⟩ := isStrictlyPiecewise_iff.mp h
  refine fun w₁ w₂ heq => propext ⟨fun hw s hlen hs => ?_, fun hw s hlen hs => ?_⟩
  · exact hw s hlen ((subseqSet_eq_iff heq hlen).mpr hs)
  · exact hw s hlen ((subseqSet_eq_iff heq hlen).mp hs)

/-- A language is strictly piecewise at some width iff it is sublist-closed
[rogers-heinz-et-al-2010]. Backwards, `L` is its own grammar at the width bounding the
finite forbidden basis, so that any word outside `L` is already refuted by a basis word it
contains. -/
theorem exists_isStrictlyPiecewise_iff_isSublistClosed [Finite α] :
    (∃ k, L.IsStrictlyPiecewise k) ↔ L.IsSublistClosed := by
  refine ⟨fun ⟨_, hk⟩ _ _ hvw hw => hk.mem_of_sublist hvw hw, fun hL => ?_⟩
  obtain ⟨F, hF⟩ := hL.exists_finset_compl_eq_biSup_shuffleIdeal
  have hFmem : ∀ w, w ∈ Lᶜ ↔ ∃ m ∈ F, m <+ w := fun w => by
    rw [show Lᶜ = _ from hF]; simp [Language.mem_iSup]
  refine ⟨F.sup List.length, le_antisymm (fun w h => by_contra fun hwL => ?_)
    fun w hw s _ hs => hL hs hw⟩
  obtain ⟨m, hm, hmw⟩ := (hFmem w).mp hwL
  exact (hFmem m).mpr ⟨m, hm, Sublist.refl m⟩ (h m (Finset.le_sup hm) hmw)

end Language
