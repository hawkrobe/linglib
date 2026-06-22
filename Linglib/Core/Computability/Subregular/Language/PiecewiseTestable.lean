/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Language
import Linglib.Core.Computability.Subregular.Language.StrictlyPiecewise
import Mathlib.Computability.Language

/-!
# Piecewise testable languages (PT_k)

A language is **piecewise `k`-testable** when its membership depends only on the set of
length-`≤ k` subsequences (scattered subwords) of the input [simon-1975] — i.e. it is
invariant under the map `subseqSet k`. PT_k is the Boolean closure of SP_k, the
piecewise analogue of locally testable over strictly local.

## Main definitions

* `subseqSet k w` — the subsequences of `w` of length `≤ k`.
* `Language.IsPiecewiseTestable L k` — `L.InvariantUnder (subseqSet k)`.

## Main results

* `Language.IsStrictlyPiecewise.toIsPiecewiseTestable` — `SP_k ⊆ PT_k`.
* Closure under complement is inherited from `Language.InvariantUnder.compl`.
-/

namespace Subregular

open List

variable {α : Type*}

/-- The subsequences of `w` of length **at most** `k`. The "≤ k" (rather than
"exactly k") bound is what keeps strings shorter than `k` distinguishable. -/
def subseqSet (k : ℕ) (w : List α) : Set (List α) :=
  { s | s <+ w ∧ s.length ≤ k }

@[simp] lemma mem_subseqSet {k : ℕ} {s w : List α} :
    s ∈ subseqSet k w ↔ s <+ w ∧ s.length ≤ k :=
  Iff.rfl

/-- Subsequences of length at most `k` are interchangeable across strings sharing
their `subseqSet k`. The ratchet for proving piecewise testability from a predicate
depending only on length-`≤ k` subsequence presence. -/
lemma subseqSet_eq_iff {k : ℕ} {w₁ w₂ : List α}
    (heq : subseqSet k w₁ = subseqSet k w₂) {s : List α} (hlen : s.length ≤ k) :
    s <+ w₁ ↔ s <+ w₂ := by
  simpa [hlen] using Set.ext_iff.mp heq s

end Subregular

namespace Language

open _root_.Subregular

variable {α : Type*}

/-- A language is **piecewise `k`-testable**: membership factors through the
length-`≤ k` subsequence set `subseqSet k`. -/
def IsPiecewiseTestable (L : Language α) (k : ℕ) : Prop :=
  L.InvariantUnder (subseqSet k)

/-- Pointwise form: strings with equal `subseqSet k` are `L`-equivalent. -/
lemma isPiecewiseTestable_iff {L : Language α} {k : ℕ} :
    L.IsPiecewiseTestable k ↔
      ∀ w₁ w₂, subseqSet k w₁ = subseqSet k w₂ → (w₁ ∈ L ↔ w₂ ∈ L) :=
  ⟨fun h _ _ h' => h.iff h', fun h => InvariantUnder.mk fun _ _ h' => h _ _ h'⟩

/-- **SP_k ⊆ PT_k**: the strictly-piecewise test ("every length-`k` subsequence is
permitted") depends only on the set of subsequences of that length. -/
theorem IsStrictlyPiecewise.toIsPiecewiseTestable {k : ℕ} {L : Language α}
    (h : L.IsStrictlyPiecewise k) : L.IsPiecewiseTestable k := by
  obtain ⟨G, rfl⟩ := h
  refine InvariantUnder.mk fun w₁ w₂ heq => ⟨fun hw s hlen hs => ?_, fun hw s hlen hs => ?_⟩
  · exact hw s hlen ((subseqSet_eq_iff heq hlen.le).mpr hs)
  · exact hw s hlen ((subseqSet_eq_iff heq hlen.le).mp hs)

end Language
