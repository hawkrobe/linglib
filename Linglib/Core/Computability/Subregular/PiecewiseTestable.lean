/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.StrictlyPiecewise

/-!
# Piecewise Testable Languages (PT_k)

A language `L` is **piecewise `k`-testable** when membership depends only
on which length-`k` *subsequences* the input contains [simon-1975]
[rogers-pullum-2011] [lambert-2022]. PT is to SP what LT is to
SL: the Boolean closure of the strictly variant.

Both are *property-based* (extensional) classifications — there is no
canonical grammar, only an indistinguishability relation on strings:
`w₁ ~_PT w₂` iff their `k`-subsequence sets coincide. `L` is PT_k iff it
is closed under `~_PT`.

## Lambert (2026) and the multitier extension

The multitier closure of PT (which Lambert classifies as 𝒥) covers a
large fraction of attested phonotactic constraints — including the
piecewise-testable analyses of unbounded stress patterns surveyed in
[lambert-2026] §3 and the Karanga Shona tone analysis (which is
piecewise testable but not multitier generalised definite). The
substrate sits adjacent to `Multitier.lean` and is composed via
`IsBTC IsPiecewiseTestable`.

## Main definitions

* `subseqSet k w` — the set of length-`k` subsequences of `w`.
* `IsPiecewiseTestable k L` — closure of `L` under equality of `subseqSet`.

The cast `IsStrictlyPiecewise k L → IsPiecewiseTestable k L` lives at
the end of the file (mathlib convention: cast lives with the larger class).
-/

namespace Subregular

open List

variable {α : Type*}

/-- The set of subsequences of `w` of length **at most** `k`. The PT
indistinguishability relation `w₁ ~_PT w₂` is equality of
`subseqSet k w₁` and `subseqSet k w₂`.

The "up to `k`" semantics matches [simon-1975] and the Heinz/Lambert
literature ([lambert-2026] Def 11; [heinz-2018]). The "exactly
`k`" alternative would mis-classify languages that distinguish strings
of length less than `k` (e.g. Luganda high-tone plateauing
[lambert-2026] (37) distinguishes `[h]` from `[ℓ]` while their
length-3 subsequence sets are both empty). Unlike `factorSet`, no
boundary augmentation: SP/PT are insensitive to position. -/
def subseqSet (k : ℕ) (w : List α) : Set (List α) :=
  { s | s <+ w ∧ s.length ≤ k }

@[simp] lemma mem_subseqSet {k : ℕ} {s w : List α} :
    s ∈ subseqSet k w ↔ s <+ w ∧ s.length ≤ k :=
  Iff.rfl

/-- A language is **piecewise `k`-testable** iff strings with the same set
of length-≤-`k` subsequences are either both in `L` or both out. -/
def IsPiecewiseTestable (k : ℕ) (L : Language α) : Prop :=
  ∀ w₁ w₂ : List α, subseqSet k w₁ = subseqSet k w₂ → (w₁ ∈ L ↔ w₂ ∈ L)

/-- Subsequences of length at most `k` are interchangeable across strings
sharing their `subseqSet k`. The standard ratchet for proving
`IsPiecewiseTestable k L` from a predicate that depends only on
length-≤-`k` subsequence presence. -/
lemma subseqSet_eq_iff {k : ℕ} {w₁ w₂ : List α}
    (heq : subseqSet k w₁ = subseqSet k w₂) {s : List α} (hlen : s.length ≤ k) :
    s <+ w₁ ↔ s <+ w₂ := by
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have h₁ : s ∈ subseqSet k w₁ := ⟨hs, hlen⟩
    rw [heq] at h₁
    exact h₁.1
  · have h₂ : s ∈ subseqSet k w₂ := ⟨hs, hlen⟩
    rw [← heq] at h₂
    exact h₂.1

/-- **SP_k ⊆ PT_k**: every strictly-`k`-piecewise language is piecewise
`k`-testable. The SP test ("every length-`k` subsequence is permitted")
trivially depends only on the *set* of subsequences of that length. -/
theorem IsStrictlyPiecewise.toIsPiecewiseTestable {k : ℕ} {L : Language α}
    (h : IsStrictlyPiecewise k L) : IsPiecewiseTestable k L := by
  obtain ⟨G, rfl⟩ := h
  intro w₁ w₂ heq
  refine ⟨fun hw s hlen hs => hw s hlen ?_, fun hw s hlen hs => hw s hlen ?_⟩
  · exact (subseqSet_eq_iff heq hlen.le).mpr hs
  · exact (subseqSet_eq_iff heq hlen.le).mp hs

end Subregular
