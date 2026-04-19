/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Mathlib.Data.List.Infix

/-!
# Subregular Languages — Boundaries and `k`-Factors

Common infrastructure for the subregular hierarchy @cite{lambert-2022}
@cite{heinz-rogers-2010} @cite{rogers-pullum-2011}: boundary augmentation
of strings, contiguous `k`-factors with boundary padding, and the
factor-membership predicate that all of `StrictlyLocal`, `LocallyTestable`,
and their tier-relativized variants build on.

## Why `Option α` for boundaries

The canonical subregular convention extends the alphabet with edge markers
`⋊` (left) and `⋉` (right) and studies `k`-factors of `⋊ᵏ⁻¹ · w · ⋉ᵏ⁻¹`.
Mathlib's idiomatic way to extend an alphabet by one fresh symbol is
`Option α`: `none` is the new boundary, `some a` an original symbol. Two
distinct edges are unnecessary — boundary symbols only appear at fixed
positions by construction.

## Main definitions

* `Augmented α` — abbreviation for `List (Option α)`.
* `boundary k w` — `w.map some` padded with `k - 1` boundary symbols on
  each side.
* `kFactors k xs` — the contiguous length-`k` infixes of `xs`, built as
  `(xs.tails.filter (k ≤ ·.length)).map (·.take k)`.
-/

namespace Core.Computability.Subregular

variable {α β : Type*}

/-- A boundary-augmented string: an alphabet symbol or the boundary marker
`none`. Lambert's `⋊` and `⋉` collapse to the single `none` symbol here, since
edges only appear at fixed positions by construction. -/
abbrev Augmented (α : Type*) : Type _ := List (Option α)

/-- Boundary-augment a string with `k - 1` boundary markers on each side.
For `k ≤ 1` no padding is added (no `k`-factor can span the edge). -/
def boundary (k : ℕ) (w : List α) : Augmented α :=
  List.replicate (k - 1) none ++ w.map some ++ List.replicate (k - 1) none

@[simp] lemma boundary_one (w : List α) : boundary 1 w = w.map some := by
  simp [boundary]

lemma length_boundary (k : ℕ) (w : List α) :
    (boundary k w).length = w.length + 2 * (k - 1) := by
  simp [boundary]; omega

/-- The contiguous length-`k` infixes of `xs`. Built by enumerating suffixes
and taking each one's length-`k` prefix; suffixes shorter than `k` are
filtered out. -/
def kFactors (k : ℕ) (xs : List β) : List (List β) :=
  (xs.tails.filter (k ≤ ·.length)).map (·.take k)

/-- Every member of `kFactors k xs` has length exactly `k`. -/
lemma length_of_mem_kFactors {k : ℕ} {f xs : List β}
    (h : f ∈ kFactors k xs) : f.length = k := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨_, hlen⟩ := List.mem_filter.mp hs
  exact List.length_take_of_le (by simpa using hlen)

/-- A `k`-factor of `xs` is a contiguous infix of `xs`. The witness is a
prefix (`take`) of a suffix (`tails`), and prefix-of-suffix is infix. -/
lemma isInfix_of_mem_kFactors {k : ℕ} {f xs : List β}
    (h : f ∈ kFactors k xs) : f <:+: xs := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hs_tail, _⟩ := List.mem_filter.mp hs
  have hsuffix : s <:+ xs := (List.mem_tails ..).mp hs_tail
  exact (List.take_prefix _ s).isInfix.trans hsuffix.isInfix

instance [DecidableEq β] (k : ℕ) (f xs : List β) :
    Decidable (f ∈ kFactors k xs) := by
  unfold kFactors; infer_instance

end Core.Computability.Subregular
