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

The canonical subregular convention is to extend the alphabet with edge
markers `⋊` (left) and `⋉` (right) and then study `k`-factors of the
augmented string `⋊ᵏ⁻¹ · w · ⋉ᵏ⁻¹`. Mathlib's idiomatic way to extend
an alphabet by a single fresh symbol is `Option α`: `none` is the new
boundary, `some a` is the original symbol. Two distinct edges are not
needed — boundary symbols only appear at fixed positions by construction,
so `(none, a)` reads as "starts with a" and `(b, none)` reads as "ends
with b" without ambiguity.

This is the same trick `Mathlib.Computability.Language` uses everywhere
strings live in `List α` over a parametric alphabet, and means a
subregular grammar is just a `Finset (List (Option α))` of permitted
`k`-factors — directly comparable with `Language (Option α)` from
mathlib.

## Main definitions

- `boundary k w : List (Option α)` — augment `w` with `k - 1` boundary
  symbols on each side.
- `kFactors k xs : Finset (List (Option α))` — the multiset-as-set of
  contiguous length-`k` infixes of `xs`.
- `Augmented α := List (Option α)` — abbreviation for boundary-augmented
  strings.

## Connection to `Mathlib.Computability.Language`

A subregular language over `α` is a `Language α` whose membership
predicate factors through `kFactors k ∘ boundary k`. `StrictlyLocal.lean`
makes this connection explicit.
-/

namespace Core.Computability.Subregular

universe u v

variable {α : Type u} {β : Type v}

-- ============================================================================
-- § 1: Boundary augmentation
-- ============================================================================

/-- A boundary-augmented string: an alphabet symbol or the boundary marker
    `none`. Lambert's `⋊` and `⋉` collapse to the single `none` symbol
    here, since edges only appear at fixed positions by construction. -/
abbrev Augmented (α : Type u) : Type u := List (Option α)

/-- Lift an unaugmented string into the augmented alphabet. -/
def lift (w : List α) : Augmented α := w.map some

@[simp] theorem lift_nil : lift ([] : List α) = [] := rfl

@[simp] theorem lift_cons (a : α) (w : List α) :
    lift (a :: w) = some a :: lift w := rfl

@[simp] theorem length_lift (w : List α) : (lift w).length = w.length :=
  List.length_map ..

/-- Boundary-augment a string with `k - 1` boundary markers on each side.
    For `k = 0` and `k = 1` no padding is added (no `k`-factor can span
    the edge). -/
def boundary (k : ℕ) (w : List α) : Augmented α :=
  List.replicate (k - 1) none ++ lift w ++ List.replicate (k - 1) none

@[simp] theorem boundary_zero (w : List α) : boundary 0 w = lift w := by
  simp [boundary]

@[simp] theorem boundary_one (w : List α) : boundary 1 w = lift w := by
  simp [boundary]

theorem length_boundary (k : ℕ) (w : List α) :
    (boundary k w).length = w.length + 2 * (k - 1) := by
  simp [boundary]; omega

-- ============================================================================
-- § 2: `k`-Factors
-- ============================================================================

/-- The contiguous length-`k` prefixes-of-suffixes of `xs`. The encoding
    keeps duplicate factors collapsed at the `Set` level — what matters
    for SL is which factors *occur*, not how many times. We list every
    suffix-prefix of length `k`; suffixes shorter than `k` contribute
    nothing. -/
def kFactorsList (k : ℕ) : List β → List (List β)
  | [] => []
  | x :: xs =>
      if k ≤ (x :: xs).length
      then ((x :: xs).take k) :: kFactorsList k xs
      else kFactorsList k xs

/-- `k`-factor membership as a `Prop` predicate. Decidable when factors
    have decidable equality (the standard finite-alphabet case). -/
def IsKFactor (k : ℕ) (f xs : List β) : Prop :=
  f ∈ kFactorsList k xs

instance [DecidableEq β] (k : ℕ) (f xs : List β) :
    Decidable (IsKFactor k f xs) := by
  unfold IsKFactor; infer_instance

/-- Every `k`-factor has length exactly `k`. -/
theorem length_of_mem_kFactorsList {k : ℕ} {f xs : List β}
    (h : f ∈ kFactorsList k xs) : f.length = k := by
  induction xs with
  | nil => simp [kFactorsList] at h
  | cons x xs ih =>
    rw [kFactorsList] at h
    by_cases hk : k ≤ (x :: xs).length
    · rw [if_pos hk] at h
      rcases List.mem_cons.mp h with heq | hmem
      · subst heq; exact List.length_take_of_le hk
      · exact ih hmem
    · rw [if_neg hk] at h
      exact ih h

/-- Helper: extending an infix by one symbol on the left. -/
private theorem isInfix_cons_right {f xs : List β} (a : β) (h : f <:+: xs) :
    f <:+: (a :: xs) := by
  obtain ⟨s, t, hst⟩ := h
  exact ⟨a :: s, t, by simp [← hst]⟩

/-- A `k`-factor of `xs` is a contiguous infix of `xs`. -/
theorem isInfix_of_mem_kFactorsList {k : ℕ} {f xs : List β}
    (h : f ∈ kFactorsList k xs) : f <:+: xs := by
  induction xs with
  | nil => simp [kFactorsList] at h
  | cons x xs ih =>
    rw [kFactorsList] at h
    by_cases hk : k ≤ (x :: xs).length
    · rw [if_pos hk] at h
      rcases List.mem_cons.mp h with heq | hmem
      · subst heq; exact ⟨[], (x :: xs).drop k, by simp⟩
      · exact isInfix_cons_right x (ih hmem)
    · rw [if_neg hk] at h
      exact isInfix_cons_right x (ih h)

end Core.Computability.Subregular
