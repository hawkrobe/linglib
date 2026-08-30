import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Monotone.Defs

/-!
# Verb Cluster Bindings

Framework-agnostic type for verb cluster NP-verb binding patterns.

A verb cluster binding σ : Equiv.Perm (Fin n) maps each NP position (0-indexed)
to the surface position of the verb it binds to. The two canonical patterns:

- **Cross-serial** (Dutch): σ = identity — NP₁→V₁, NP₂→V₂, ...
- **Nested** (German): σ = reverse — NP₁→Vₙ, NP₂→Vₙ₋₁, ...

The key structural property: two arcs (i, n+σ(i)) and (j, n+σ(j)) with
i < j cross iff σ(i) < σ(j). Cross-serial (identity) has all concordant
pairs → maximally non-projective. Nested (reverse) has all discordant
pairs → fully projective.

Using `Equiv.Perm` (Mathlib) gives bijectivity by construction, `DecidableEq`,
and group structure. Projectivity is characterized as `Antitone σ`.
-/

namespace Features

/-- Verb cluster binding: a permutation on n verb positions.
    `σ i` gives the surface position (among verbs) of the verb that NP_i binds to. -/
abbrev VerbClusterBinding (n : Nat) := Equiv.Perm (Fin n)

namespace VerbClusterBinding

variable {n : Nat}

/-- Cross-serial binding: NP_i → V_i (identity permutation, Dutch pattern). -/
abbrev identity (n : Nat) : VerbClusterBinding n := Equiv.refl (Fin n)

/-- Nested binding: NP_i → V_{n−1−i} (reversal permutation, German pattern).
    Self-inverse: reversing twice is the identity. -/
def reverse (n : Nat) : VerbClusterBinding n :=
  { toFun := λ i => ⟨n - 1 - i.val, by omega⟩
  , invFun := λ i => ⟨n - 1 - i.val, by omega⟩
  , left_inv := λ i => by ext; simp; omega
  , right_inv := λ i => by ext; simp; omega }

-- Display

/-- Convert a binding to a list of verb positions for display. -/
def toList (σ : VerbClusterBinding n) : List Nat :=
  (List.range n).map λ i =>
    if hi : i < n then (σ ⟨i, hi⟩).val else 0

instance : Repr (VerbClusterBinding n) where
  reprPrec σ _ := repr (toList σ)

-- Arc Crossing and Projectivity

/-- Whether any two binding arcs cross. Two arcs (i, n+σ(i)) and (j, n+σ(j))
    with i < j cross iff σ(i) < σ(j) — a concordant pair.

    Since all NPs precede all verbs, an arc from NP_i to V_{σ(i)} spans
    [i, n+σ(i)]. For i < j, arc i's right endpoint is n+σ(i) and arc j's
    right endpoint is n+σ(j). They cross iff the right endpoints are in the
    same order as the left endpoints, i.e., σ(i) < σ(j). -/
private def hasCrossing (σ : VerbClusterBinding n) : Bool :=
  (List.range n).any λ i =>
    (List.range n).any λ j =>
      if hi : i < n then
        if hj : j < n then
          i < j && (σ ⟨i, hi⟩).val < (σ ⟨j, hj⟩).val
        else false
      else false

/-- A binding is projective iff no two arcs cross (no concordant pairs).
    Projective = nested (German), non-projective = cross-serial (Dutch). -/
def isProjective (σ : VerbClusterBinding n) : Bool := !hasCrossing σ

/-- Projectivity = antitone binding: i ≤ j → σ j ≤ σ i.
    Equivalently, no concordant pairs exist. -/
private theorem hasCrossing_iff {σ : VerbClusterBinding n} :
    hasCrossing σ = true ↔ ∃ i j : Fin n, i < j ∧ σ i < σ j := by
  simp only [hasCrossing]
  constructor
  · intro h
    rw [List.any_eq_true] at h
    obtain ⟨i, hi_mem, h_inner⟩ := h
    rw [List.mem_range] at hi_mem
    rw [List.any_eq_true] at h_inner
    obtain ⟨j, hj_mem, hP⟩ := h_inner
    rw [List.mem_range] at hj_mem
    simp only [show i < n from hi_mem, show j < n from hj_mem, dite_true,
      Bool.and_eq_true, decide_eq_true_eq] at hP
    exact ⟨⟨i, hi_mem⟩, ⟨j, hj_mem⟩, hP.1, hP.2⟩
  · intro ⟨i, j, hij, hlt⟩
    rw [List.any_eq_true]
    refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
    rw [List.any_eq_true]
    refine ⟨j.val, List.mem_range.mpr j.isLt, ?_⟩
    simp only [show i.val < n from i.isLt, show j.val < n from j.isLt, dite_true,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hij, hlt⟩

theorem isProjective_iff_antitone {σ : VerbClusterBinding n} :
    isProjective σ = true ↔ Antitone (σ : Fin n → Fin n) := by
  simp only [isProjective]
  rw [Bool.not_eq_true']
  constructor
  · -- No crossings → antitone
    intro h i j hij
    rcases eq_or_lt_of_le hij with rfl | hij_lt
    · exact le_refl _
    · by_contra hlt
      have hcross : hasCrossing σ = true := by
        rw [hasCrossing_iff]
        exact ⟨i, j, hij_lt, not_le.mp hlt⟩
      simp [hcross] at h
  · -- Antitone → no crossings
    intro h
    rw [Bool.eq_false_iff]
    intro habs
    rw [hasCrossing_iff] at habs
    obtain ⟨i, j, hij, hlt⟩ := habs
    exact absurd hlt (not_lt.mpr (h (le_of_lt hij)))

-- Key Theorems

/-- Cross-serial (identity) binding is non-projective for n ≥ 2. -/
theorem identity_not_projective (hn : n ≥ 2) :
    isProjective (identity n) = false := by
  simp only [isProjective, hasCrossing, identity]
  rw [Bool.not_eq_false']
  rw [List.any_eq_true]
  refine ⟨0, List.mem_range.mpr (by omega), ?_⟩
  rw [List.any_eq_true]
  refine ⟨1, List.mem_range.mpr (by omega), ?_⟩
  simp only [show (0 : Nat) < n from by omega, show (1 : Nat) < n from by omega,
    dite_true, Nat.zero_lt_one, Bool.true_and, decide_true, Equiv.refl_apply]

/-- Nested (reverse) binding is projective: no concordant pairs.
    For all i < j, σ(i) = n−1−i > n−1−j = σ(j), so all pairs are discordant.
    Equivalently, `reverse` is antitone. -/
theorem reverse_is_projective : isProjective (reverse n) = true := by
  rw [isProjective_iff_antitone]
  intro i j hij
  simp only [reverse, Equiv.coe_fn_mk, Fin.mk_le_mk]
  omega

end VerbClusterBinding

-- Derived Classification

/-- Classification of binding patterns, derived from the binding.
    Replaces the old `DependencyPattern` enum — now computed, not stored. -/
inductive BindingPattern where
  | crossSerial  -- Identity permutation (NP_i → V_i)
  | nested       -- Reversal permutation (NP_i → V_{n−1−i})
  | other        -- Any other permutation
  deriving DecidableEq, Repr

/-- Classify a binding as cross-serial, nested, or other.
    Uses `DecidableEq (Equiv.Perm (Fin n))` for direct equality checks. -/
def VerbClusterBinding.pattern {n : Nat} (σ : VerbClusterBinding n) : BindingPattern :=
  if σ = Equiv.refl (Fin n) then .crossSerial
  else if σ = VerbClusterBinding.reverse n then .nested
  else .other

end Features
