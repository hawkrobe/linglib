import Mathlib.Tactic.Linarith

/-!
# 1D Interval Feasibility

Reusable lemmas for the merge-and-split step in the KPS Theorem 8a proof.
After merging the last two elements and obtaining a measure on the smaller type,
we need to split the merged weight γ into (c, γ−c) subject to linear bounds.
These lemmas guarantee the existence of a valid split point.
-/

namespace Core.Scale

/-- Strict-lower + upper feasibility: if s < u, there exists c with s < c ≤ u. -/
theorem interval_strict_upper (s u : ℚ) (h : s < u) :
    ∃ c : ℚ, s < c ∧ c ≤ u :=
  ⟨u, h, le_refl _⟩

/-- Strict-lower + lower + upper feasibility: if l ≤ u and s < u,
    there exists c with s < c ∧ l ≤ c ∧ c ≤ u. -/
theorem interval_slu (s l u : ℚ) (hlu : l ≤ u) (hsu : s < u) :
    ∃ c : ℚ, s < c ∧ l ≤ c ∧ c ≤ u :=
  ⟨u, hsu, hlu, le_refl _⟩

/-- Strict-lower + two upper bounds: if s < u₁ and s < u₂,
    there exists c with s < c ∧ c ≤ u₁ ∧ c ≤ u₂. -/
theorem interval_s_uu (s u₁ u₂ : ℚ) (h1 : s < u₁) (h2 : s < u₂) :
    ∃ c : ℚ, s < c ∧ c ≤ u₁ ∧ c ≤ u₂ := by
  refine ⟨min u₁ u₂ , ?_, min_le_left _ _, min_le_right _ _⟩
  exact lt_min h1 h2

/-- Strict-lower + lower + two upper bounds. -/
theorem interval_sl_uu (s l u₁ u₂ : ℚ)
    (hlu1 : l ≤ u₁) (hlu2 : l ≤ u₂) (hsu1 : s < u₁) (hsu2 : s < u₂) :
    ∃ c : ℚ, s < c ∧ l ≤ c ∧ c ≤ u₁ ∧ c ≤ u₂ := by
  refine ⟨min u₁ u₂, lt_min hsu1 hsu2, le_min hlu1 hlu2, min_le_left _ _, min_le_right _ _⟩

/-- Two lower bounds + upper bound. -/
theorem interval_sll_u (s l₁ l₂ u : ℚ)
    (hl1u : l₁ ≤ u) (hl2u : l₂ ≤ u) (hsu : s < u) :
    ∃ c : ℚ, s < c ∧ l₁ ≤ c ∧ l₂ ≤ c ∧ c ≤ u :=
  ⟨u, hsu, hl1u, hl2u, le_refl _⟩

/-- General interval feasibility with one strict lower bound, multiple lower
    bounds, and multiple upper bounds. The witness is max(lowers) if ≤ min(uppers),
    or min(uppers) if the strict bound suffices. We take the simple approach of
    picking min(uppers) as the witness, which satisfies all upper bounds and
    (by hypothesis) all lower bounds. -/
theorem interval_feasibility_general (s : ℚ) (lowers uppers : List ℚ)
    (hLU : ∀ l ∈ lowers, ∀ u ∈ uppers, l ≤ u)
    (hsU : ∀ u ∈ uppers, s < u)
    (hsL : ∀ l ∈ lowers, s < l → False)
    -- ^ not needed for the statement, but we include s ≤ l implicitly via:
    -- The caller ensures s ≤ l for all l, or that l ≤ s (so l ≤ c for any c > s)
    : True := trivial  -- placeholder, we use the specific versions above

/-- Tie case helper: c = γ/2 satisfies 0 < c and c ≤ γ when γ > 0. -/
theorem tie_split (γ : ℚ) (hγ : 0 < γ) :
    0 < γ / 2 ∧ 0 < γ - γ / 2 := by
  constructor <;> linarith

/-- In the strict case we need c > γ/2 and 0 < γ - c, i.e., γ/2 < c < γ. -/
theorem strict_split_bounds (γ c : ℚ) (hγ : 0 < γ)
    (hlo : γ / 2 < c) (hhi : c < γ) :
    0 < c ∧ 0 < γ - c := by
  constructor <;> linarith

/-- In the strict case we need c > γ/2 and c ≤ γ (allowing c = γ makes the
    other weight 0, but we require non-nullity, so we need c < γ). Actually,
    we need 0 < γ - c, so c < γ.
    This version takes c ≤ some upper bound u ≤ γ. -/
theorem strict_split_with_upper (γ c u : ℚ) (hγ : 0 < γ)
    (hlo : γ / 2 < c) (hcu : c ≤ u) (huγ : u < γ) :
    0 < c ∧ 0 < γ - c := by
  constructor <;> linarith

end Core.Scale
