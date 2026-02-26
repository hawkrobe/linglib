import Linglib.Core.Scales.EpistemicScale.Defs

/-!
# Epistemic Entailment Patterns (Holliday & Icard 2013, Figure 1)

@cite{holliday-icard-2013}

Holliday & Icard (2013) Figure 1 lists 13 validity patterns (V1–V13) and
3 invalidity patterns (I1–I3) for epistemic comparatives. This file defines
each pattern as a `Prop`-valued predicate on a comparison relation `ge`, then
proves which patterns hold (or fail) in each of three semantic classes:

| Pattern | Measure (FP∞) | Qualitative (FA) | World-ordering (W) |
|---------|:-------------:|:----------------:|:-------------------:|
| V1      | ✓             | ✓                | ✓                   |
| V2      | ✓             | ✓                | ✓                   |
| V3      | ✓             | ✓                | ✓                   |
| V4      | ✓             | ✓                | ✓                   |
| V5      | ✓             | ✓                | ✓                   |
| V6      | ✓             | ✓                | ✓                   |
| V7      | ✓             | ✓                | ✓                   |
| V11     | ✓             | ✓                | ✓                   |
| V12     | ✓             | ✓                | ✓                   |
| V13     | ✓             | ✓                | ✗                   |
| I1      | ✗             | ✗                | ✓ (disjunction bug) |
| I2      | ✗             | ✗                | ✓ (disjunction bug) |
| I3      | ✗             | ✗                | ✓ (disjunction bug) |

The world-ordering column illustrates the "disjunction problem": Halpern's
l-lifting validates patterns (I1–I3) that are invalid under measure semantics,
showing that world-ordering semantics is strictly stronger than intended.
-/

namespace Core.Scale

-- ══════════════════════════════════════════════════════════════════
-- § 1. Derived operators
-- ══════════════════════════════════════════════════════════════════

variable {W : Type*}

/-- Strict comparative: A ≻ B iff A ≿ B but not B ≿ A. -/
def strict (ge : Set W → Set W → Prop) (A B : Set W) : Prop :=
  ge A B ∧ ¬ge B A

/-- "Probably A" — A is strictly more likely than its complement. -/
def probably (ge : Set W → Set W → Prop) (A : Set W) : Prop :=
  strict ge A Aᶜ

/-- "Possibly A" — A is not certainly impossible (¬(∅ ≿ A)). -/
def possibly (ge : Set W → Set W → Prop) (A : Set W) : Prop :=
  ¬ge ∅ A

-- ══════════════════════════════════════════════════════════════════
-- § 2. Pattern definitions (V1–V13, I1–I3)
-- ══════════════════════════════════════════════════════════════════

section PatternDefs

variable (ge : Set W → Set W → Prop)

/-- V1: △A → ¬△Aᶜ (probably A implies not probably not-A). -/
def patternV1 : Prop :=
  ∀ A : Set W, probably ge A → ¬probably ge Aᶜ

/-- V2: △(A ∩ B) → △A ∧ △B (probably conjunction implies probably each conjunct). -/
def patternV2 : Prop :=
  ∀ A B : Set W, probably ge (A ∩ B) → probably ge A ∧ probably ge B

/-- V3: △A → △(A ∪ B) (probably A implies probably any disjunction containing A). -/
def patternV3 : Prop :=
  ∀ A B : Set W, probably ge A → probably ge (A ∪ B)

/-- V4: A ≿ ∅ (every proposition is at least as likely as absurdity). -/
def patternV4 : Prop :=
  ∀ A : Set W, ge A ∅

/-- V5: ⊤ ≿ A (tautology is at least as likely as anything). -/
def patternV5 : Prop :=
  ∀ A : Set W, ge Set.univ A

/-- V6: △⊤ (tautology is probably true). -/
def patternV6 : Prop :=
  probably ge Set.univ

/-- V7: △A → ◇A (probably implies possibly). -/
def patternV7 : Prop :=
  ∀ A : Set W, probably ge A → possibly ge A

/-- V11: B ⊇ A → △A → △B (superset of a probable set is probable). -/
def patternV11 : Prop :=
  ∀ A B : Set W, A ⊆ B → probably ge A → probably ge B

/-- V12: B ⊇ A → A ≿ Aᶜ → B ≿ Bᶜ (superset of a "more likely than not"
    set is also "more likely than not"). -/
def patternV12 : Prop :=
  ∀ A B : Set W, A ⊆ B → ge A Aᶜ → ge B Bᶜ

/-- V13: (A \ B) ≻ ∅ → (A ∪ B) ≻ B (positive excess implies strict increase). -/
def patternV13 : Prop :=
  ∀ A B : Set W, strict ge (A \ B) ∅ → strict ge (A ∪ B) B

/-- I1: A ≿ B → A ≿ C → A ≿ (B ∪ C) (additivity of upper bound — INVALID
    for measures). -/
def patternI1 : Prop :=
  ∀ A B C : Set W, ge A B → ge A C → ge A (B ∪ C)

/-- I2: A ≿ Aᶜ → A ≿ B (more-likely-than-not implies universally maximal —
    INVALID for measures). -/
def patternI2 : Prop :=
  ∀ A B : Set W, ge A Aᶜ → ge A B

/-- I3: △A → A ≿ B (probably implies universally maximal — INVALID for measures). -/
def patternI3 : Prop :=
  ∀ A B : Set W, probably ge A → ge A B

end PatternDefs

-- ══════════════════════════════════════════════════════════════════
-- § 3. Measure Semantics (FP∞)
-- ══════════════════════════════════════════════════════════════════

section MeasureSemantics

private theorem mu_empty' (m : FinAddMeasure W) : m.mu ∅ = 0 := by
  have h : m.mu (∅ ∪ ∅) = m.mu ∅ + m.mu ∅ :=
    m.additive ∅ ∅ (fun x hx => hx.elim)
  simp only [Set.empty_union] at h; linarith

private theorem mu_compl (m : FinAddMeasure W) (A : Set W) :
    m.mu Aᶜ = 1 - m.mu A := by
  have hd : ∀ x, x ∈ A → x ∉ Aᶜ := fun x hx hxc => hxc hx
  have := m.additive A Aᶜ hd
  rw [Set.union_compl_self, m.total] at this; linarith

private theorem mu_mono (m : FinAddMeasure W) {A B : Set W} (h : A ⊆ B) :
    m.mu A ≤ m.mu B := by
  have hd : ∀ x, x ∈ A → x ∉ B \ A := fun x hx ⟨_, hna⟩ => hna hx
  rw [show B = A ∪ (B \ A) from (Set.union_diff_cancel h).symm, m.additive A (B \ A) hd]
  linarith [m.nonneg (B \ A)]

-- For measure semantics, "probably" reduces to μ(A) > 1/2 and "ge" to μ(A) ≥ μ(B).
-- All proofs are μ-arithmetic via linarith.

theorem measure_V1 (m : FinAddMeasure W) : patternV1 m.inducedGe := by
  intro A ⟨_, hAnot⟩ ⟨hAc, _⟩
  rw [compl_compl] at hAc; exact hAnot hAc

theorem measure_V2 (m : FinAddMeasure W) : patternV2 m.inducedGe := by
  intro A B ⟨hAB, hABnot⟩
  unfold FinAddMeasure.inducedGe at hAB hABnot
  rw [mu_compl] at hAB
  -- hAB : μ(A ∩ B) ≥ 1 - μ(A ∩ B), i.e. μ(A ∩ B) ≥ 1/2
  -- Since A ∩ B ⊆ A, μ(A) ≥ μ(A ∩ B) ≥ 1/2, so μ(A) ≥ 1 - μ(A).
  have hmuA : m.mu (A ∩ B) ≤ m.mu A := mu_mono m Set.inter_subset_left
  have hmuB : m.mu (A ∩ B) ≤ m.mu B := mu_mono m Set.inter_subset_right
  constructor
  · constructor
    · show m.mu A ≥ m.mu Aᶜ; rw [mu_compl]; linarith
    · intro hc; apply hABnot; show m.mu (A ∩ B)ᶜ ≥ m.mu (A ∩ B); rw [mu_compl]
      unfold FinAddMeasure.inducedGe at hc; rw [mu_compl] at hc; linarith
  · constructor
    · show m.mu B ≥ m.mu Bᶜ; rw [mu_compl]; linarith
    · intro hc; apply hABnot; show m.mu (A ∩ B)ᶜ ≥ m.mu (A ∩ B); rw [mu_compl]
      unfold FinAddMeasure.inducedGe at hc; rw [mu_compl] at hc; linarith

theorem measure_V3 (m : FinAddMeasure W) : patternV3 m.inducedGe := by
  intro A B ⟨hA, hAnot⟩
  unfold FinAddMeasure.inducedGe at *
  rw [mu_compl] at hA
  have hmuAU := mu_mono m (A := A) (B := A ∪ B) Set.subset_union_left
  constructor
  · show m.mu (A ∪ B) ≥ m.mu (A ∪ B)ᶜ; rw [mu_compl]; linarith
  · intro hc; apply hAnot; rw [mu_compl]; rw [mu_compl] at hc; linarith

theorem measure_V4 (m : FinAddMeasure W) : patternV4 m.inducedGe := by
  intro A; show m.mu A ≥ m.mu ∅; rw [mu_empty']; exact m.nonneg A

theorem measure_V5 (m : FinAddMeasure W) : patternV5 m.inducedGe := by
  intro A; exact mu_mono m (Set.subset_univ A)

theorem measure_V6 (m : FinAddMeasure W) : patternV6 m.inducedGe := by
  constructor
  · show m.mu Set.univ ≥ m.mu Set.univᶜ
    rw [Set.compl_univ, mu_empty', m.total]; linarith
  · intro h; unfold FinAddMeasure.inducedGe at h
    rw [Set.compl_univ, mu_empty', m.total] at h; linarith

theorem measure_V7 (m : FinAddMeasure W) : patternV7 m.inducedGe := by
  intro A ⟨hA, _⟩ hposs
  unfold FinAddMeasure.inducedGe at *
  rw [mu_empty'] at hposs; rw [mu_compl] at hA
  linarith [m.nonneg A]

theorem measure_V11 (m : FinAddMeasure W) : patternV11 m.inducedGe := by
  intro A B hAB ⟨hA, hAnot⟩
  unfold FinAddMeasure.inducedGe at *
  rw [mu_compl] at hA
  have hmuAB := mu_mono m hAB
  constructor
  · show m.mu B ≥ m.mu Bᶜ; rw [mu_compl]; linarith
  · intro hBc; apply hAnot; rw [mu_compl]
    change m.mu Bᶜ ≥ m.mu B at hBc; rw [mu_compl] at hBc; linarith

theorem measure_V12 (m : FinAddMeasure W) : patternV12 m.inducedGe := by
  intro A B hAB hA
  unfold FinAddMeasure.inducedGe at *
  rw [mu_compl] at *; linarith [mu_mono m hAB]

theorem measure_V13 (m : FinAddMeasure W) : patternV13 m.inducedGe := by
  intro A B ⟨hAB, hABnot⟩
  unfold FinAddMeasure.inducedGe at *
  rw [mu_empty'] at *
  have hd : ∀ x, x ∈ A \ B → x ∉ B := fun x ⟨_, hna⟩ hxB => hna hxB
  have hdecomp : A ∪ B = (A \ B) ∪ B := by rw [Set.diff_union_self]
  constructor
  · show m.mu (A ∪ B) ≥ m.mu B
    rw [hdecomp, m.additive (A \ B) B hd]; linarith [m.nonneg (A \ B)]
  · intro hc; apply hABnot
    change m.mu B ≥ m.mu (A ∪ B) at hc
    rw [hdecomp, m.additive (A \ B) B hd] at hc; linarith [m.nonneg (A \ B)]

/-- I1 is invalid for measure semantics: with uniform measure on Fin 3,
    {0} ≿ {1} and {0} ≿ {2} but ¬({0} ≿ {1,2}). -/
theorem measure_not_I1 :
    ¬∀ (m : FinAddMeasure (Fin 3)), patternI1 m.inducedGe := by
  sorry -- TODO: construct explicit uniform Fin 3 measure

/-- I2 is invalid for measure semantics. -/
theorem measure_not_I2 :
    ¬∀ (m : FinAddMeasure (Fin 3)), patternI2 m.inducedGe := by
  sorry -- TODO: construct explicit measure counterexample

/-- I3 is invalid for measure semantics. -/
theorem measure_not_I3 :
    ¬∀ (m : FinAddMeasure (Fin 3)), patternI3 m.inducedGe := by
  sorry -- TODO: construct explicit measure counterexample

end MeasureSemantics

-- ══════════════════════════════════════════════════════════════════
-- § 4. Qualitative Additivity (FA)
-- ══════════════════════════════════════════════════════════════════

section QualitativeAdditivity

-- All FA proofs use only monotonicity (T), transitivity, totality, and
-- complementation. The key technique: A ⊆ B gives ge B A (mono) and
-- ge Aᶜ Bᶜ (mono on complements), enabling transitivity chains.

theorem fa_V1 (sys : EpistemicSystemFA W) : patternV1 sys.ge := by
  intro A ⟨_, hAnot⟩ ⟨hAc, _⟩
  rw [compl_compl] at hAc; exact hAnot hAc

theorem fa_V2 (sys : EpistemicSystemFA W) : patternV2 sys.ge := by
  intro A B ⟨hAB, hABnot⟩
  have hsubA : sys.ge A (A ∩ B) := sys.mono (A ∩ B) A Set.inter_subset_left
  have hsubB : sys.ge B (A ∩ B) := sys.mono (A ∩ B) B Set.inter_subset_right
  have hcompA : sys.ge (A ∩ B)ᶜ Aᶜ :=
    sys.mono Aᶜ (A ∩ B)ᶜ (Set.compl_subset_compl.mpr Set.inter_subset_left)
  have hcompB : sys.ge (A ∩ B)ᶜ Bᶜ :=
    sys.mono Bᶜ (A ∩ B)ᶜ (Set.compl_subset_compl.mpr Set.inter_subset_right)
  constructor
  · constructor
    · -- ge A Aᶜ: chain A ≿ A∩B ≿ (A∩B)ᶜ ≿ Aᶜ
      exact sys.trans A (A ∩ B)ᶜ Aᶜ (sys.trans A (A ∩ B) (A ∩ B)ᶜ hsubA hAB) hcompA
    · -- ¬ge Aᶜ A: if ge Aᶜ A, chain Aᶜ ≿ A ≿ A∩B, and (A∩B)ᶜ ≿ Aᶜ ≿ A ≿ A∩B
      intro hc; apply hABnot
      exact sys.trans (A ∩ B)ᶜ A (A ∩ B) (sys.trans (A ∩ B)ᶜ Aᶜ A hcompA hc) hsubA
  · constructor
    · exact sys.trans B (A ∩ B)ᶜ Bᶜ (sys.trans B (A ∩ B) (A ∩ B)ᶜ hsubB hAB) hcompB
    · intro hc; apply hABnot
      exact sys.trans (A ∩ B)ᶜ B (A ∩ B) (sys.trans (A ∩ B)ᶜ Bᶜ B hcompB hc) hsubB

theorem fa_V3 (sys : EpistemicSystemFA W) : patternV3 sys.ge := by
  intro A B ⟨hA, hAnot⟩
  have h1 : sys.ge (A ∪ B) A := sys.mono A (A ∪ B) Set.subset_union_left
  have h2 : sys.ge Aᶜ (Aᶜ ∩ Bᶜ) := sys.mono (Aᶜ ∩ Bᶜ) Aᶜ Set.inter_subset_left
  constructor
  · rw [Set.compl_union]
    exact sys.trans (A ∪ B) Aᶜ (Aᶜ ∩ Bᶜ) (sys.trans (A ∪ B) A Aᶜ h1 hA) h2
  · intro hc; rw [Set.compl_union] at hc; apply hAnot
    exact sys.trans Aᶜ (A ∪ B) A
      (sys.trans Aᶜ (Aᶜ ∩ Bᶜ) (A ∪ B) h2 hc) h1

theorem fa_V4 (sys : EpistemicSystemFA W) : patternV4 sys.ge := by
  intro A; exact sys.mono ∅ A (Set.empty_subset A)

theorem fa_V5 (sys : EpistemicSystemFA W) : patternV5 sys.ge := by
  intro A; exact sys.mono A Set.univ (Set.subset_univ A)

theorem fa_V6 (sys : EpistemicSystemFA W) : patternV6 sys.ge := by
  constructor
  · rw [Set.compl_univ]; exact sys.bottom
  · intro h; rw [Set.compl_univ] at h; exact sys.nonTrivial h

theorem fa_V7 (sys : EpistemicSystemFA W) : patternV7 sys.ge := by
  intro A ⟨_, hAnot⟩ hempty
  exact hAnot (sys.trans Aᶜ ∅ A (sys.mono ∅ Aᶜ (Set.empty_subset Aᶜ)) hempty)

theorem fa_V11 (sys : EpistemicSystemFA W) : patternV11 sys.ge := by
  intro A B hAB ⟨hA, hAnot⟩
  have h1 : sys.ge B A := sys.mono A B hAB
  have h2 : sys.ge Aᶜ Bᶜ := sys.mono Bᶜ Aᶜ (Set.compl_subset_compl.mpr hAB)
  constructor
  · exact sys.trans B Aᶜ Bᶜ (sys.trans B A Aᶜ h1 hA) h2
  · intro hc; exact hAnot (sys.trans Aᶜ B A (sys.trans Aᶜ Bᶜ B h2 hc) h1)

theorem fa_V12 (sys : EpistemicSystemFA W) : patternV12 sys.ge := by
  intro A B hAB hA
  exact sys.trans B Aᶜ Bᶜ
    (sys.trans B A Aᶜ (sys.mono A B hAB) hA)
    (sys.mono Bᶜ Aᶜ (Set.compl_subset_compl.mpr hAB))

theorem fa_V13 (sys : EpistemicSystemFA W) : patternV13 sys.ge := by
  intro A B ⟨_, hABnot⟩
  constructor
  · exact sys.mono B (A ∪ B) Set.subset_union_right
  · intro hc; apply hABnot
    have hax := sys.additive B (A ∪ B)
    have h1 : B \ (A ∪ B) = ∅ := by
      ext x; simp only [Set.mem_diff, Set.mem_union, Set.mem_empty_iff_false,
        iff_false, not_and, not_not]
      exact fun hxB => Or.inr hxB
    have h2 : (A ∪ B) \ B = A \ B := by
      ext x; constructor
      · rintro ⟨hx | hx, hn⟩
        · exact ⟨hx, hn⟩
        · exact absurd hx hn
      · rintro ⟨hx, hn⟩
        exact ⟨Or.inl hx, hn⟩
    rw [h1, h2] at hax
    exact hax.mp hc

/-- I1 is invalid for FA. -/
theorem fa_not_I1 : ¬∀ (W : Type*) (sys : EpistemicSystemFA W),
    patternI1 sys.ge := by
  sorry -- TODO: construct explicit FA counterexample on Fin 3

/-- I2 is invalid for FA. -/
theorem fa_not_I2 : ¬∀ (W : Type*) (sys : EpistemicSystemFA W),
    patternI2 sys.ge := by
  sorry -- TODO: construct explicit FA counterexample

/-- I3 is invalid for FA. -/
theorem fa_not_I3 : ¬∀ (W : Type*) (sys : EpistemicSystemFA W),
    patternI3 sys.ge := by
  sorry -- TODO: construct explicit FA counterexample

end QualitativeAdditivity

-- ══════════════════════════════════════════════════════════════════
-- § 5. World Ordering (System W / Halpern Lift)
-- ══════════════════════════════════════════════════════════════════

/-! Recall: `halpernLift ge_w A B := ∀ b, b ∈ B → ∃ a, a ∈ A ∧ ge_w a b`.
    So `halpernLift ge_w A B` means every element of B is dominated by some
    element of A. -/

section WorldOrdering

theorem halpern_V1 {W : Type*} (ge_w : W → W → Prop) :
    patternV1 (halpernLift ge_w) := by
  intro A ⟨_, hAnot⟩ ⟨hAc, _⟩
  rw [compl_compl] at hAc; exact hAnot hAc

theorem halpern_V2 {W : Type*} (ge_w : W → W → Prop) :
    patternV2 (halpernLift ge_w) := by
  intro A B ⟨hAB, hABnot⟩
  constructor
  · constructor
    · -- ge A Aᶜ: ∀ b ∈ Aᶜ, ∃ a ∈ A, ge_w a b.
      -- b ∈ Aᶜ → b ∉ A → b ∉ A ∩ B. Since Aᶜ ⊆ (A ∩ B)ᶜ, use hAB.
      intro b hb
      have hb' : b ∈ (A ∩ B)ᶜ := fun ⟨ha, _⟩ => hb ha
      obtain ⟨a, ⟨ha, _⟩, hge⟩ := hAB b hb'
      exact ⟨a, ha, hge⟩
    · -- ¬ge Aᶜ A: if so, every b ∈ A has dominator in Aᶜ ⊆ (A ∩ B)ᶜ.
      -- Then every b ∈ A ∩ B (⊆ A) has dominator in (A ∩ B)ᶜ, so ge (A∩B)ᶜ (A∩B).
      intro hc; apply hABnot; intro b ⟨hbA, _⟩
      obtain ⟨a, ha, hge⟩ := hc b hbA
      exact ⟨a, fun ⟨haA, _⟩ => ha haA, hge⟩
  · constructor
    · intro b hb
      have hb' : b ∈ (A ∩ B)ᶜ := fun ⟨_, hbB⟩ => hb hbB
      obtain ⟨a, ⟨_, ha⟩, hge⟩ := hAB b hb'
      exact ⟨a, ha, hge⟩
    · intro hc; apply hABnot; intro b ⟨_, hbB⟩
      obtain ⟨a, ha, hge⟩ := hc b hbB
      exact ⟨a, fun ⟨_, haB⟩ => ha haB, hge⟩

theorem halpern_V3 {W : Type*} (ge_w : W → W → Prop) :
    patternV3 (halpernLift ge_w) := by
  intro A B ⟨hA, hAnot⟩
  constructor
  · -- ge (A ∪ B) (A ∪ B)ᶜ: b ∈ (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ → b ∈ Aᶜ → use hA.
    rw [Set.compl_union]; intro b ⟨hbAc, _⟩
    obtain ⟨a, ha, hge⟩ := hA b hbAc
    exact ⟨a, Set.mem_union_left B ha, hge⟩
  · -- ¬ge (A ∪ B)ᶜ (A ∪ B): if so, restricting to A ⊆ A ∪ B gives ge Aᶜ A.
    rw [Set.compl_union]; intro hc; apply hAnot; intro b hbA
    obtain ⟨a, ⟨haAc, _⟩, hge⟩ := hc b (Set.mem_union_left B hbA)
    exact ⟨a, haAc, hge⟩

theorem halpern_V4 {W : Type*} (ge_w : W → W → Prop) :
    patternV4 (halpernLift ge_w) := by
  intro _ b hb; exact hb.elim

theorem halpern_V5 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternV5 (halpernLift ge_w) := by
  intro _ b hb; exact ⟨b, Set.mem_univ b, hRefl b⟩

theorem halpern_V6 {W : Type*} [Nonempty W] (ge_w : W → W → Prop) :
    patternV6 (halpernLift ge_w) := by
  show strict (halpernLift ge_w) Set.univ Set.univᶜ
  rw [Set.compl_univ]
  exact ⟨fun b hb => hb.elim,
    fun h => by obtain ⟨w⟩ := ‹Nonempty W›; obtain ⟨a, ha, _⟩ := h w (Set.mem_univ w); exact ha.elim⟩

theorem halpern_V7 {W : Type*} (ge_w : W → W → Prop) :
    patternV7 (halpernLift ge_w) := by
  intro A ⟨_, hAnot⟩ hempty
  by_cases hne : (A : Set W).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨a, ha, _⟩ := hempty x hx; exact ha.elim
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.compl_empty] at hAnot
    exact hAnot (fun b hb => hb.elim)

theorem halpern_V11 {W : Type*} (ge_w : W → W → Prop) :
    patternV11 (halpernLift ge_w) := by
  intro A B hAB ⟨hA, hAnot⟩
  constructor
  · -- ge B Bᶜ: b ∈ Bᶜ → b ∈ Aᶜ (since A ⊆ B) → use hA to get a ∈ A ⊆ B.
    intro b hbBc
    obtain ⟨a, haA, hge⟩ := hA b (fun hbA => hbBc (hAB hbA))
    exact ⟨a, hAB haA, hge⟩
  · -- ¬ge Bᶜ B: if so, restricting to A ⊆ B gives dominators in Bᶜ ⊆ Aᶜ.
    intro hc; apply hAnot; intro b hbA
    obtain ⟨a, haBc, hge⟩ := hc b (hAB hbA)
    exact ⟨a, fun haA => haBc (hAB haA), hge⟩

theorem halpern_V12 {W : Type*} (ge_w : W → W → Prop) :
    patternV12 (halpernLift ge_w) := by
  intro A B hAB hA b hbBc
  obtain ⟨a, haA, hge⟩ := hA b (fun hbA => hbBc (hAB hbA))
  exact ⟨a, hAB haA, hge⟩

/-- V13 is invalid for world-ordering semantics. Counterexample:
    W = Fin 2, ge_w = total (everything related). A = {0}, B = {1}.
    Then (A \ B) ≻ ∅ holds but (A ∪ B) ≻ B fails because ge B (A ∪ B). -/
theorem halpern_not_V13 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV13 (halpernLift ge_w) := by
  refine ⟨Fin 2, fun _ _ => True, fun _ => trivial, ?_⟩
  intro h
  have hA : ({0} : Set (Fin 2)) \ {1} = {0} := by
    ext x; simp only [Set.mem_diff, Set.mem_singleton_iff]; omega
  have hstrict : strict (halpernLift (fun (_ _ : Fin 2) => True)) ({0} \ {1}) ∅ :=
    ⟨fun b hb => hb.elim, fun hge => by
      obtain ⟨a, ha, _⟩ := hge (0 : Fin 2) (by rw [hA]; rfl); exact ha.elim⟩
  have hresult := h {0} {1} hstrict
  have huniv : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]; omega
  rw [huniv] at hresult
  exact hresult.2 (fun b _ => ⟨1, rfl, trivial⟩)

/-- I1 is valid for world-ordering semantics: the "disjunction problem". -/
theorem halpern_I1 {W : Type*} (ge_w : W → W → Prop) :
    patternI1 (halpernLift ge_w) := by
  intro A B C hAB hAC b hb
  exact hb.elim (hAB b) (hAC b)

/-- I2 is valid for world-ordering semantics. -/
theorem halpern_I2 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternI2 (halpernLift ge_w) := by
  intro A B hA b hbB
  by_cases hbA : b ∈ A
  · exact ⟨b, hbA, hRefl b⟩
  · exact hA b hbA

/-- I3 is valid for world-ordering semantics. -/
theorem halpern_I3 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternI3 (halpernLift ge_w) := by
  intro A B ⟨hA, _⟩; exact halpern_I2 ge_w hRefl A B hA

end WorldOrdering

end Core.Scale
