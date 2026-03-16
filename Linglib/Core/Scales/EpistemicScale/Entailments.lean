import Linglib.Core.Scales.EpistemicScale.Defs
import Mathlib.Data.Set.Card

/-!
# Epistemic Entailment Patterns (@cite{holliday-icard-2013}, Figure 1)

@cite{holliday-icard-2013} @cite{harrison-trainor-holliday-icard-2018} @cite{yalcin-2010}

@cite{holliday-icard-2013} Figure 1 lists 10 validity patterns (V1–V7, V11–V13)
and 3 invalidity patterns (I1–I3) for epistemic comparatives. (V8–V10 are from
@cite{yalcin-2010} and omitted from H&I's condensed figure.) This file defines
each pattern as a `Prop`-valued predicate on a comparison relation `ge`, then
proves which patterns hold (or fail) in each of three semantic classes:

| Pattern | Measure (FP∞) | Qualitative (FA) | l-lifting (W) | m-lifting     |
|---------|:-------------:|:----------------:|:-------------:|:-------------:|
| V1      | ✓             | ✓                | ✓             | ✓             |
| V2      | ✓             | ✓                | ✓             | ✓             |
| V3      | ✓             | ✓                | ✓             | ✓             |
| V4      | ✓             | ✓                | ✓             | ✓             |
| V5      | ✓             | ✓                | ✓             | ✓             |
| V6      | ✓             | ✓                | ✓             | ✓             |
| V7      | ✓             | ✓                | ✓             | ✓             |
| V11     | ✓             | ✓                | ✗             | ✓             |
| V12     | ✓             | ✓                | ✓ (preorder)  | ✓             |
| V13     | ✓             | ✓                | ✗             | ✓             |
| I1      | ✗             | ✗                | ✓ (disj. bug) | ✗             |
| I2      | ✗             | ✗                | ✓ (disj. bug) | ✗             |
| I3      | ✗             | ✗                | ✓ (disj. bug) | ✗             |

The world-ordering column illustrates the "disjunction problem": Halpern's
l-lifting validates patterns (I1–I3) that are invalid under measure semantics,
showing that world-ordering semantics is strictly stronger than intended.
V11 and V13 are invalid for l-lifting (Fact 1 in the paper).
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

/-- V6: □A → △A (necessarily A implies probably A).
    □A is ¬◇¬A = ge ∅ Aᶜ in the set-theoretic framework
    (@cite{holliday-icard-2013}, Figure 1). -/
def patternV6 : Prop :=
  ∀ A : Set W, ge ∅ Aᶜ → probably ge A

/-- V7: △A → ◇A (probably implies possibly). -/
def patternV7 : Prop :=
  ∀ A : Set W, probably ge A → possibly ge A

/-- V11: B ≿ A → △A → △B (if B is at least as likely as a probable set,
    then B is probable). Uses the comparative ≿, not set inclusion ⊆.
    Invalid for l-lifting (Fact 1 in @cite{holliday-icard-2013}). -/
def patternV11 : Prop :=
  ∀ A B : Set W, ge B A → probably ge A → probably ge B

/-- V12: B ≿ A → A ≿ Aᶜ → B ≿ Bᶜ (if B is at least as likely as a set
    that is more likely than not, then B is more likely than not).
    Uses the comparative ≿, not set inclusion ⊆. -/
def patternV12 : Prop :=
  ∀ A B : Set W, ge B A → ge A Aᶜ → ge B Bᶜ

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
  intro A; show m.mu A ≥ m.mu ∅; rw [m.mu_empty]; exact m.nonneg A

theorem measure_V5 (m : FinAddMeasure W) : patternV5 m.inducedGe := by
  intro A; exact mu_mono m (Set.subset_univ A)

theorem measure_V6 (m : FinAddMeasure W) : patternV6 m.inducedGe := by
  intro A h
  unfold FinAddMeasure.inducedGe at h
  rw [m.mu_empty] at h
  have hAc0 : m.mu Aᶜ = 0 := le_antisymm h (m.nonneg Aᶜ)
  constructor
  · show m.mu A ≥ m.mu Aᶜ; rw [hAc0]; exact m.nonneg A
  · intro hc; unfold FinAddMeasure.inducedGe at hc
    linarith [mu_compl m A]

theorem measure_V7 (m : FinAddMeasure W) : patternV7 m.inducedGe := by
  intro A ⟨hA, _⟩ hposs
  unfold FinAddMeasure.inducedGe at *
  rw [m.mu_empty] at hposs; rw [mu_compl] at hA
  linarith [m.nonneg A]

theorem measure_V11 (m : FinAddMeasure W) : patternV11 m.inducedGe := by
  intro A B hAB ⟨hA, hAnot⟩
  unfold FinAddMeasure.inducedGe at *
  rw [mu_compl] at hA
  -- hAB : m.mu B ≥ m.mu A (from ge B A after unfolding)
  constructor
  · show m.mu B ≥ m.mu Bᶜ; rw [mu_compl]; linarith
  · intro hBc; apply hAnot; rw [mu_compl]
    change m.mu Bᶜ ≥ m.mu B at hBc; rw [mu_compl] at hBc; linarith

theorem measure_V12 (m : FinAddMeasure W) : patternV12 m.inducedGe := by
  intro A B hAB hA
  unfold FinAddMeasure.inducedGe at *
  -- hAB : m.mu B ≥ m.mu A; hA : m.mu A ≥ m.mu Aᶜ
  rw [mu_compl] at *; linarith

theorem measure_V13 (m : FinAddMeasure W) : patternV13 m.inducedGe := by
  intro A B ⟨hAB, hABnot⟩
  unfold FinAddMeasure.inducedGe at *
  rw [m.mu_empty] at *
  have hd : ∀ x, x ∈ A \ B → x ∉ B := fun x ⟨_, hna⟩ hxB => hna hxB
  have hdecomp : A ∪ B = (A \ B) ∪ B := by rw [Set.diff_union_self]
  constructor
  · show m.mu (A ∪ B) ≥ m.mu B
    rw [hdecomp, m.additive (A \ B) B hd]; linarith [m.nonneg (A \ B)]
  · intro hc; apply hABnot
    change m.mu B ≥ m.mu (A ∪ B) at hc
    rw [hdecomp, m.additive (A \ B) B hd] at hc; linarith [m.nonneg (A \ B)]

-- Counterexample infrastructure: uniform measure on Fin 3 (μ({i}) = 1/3).

attribute [local instance] Classical.propDecidable

private noncomputable def uf3 : FinAddMeasure (Fin 3) where
  mu := λ A =>
    (if (0 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (1 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (2 : Fin 3) ∈ A then (1:ℚ)/3 else 0)
  nonneg := λ A => add_nonneg (add_nonneg
    (by split <;> norm_num) (by split <;> norm_num)) (by split <;> norm_num)
  additive := λ A B hdisj => by
    simp only [Set.mem_union]
    by_cases h0A : (0 : Fin 3) ∈ A <;> by_cases h0B : (0 : Fin 3) ∈ B <;>
    by_cases h1A : (1 : Fin 3) ∈ A <;> by_cases h1B : (1 : Fin 3) ∈ B <;>
    by_cases h2A : (2 : Fin 3) ∈ A <;> by_cases h2B : (2 : Fin 3) ∈ B <;>
    simp_all <;> linarith
  total := by simp only [Set.mem_univ, ite_true]; norm_num

private theorem uf3_mu_eq (A : Set (Fin 3)) :
    uf3.mu A =
    (if (0 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (1 : Fin 3) ∈ A then (1:ℚ)/3 else 0) +
    (if (2 : Fin 3) ∈ A then (1:ℚ)/3 else 0) := rfl

private theorem uf3_mu_0 : uf3.mu {(0 : Fin 3)} = 1/3 := by
  rw [uf3_mu_eq]
  have h0 : (0 : Fin 3) ∈ ({(0 : Fin 3)} : Set _) := rfl
  have h1 : (1 : Fin 3) ∉ ({(0 : Fin 3)} : Set _) :=
    fun h => absurd (Set.mem_singleton_iff.mp h) (by omega)
  have h2 : (2 : Fin 3) ∉ ({(0 : Fin 3)} : Set _) :=
    fun h => absurd (Set.mem_singleton_iff.mp h) (by omega)
  rw [if_pos h0, if_neg h1, if_neg h2]; norm_num

private theorem uf3_mu_1 : uf3.mu {(1 : Fin 3)} = 1/3 := by
  rw [uf3_mu_eq]
  have h0 : (0 : Fin 3) ∉ ({(1 : Fin 3)} : Set _) :=
    fun h => absurd (Set.mem_singleton_iff.mp h) (by omega)
  have h1 : (1 : Fin 3) ∈ ({(1 : Fin 3)} : Set _) := rfl
  have h2 : (2 : Fin 3) ∉ ({(1 : Fin 3)} : Set _) :=
    fun h => absurd (Set.mem_singleton_iff.mp h) (by omega)
  rw [if_neg h0, if_pos h1, if_neg h2]; norm_num

private theorem uf3_mu_2 : uf3.mu {(2 : Fin 3)} = 1/3 := by
  rw [uf3_mu_eq]
  have h0 : (0 : Fin 3) ∉ ({(2 : Fin 3)} : Set _) :=
    fun h => absurd (Set.mem_singleton_iff.mp h) (by omega)
  have h1 : (1 : Fin 3) ∉ ({(2 : Fin 3)} : Set _) :=
    fun h => absurd (Set.mem_singleton_iff.mp h) (by omega)
  have h2 : (2 : Fin 3) ∈ ({(2 : Fin 3)} : Set _) := rfl
  rw [if_neg h0, if_neg h1, if_pos h2]; norm_num

private theorem uf3_mu_union_12 : uf3.mu ({(1 : Fin 3)} ∪ {2}) = 2/3 := by
  rw [uf3.additive _ _ (λ x hx hx2 => by
    rw [Set.mem_singleton_iff] at hx hx2; omega)]
  rw [uf3_mu_1, uf3_mu_2]; norm_num

private theorem uf3_mu_pair_01 : uf3.mu ({0, 1} : Set (Fin 3)) = 2/3 := by
  rw [show ({0, 1} : Set (Fin 3)) = {0} ∪ {1} from Set.insert_eq 0 {1}]
  rw [uf3.additive _ _ (λ x hx hx1 => by
    rw [Set.mem_singleton_iff] at hx hx1; omega)]
  rw [uf3_mu_0, uf3_mu_1]; norm_num

private theorem uf3_mu_compl' (A : Set (Fin 3)) :
    uf3.mu Aᶜ = 1 - uf3.mu A := by
  have hd : ∀ x, x ∈ A → x ∉ Aᶜ := fun x hx hxc => hxc hx
  have h := uf3.additive A Aᶜ hd
  rw [Set.union_compl_self, uf3.total] at h; linarith

/-- I1 is invalid for measure semantics: with uniform measure on Fin 3,
    {0} ≿ {1} and {0} ≿ {2} but ¬({0} ≿ {1,2}). -/
theorem measure_not_I1 :
    ¬∀ (m : FinAddMeasure (Fin 3)), patternI1 m.inducedGe := by
  intro hall
  have hI1 := hall uf3 {(0 : Fin 3)} {1} {2}
  have h01 : uf3.inducedGe {(0 : Fin 3)} {1} := by
    unfold FinAddMeasure.inducedGe; rw [uf3_mu_0, uf3_mu_1]
  have h02 : uf3.inducedGe {(0 : Fin 3)} {2} := by
    unfold FinAddMeasure.inducedGe; rw [uf3_mu_0, uf3_mu_2]
  have hconc := hI1 h01 h02
  unfold FinAddMeasure.inducedGe at hconc
  rw [uf3_mu_0, uf3_mu_union_12] at hconc; linarith

/-- I2 is invalid for measure semantics: with uniform measure on Fin 3,
    {0,1} ≿ {0,1}ᶜ but ¬({0,1} ≿ univ). -/
theorem measure_not_I2 :
    ¬∀ (m : FinAddMeasure (Fin 3)), patternI2 m.inducedGe := by
  intro hall
  have hI2 := hall uf3 ({0, 1} : Set (Fin 3)) Set.univ
  have hge : uf3.inducedGe ({0, 1} : Set (Fin 3)) ({0, 1} : Set (Fin 3))ᶜ := by
    unfold FinAddMeasure.inducedGe
    rw [uf3_mu_pair_01, uf3_mu_compl', uf3_mu_pair_01]; linarith
  have hconc := hI2 hge
  unfold FinAddMeasure.inducedGe at hconc
  rw [uf3_mu_pair_01, uf3.total] at hconc; linarith

/-- I3 is invalid for measure semantics: with uniform measure on Fin 3,
    probably({0,1}) but ¬({0,1} ≿ univ). -/
theorem measure_not_I3 :
    ¬∀ (m : FinAddMeasure (Fin 3)), patternI3 m.inducedGe := by
  intro hall
  have hI3 := hall uf3 ({0, 1} : Set (Fin 3)) Set.univ
  have hprob : probably uf3.inducedGe ({0, 1} : Set (Fin 3)) := by
    constructor
    · unfold FinAddMeasure.inducedGe
      rw [uf3_mu_pair_01, uf3_mu_compl', uf3_mu_pair_01]; linarith
    · intro h; unfold FinAddMeasure.inducedGe at h
      rw [uf3_mu_pair_01, uf3_mu_compl', uf3_mu_pair_01] at h; linarith
  have hconc := hI3 hprob
  unfold FinAddMeasure.inducedGe at hconc
  rw [uf3_mu_pair_01, uf3.total] at hconc; linarith

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
  intro A h0Ac
  have hA0 : sys.ge A ∅ := sys.mono ∅ A (Set.empty_subset A)
  constructor
  · exact sys.trans A ∅ Aᶜ hA0 h0Ac
  · intro hAcA
    -- ge ∅ A by transitivity, then ge A Set.univ by axiom A
    have h0A : sys.ge ∅ A := sys.trans ∅ Aᶜ A h0Ac hAcA
    have hAU : sys.ge A Set.univ := by
      rw [sys.additive A Set.univ]
      have h1 : A \ Set.univ = ∅ := Set.diff_eq_empty.mpr (Set.subset_univ A)
      have h2 : Set.univ \ A = Aᶜ := by ext x; simp [Set.mem_diff, Set.mem_compl_iff]
      rw [h1, h2]; exact h0Ac
    exact sys.nonTrivial (sys.trans ∅ A Set.univ h0A hAU)

theorem fa_V7 (sys : EpistemicSystemFA W) : patternV7 sys.ge := by
  intro A ⟨_, hAnot⟩ hempty
  exact hAnot (sys.trans Aᶜ ∅ A (sys.mono ∅ Aᶜ (Set.empty_subset Aᶜ)) hempty)

private theorem fa_compl_ge (sys : EpistemicSystemFA W) {A B : Set W}
    (h : sys.ge B A) : sys.ge Aᶜ Bᶜ := by
  -- From ge B A, by Axiom A: ge (B \ A) (A \ B).
  -- Since Aᶜ \ Bᶜ = B \ A and Bᶜ \ Aᶜ = A \ B, Axiom A gives ge Aᶜ Bᶜ.
  have hd1 : Aᶜ \ Bᶜ = B \ A := by
    ext x; simp only [Set.mem_diff, Set.mem_compl_iff, not_not]; exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  have hd2 : Bᶜ \ Aᶜ = A \ B := by
    ext x; simp only [Set.mem_diff, Set.mem_compl_iff, not_not]; exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  rw [sys.additive Aᶜ Bᶜ, hd1, hd2]
  exact (sys.additive B A).mp h

theorem fa_V11 (sys : EpistemicSystemFA W) : patternV11 sys.ge := by
  intro A B hAB ⟨hA, hAnot⟩
  -- hAB : sys.ge B A
  have h2 : sys.ge Aᶜ Bᶜ := fa_compl_ge sys hAB
  constructor
  · exact sys.trans B Aᶜ Bᶜ (sys.trans B A Aᶜ hAB hA) h2
  · intro hc; exact hAnot (sys.trans Aᶜ B A (sys.trans Aᶜ Bᶜ B h2 hc) hAB)

theorem fa_V12 (sys : EpistemicSystemFA W) : patternV12 sys.ge := by
  intro A B hAB hA
  -- hAB : sys.ge B A; hA : sys.ge A Aᶜ
  exact sys.trans B Aᶜ Bᶜ
    (sys.trans B A Aᶜ hAB hA)
    (fa_compl_ge sys hAB)

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

/-- I1 is invalid for FA: the measure-induced FA system on Fin 3 is a
    counterexample (every finitely additive measure induces an FA system
    via `toSystemFA`). -/
theorem fa_not_I1 : ¬∀ (W : Type) (sys : EpistemicSystemFA W),
    patternI1 sys.ge := by
  intro hall
  apply measure_not_I1
  intro m
  exact hall (Fin 3) m.toSystemFA

/-- I2 is invalid for FA. -/
theorem fa_not_I2 : ¬∀ (W : Type) (sys : EpistemicSystemFA W),
    patternI2 sys.ge := by
  intro hall
  apply measure_not_I2
  intro m
  exact hall (Fin 3) m.toSystemFA

/-- I3 is invalid for FA. -/
theorem fa_not_I3 : ¬∀ (W : Type) (sys : EpistemicSystemFA W),
    patternI3 sys.ge := by
  intro hall
  apply measure_not_I3
  intro m
  exact hall (Fin 3) m.toSystemFA

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
  intro A hAc
  -- halpernLift ge_w ∅ Aᶜ forces Aᶜ = ∅ (no function from Aᶜ to ∅)
  have hAuniv : A = Set.univ := by
    ext x; simp only [Set.mem_univ, iff_true]
    by_contra hx; obtain ⟨a, ha, _⟩ := hAc x hx; exact ha.elim
  subst hAuniv
  show halpernLift ge_w Set.univ Set.univᶜ ∧ ¬halpernLift ge_w Set.univᶜ Set.univ
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

/-- V11 is **invalid** for world-ordering semantics (Fact 1 in
    @cite{holliday-icard-2013}). Counterexample: W = Fin 2, ge_w total.
    A = W (probably, since W ≿ ∅ and ¬(∅ ≿ W)). B = {0} (B ≿ A since
    ge_w is total, but Bᶜ = {1} ≿ B since ge_w is total — not strictly). -/
theorem halpern_not_V11 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternV11 (halpernLift ge_w) := by
  refine ⟨Fin 2, fun _ _ => True, fun _ => trivial, ?_⟩
  intro h
  -- B = {0}, A = Set.univ
  have hBA : halpernLift (fun (_ _ : Fin 2) => True) {(0 : Fin 2)} Set.univ :=
    fun _ _ => ⟨0, rfl, trivial⟩
  have hprobA : probably (halpernLift (fun (_ _ : Fin 2) => True)) Set.univ := by
    refine ⟨fun b hb => absurd (Set.mem_univ b) hb, ?_⟩
    intro hge
    obtain ⟨a, ha, _⟩ := hge (0 : Fin 2) (Set.mem_univ _)
    exact absurd (Set.mem_univ a) ha
  have hresult := h Set.univ {(0 : Fin 2)} hBA hprobA
  -- hresult : probably {0}, i.e., {0} ≿ {1} and ¬({1} ≿ {0})
  -- But {1} ≿ {0} since ge_w is total: 1 ≥ 0.
  apply hresult.2
  intro b _
  exact ⟨1, fun h1 => absurd (Set.mem_singleton_iff.mp h1) (by omega), trivial⟩

/-- V12 is valid for world-ordering semantics with a preorder (Fact 1 in
    @cite{holliday-icard-2013}). Requires transitivity for the case where
    y ∈ Bᶜ ∩ Aᶜ: chain through A via ge A Aᶜ, then through B via ge B A. -/
theorem halpern_V12 {W : Type*} (ge_w : W → W → Prop)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV12 (halpernLift ge_w) := by
  intro A B hBA hA y hyBc
  by_cases hyA : y ∈ A
  · -- y ∈ A: from ge B A, get b ∈ B with b ≥ y.
    exact hBA y hyA
  · -- y ∈ Aᶜ: from ge A Aᶜ, get a ∈ A with a ≥ y.
    --          from ge B A, get b ∈ B with b ≥ a.
    --          transitivity: b ≥ a ≥ y → b ≥ y.
    obtain ⟨a, haA, hge_ay⟩ := hA y hyA
    obtain ⟨b, hbB, hge_ba⟩ := hBA a haA
    exact ⟨b, hbB, hTrans b a y hge_ba hge_ay⟩

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

-- ══════════════════════════════════════════════════════════════════
-- § 6. m-Lifting (@cite{holliday-icard-2013}, Fact 5)
-- ══════════════════════════════════════════════════════════════════

/-! The m-lifting validates all 13 validity patterns V1–V13 and invalidates
    I1–I3 (Fact 5 in @cite{holliday-icard-2013}). This avoids the
    "disjunction problem" that plagues the l-lifting.

    V1, V3–V7 follow from the l-lifting proofs (since m-lifting implies
    l-lifting). V2, V11–V13 use the injection structure directly;
    V11–V12 rely on complement reversal (`mLift_complement_reversal`). -/

section MLift

/-- Every m-lift entails an l-lift: if there is an injection from B to A
    with each image dominating its preimage, then in particular every
    element of B is dominated by some element of A. -/
theorem mLift_implies_halpernLift {W : Type*} {ge_w : W → W → Prop}
    {A B : Set W} (h : mLift ge_w A B) : halpernLift ge_w A B := by
  obtain ⟨f, hf, _⟩ := h
  intro b hbB
  obtain ⟨ha, hge⟩ := hf b hbB
  exact ⟨f b, ha, hge⟩

theorem mLift_V1 {W : Type*} (ge_w : W → W → Prop) :
    patternV1 (mLift ge_w) := by
  intro A ⟨_, hAnot⟩ ⟨hAc, _⟩
  rw [compl_compl] at hAc; exact hAnot hAc

/-- V2 is valid for the m-lifting: △(A ∩ B) → △A ∧ △B.

    Proof: restrict the injection f : (A∩B)ᶜ ↪ A∩B to Aᶜ ⊆ (A∩B)ᶜ to get
    the ge half. For the strict half, any reverse injection g : A ↪ Aᶜ
    restricts to A∩B ↪ (A∩B)ᶜ (since Aᶜ ⊆ (A∩B)ᶜ), contradicting the
    hypothesis ¬mLift (A∩B)ᶜ (A∩B). Symmetric for B. -/
theorem mLift_V2 {W : Type*} (ge_w : W → W → Prop)
    (_hRefl : ∀ w, ge_w w w) :
    patternV2 (mLift ge_w) := by
  intro A B ⟨⟨f, hf, hinj⟩, hABnot⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- mLift ge_w A Aᶜ: restrict f from (A∩B)ᶜ to Aᶜ
    exact ⟨f,
      fun b hb => ⟨(hf b (fun h => hb h.1)).1.1, (hf b (fun h => hb h.1)).2⟩,
      fun b₁ b₂ h1 h2 => hinj b₁ b₂ (fun h => h1 h.1) (fun h => h2 h.1)⟩
  · -- ¬mLift ge_w Aᶜ A: any g : A → Aᶜ restricts to A∩B → (A∩B)ᶜ
    intro ⟨g, hg, ginj⟩
    exact hABnot ⟨g,
      fun b hb => ⟨fun h => (hg b hb.1).1 h.1, (hg b hb.1).2⟩,
      fun b₁ b₂ h1 h2 => ginj b₁ b₂ h1.1 h2.1⟩
  · -- mLift ge_w B Bᶜ: restrict f from (A∩B)ᶜ to Bᶜ
    exact ⟨f,
      fun b hb => ⟨(hf b (fun h => hb h.2)).1.2, (hf b (fun h => hb h.2)).2⟩,
      fun b₁ b₂ h1 h2 => hinj b₁ b₂ (fun h => h1 h.2) (fun h => h2 h.2)⟩
  · -- ¬mLift ge_w Bᶜ B: any g : B → Bᶜ restricts to A∩B → (A∩B)ᶜ
    intro ⟨g, hg, ginj⟩
    exact hABnot ⟨g,
      fun b hb => ⟨fun h => (hg b hb.2).1 h.2, (hg b hb.2).2⟩,
      fun b₁ b₂ h1 h2 => ginj b₁ b₂ h1.2 h2.2⟩

theorem mLift_V3 {W : Type*} (ge_w : W → W → Prop) :
    patternV3 (mLift ge_w) := by
  intro A B ⟨hA, hAnot⟩
  obtain ⟨f, hf, hinj⟩ := hA
  constructor
  · -- ge (A ∪ B) (A ∪ B)ᶜ: f maps Aᶜ ↪ A, and (A ∪ B)ᶜ ⊆ Aᶜ,
    -- so restriction to (A ∪ B)ᶜ still injective, images land in A ⊆ A ∪ B.
    rw [Set.compl_union]
    exact ⟨f,
      fun b ⟨hbAc, _⟩ =>
        let ⟨ha, hge⟩ := hf b hbAc
        ⟨Set.mem_union_left B ha, hge⟩,
      fun b₁ b₂ ⟨h1, _⟩ ⟨h2, _⟩ => hinj b₁ b₂ h1 h2⟩
  · -- ¬ge (A ∪ B)ᶜ (A ∪ B): if so, restricting g to A ⊆ A ∪ B
    -- gives an injection A → Aᶜ (since (A ∪ B)ᶜ ⊆ Aᶜ), contradicting hAnot.
    intro ⟨g, hg, ginj⟩
    apply hAnot
    exact ⟨g,
      fun b hbA => by
        obtain ⟨hgc, hge⟩ := hg b (Set.mem_union_left B hbA)
        exact ⟨fun hga => hgc (Set.mem_union_left B hga), hge⟩,
      fun b₁ b₂ h1 h2 =>
        ginj b₁ b₂ (Set.mem_union_left B h1) (Set.mem_union_left B h2)⟩

theorem mLift_V4 {W : Type*} (ge_w : W → W → Prop) :
    patternV4 (mLift ge_w) := by
  intro A; exact ⟨id, fun b hb => hb.elim, fun _ _ h1 => h1.elim⟩

theorem mLift_V5 {W : Type*} (ge_w : W → W → Prop) (hRefl : ∀ w, ge_w w w) :
    patternV5 (mLift ge_w) := by
  intro A; exact ⟨id, fun b hb => ⟨Set.mem_univ b, hRefl b⟩, fun _ _ _ _ h => h⟩

theorem mLift_V6 {W : Type*} [Nonempty W] (ge_w : W → W → Prop) :
    patternV6 (mLift ge_w) := by
  intro A hAc
  -- mLift ge_w ∅ Aᶜ forces Aᶜ = ∅ (no injection from Aᶜ to ∅)
  have hAuniv : A = Set.univ := by
    ext x; simp only [Set.mem_univ, iff_true]
    by_contra hx; obtain ⟨f, hf, _⟩ := hAc; obtain ⟨ha, _⟩ := hf x hx; exact ha.elim
  subst hAuniv
  show mLift ge_w Set.univ Set.univᶜ ∧ ¬mLift ge_w Set.univᶜ Set.univ
  rw [Set.compl_univ]
  exact ⟨⟨id, fun b hb => hb.elim, fun _ _ h1 => h1.elim⟩,
    fun ⟨f, hf, _⟩ => by
      obtain ⟨w⟩ := ‹Nonempty W›
      obtain ⟨ha, _⟩ := hf w (Set.mem_univ w)
      exact ha.elim⟩

theorem mLift_V7 {W : Type*} (ge_w : W → W → Prop) :
    patternV7 (mLift ge_w) := by
  intro A ⟨_, hAnot⟩ hempty
  -- hempty : mLift ge_w ∅ A, i.e. ∃ f, ∀ b ∈ A, f b ∈ ∅ — impossible if A nonempty
  obtain ⟨f, hf, _⟩ := hempty
  by_cases hne : (A : Set W).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨ha, _⟩ := hf x hx; exact ha.elim
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.compl_empty] at hAnot
    exact hAnot ⟨id, fun b hb => hb.elim, fun _ _ h1 => h1.elim⟩

-- V11–V13 require [Finite W] and reflexivity (and V11/V12 additionally
-- need transitivity). The paper (@cite{holliday-icard-2013}) assumes a
-- finite poset (W, ≥). The proofs of V11 and V12 follow the companion
-- paper @cite{harrison-trainor-holliday-icard-2018} (Definition 3.1,
-- Lemma 3.7): the injection extension ≥ⁱ (= mLift) is a GFC order,
-- which implies V12 directly. The key lemma is *complement reversal*:
-- mLift ge_w B A → mLift ge_w Aᶜ Bᶜ (via an f-chain construction on
-- elements of A ∩ Bᶜ). V12 then follows from complement reversal +
-- two applications of mLift transitivity.

-- ── Helper: mLift transitivity ──

private theorem mLift_trans {W : Type*} {ge_w : W → W → Prop}
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w)
    {A B C : Set W} (hAB : mLift ge_w A B) (hBC : mLift ge_w B C) :
    mLift ge_w A C := by
  obtain ⟨f, hf, hinj_f⟩ := hAB
  obtain ⟨g, hg, hinj_g⟩ := hBC
  exact ⟨f ∘ g, fun c hc =>
    ⟨(hf (g c) (hg c hc).1).1, hTrans _ _ _ (hf (g c) (hg c hc).1).2 (hg c hc).2⟩,
    fun c₁ c₂ hc1 hc2 heq =>
    hinj_g c₁ c₂ hc1 hc2 (hinj_f (g c₁) (g c₂) (hg c₁ hc1).1 (hg c₂ hc2).1 heq)⟩

-- ── Helper lemmas for the f-chain construction ──

/-- If iterates f^[0],...,f^[n-1] of p stay in A, then f^[n] p ∈ B for n ≥ 1. -/
private theorem mLift_iter_in_B {W : Type*} {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B) {p : W}
    (n : ℕ) (hn : n ≥ 1) (hA : ∀ m, m < n → f^[m] p ∈ A) :
    f^[n] p ∈ B := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Function.iterate_succ', Function.comp_apply]
  exact hfmem _ (hA m (by omega))

/-- Iterates of p ∈ A \ B are pairwise distinct while staying in A. -/
private theorem mLift_iter_ne_of_lt {W : Type*} {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B)
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {p : W} (hpB : p ∉ B) (hall : ∀ m, f^[m] p ∈ A) :
    ∀ i j, i < j → f^[i] p ≠ f^[j] p := by
  intro i
  induction i with
  | zero =>
    intro j hj heq
    have : f^[j] p ∈ B := mLift_iter_in_B hfmem j (by omega) (fun m _ => hall m)
    simp only [Function.iterate_zero, id_eq] at heq
    exact hpB (heq ▸ this)
  | succ i' ih =>
    intro j hj heq
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [Function.iterate_succ', Function.comp_apply] at heq
    exact ih j' (by omega) (hfinj _ _ (hall i') (hall j') heq)

/-- The f-chain starting at p ∈ A \ B must eventually exit A. -/
private theorem mLift_chain_exits {W : Type*} [Finite W] {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B)
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {p : W} (hp : p ∈ A) (hpB : p ∉ B) :
    ∃ n, f^[n] p ∉ A := by
  by_contra h; push_neg at h
  have hall : ∀ m, f^[m] p ∈ A := by
    intro m; cases m with
    | zero => simpa
    | succ m => exact h (m + 1)
  have hdist := mLift_iter_ne_of_lt hfmem hfinj hpB hall
  have hinj : Function.Injective (fun n : ℕ => (⟨f^[n] p, hall n⟩ : ↥A)) := by
    intro i j heq; simp only [Subtype.mk.injEq] at heq
    rcases lt_trichotomy i j with h | h | h
    · exact absurd heq (hdist i j h)
    · exact h
    · exact absurd heq.symm (hdist j i h)
  haveI : Infinite ↥A := Infinite.of_injective _ hinj
  exact not_finite ↥A

/-- If both chains stay in A for n steps and f^[n] x = f^[n] y, then x = y. -/
private theorem mLift_iterate_inj_of_mem {W : Type*} {A : Set W} {f : W → W}
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {x y : W} {n : ℕ}
    (hx : ∀ m, m < n → f^[m] x ∈ A) (hy : ∀ m, m < n → f^[m] y ∈ A)
    (heq : f^[n] x = f^[n] y) : x = y := by
  induction n with
  | zero => simpa using heq
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply] at heq
    exact ih (fun m hm => hx m (by omega)) (fun m hm => hy m (by omega))
      (hfinj _ _ (hx n (by omega)) (hy n (by omega)) heq)

/-- Two f-chains landing at the same point must have started at the same point.
    Handles all four injectivity cases uniformly via `wlog`. -/
private theorem mLift_chain_origin_eq {W : Type*} {A B : Set W} {f : W → W}
    (hfmem : ∀ a, a ∈ A → f a ∈ B)
    (hfinj : ∀ a₁ a₂, a₁ ∈ A → a₂ ∈ A → f a₁ = f a₂ → a₁ = a₂)
    {p₁ p₂ : W} {k₁ k₂ : ℕ}
    (hp1 : p₁ ∉ B) (hp2 : p₂ ∉ B)
    (hk1 : ∀ m, m < k₁ → f^[m] p₁ ∈ A)
    (hk2 : ∀ m, m < k₂ → f^[m] p₂ ∈ A)
    (heq : f^[k₁] p₁ = f^[k₂] p₂) : p₁ = p₂ := by
  wlog hle : k₁ ≤ k₂ with H
  · exact (H hfmem hfinj hp2 hp1 hk2 hk1 heq.symm (by omega)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Function.iterate_add_apply] at heq
  have hpeeled := mLift_iterate_inj_of_mem hfinj hk1
    (fun m hm => by rw [← Function.iterate_add_apply]; exact hk2 (m + d) (by omega)) heq
  cases d with
  | zero => simpa using hpeeled
  | succ d => exact absurd (hpeeled ▸ mLift_iter_in_B hfmem (d + 1) (by omega)
      fun m hm => hk2 m (by omega)) hp1

/-- Dominance through a chain: ge_w (f^[n] p) p (including n = 0 by reflexivity). -/
private theorem mLift_chain_dominance {W : Type*} {A : Set W}
    {ge_w : W → W → Prop} {f : W → W}
    (hRefl : ∀ w, ge_w w w)
    (hfge : ∀ a, a ∈ A → ge_w (f a) a)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w)
    {p : W} (n : ℕ) (hp : ∀ m, m < n → f^[m] p ∈ A) :
    ge_w (f^[n] p) p := by
  induction n with
  | zero => simpa using hRefl p
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact hTrans _ _ _ (hfge _ (hp n (by omega))) (ih fun m hm => hp m (by omega))

-- ── Complement reversal ──

/-- Complement reversal: mLift ge_w B A → mLift ge_w Aᶜ Bᶜ.
    Maps p ∈ A ∩ Bᶜ to f^[k](p) (first exit from A) and
    q ∈ Aᶜ ∩ Bᶜ to q (reflexivity). Injectivity of all four
    cross-cases follows from `chain_origin_eq`
    (@cite{harrison-trainor-holliday-icard-2018}, Lemma 3.7). -/
private theorem mLift_complement_reversal {W : Type*} [Finite W]
    {ge_w : W → W → Prop}
    (hRefl : ∀ w, ge_w w w) (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w)
    {A B : Set W} (h : mLift ge_w B A) : mLift ge_w Aᶜ Bᶜ := by
  obtain ⟨f, hf, hinj_f⟩ := h
  have hfmem : ∀ a, a ∈ A → f a ∈ B := fun a ha => (hf a ha).1
  have hfge : ∀ a, a ∈ A → ge_w (f a) a := fun a ha => (hf a ha).2
  classical
  have hExits : ∀ p, p ∈ A → p ∉ B → ∃ n, f^[n] p ∉ A :=
    fun p hp hpB => mLift_chain_exits hfmem hinj_f hp hpB
  let ei (w : W) (hwA : w ∈ A) (hwB : w ∉ B) := Nat.find (hExits w hwA hwB)
  have ei_spec : ∀ w hwA hwB, f^[ei w hwA hwB] w ∉ A :=
    fun w hwA hwB => Nat.find_spec (hExits w hwA hwB)
  have ei_min : ∀ w hwA hwB m, m < ei w hwA hwB → f^[m] w ∈ A :=
    fun w hwA hwB m hm => by_contra fun h => Nat.find_min (hExits w hwA hwB) hm h
  -- The witness: f^[k] for A ∩ Bᶜ (chain exit), identity for Aᶜ ∩ Bᶜ
  let g : W → W := fun w =>
    if hwA : w ∈ A then if hwB : w ∈ B then w else f^[ei w hwA hwB] w else w
  -- Express g(b') as f^[k] b' uniformly for all b' ∈ Bᶜ
  have g_iter : ∀ b' (_ : b' ∉ B), ∃ k,
      g b' = f^[k] b' ∧ f^[k] b' ∉ A ∧ ∀ m, m < k → f^[m] b' ∈ A := by
    intro b' hb'
    by_cases hbA : b' ∈ A
    · exact ⟨ei b' hbA hb', by simp [g, dif_pos hbA, dif_neg hb'],
        ei_spec b' hbA hb', ei_min b' hbA hb'⟩
    · exact ⟨0, by simp [g, dif_neg hbA], hbA, fun _ hm => absurd hm (by omega)⟩
  refine ⟨g, fun b' hb' => ?_, fun b₁ b₂ hb1 hb2 heq => ?_⟩
  · -- Membership in Aᶜ and dominance
    obtain ⟨k, hgk, hnotA, hkA⟩ := g_iter b' hb'
    exact ⟨hgk ▸ hnotA, hgk ▸ mLift_chain_dominance hRefl hfge hTrans k hkA⟩
  · -- Injectivity: all four cases via chain_origin_eq
    obtain ⟨k₁, hgk1, -, hk1A⟩ := g_iter b₁ hb1
    obtain ⟨k₂, hgk2, -, hk2A⟩ := g_iter b₂ hb2
    rw [hgk1, hgk2] at heq
    exact mLift_chain_origin_eq hfmem hinj_f hb1 hb2 hk1A hk2A heq

-- ── V12 and V11 ──

/-- V12 is valid for the m-lifting on finite posets (Fact 5 in
    @cite{holliday-icard-2013}; proof via @cite{harrison-trainor-holliday-icard-2018},
    Lemma 3.7). The proof decomposes into complement reversal
    (mLift ge_w B A → mLift ge_w Aᶜ Bᶜ) and two applications of
    mLift transitivity: B ≿ A ≿ Aᶜ ≿ Bᶜ. -/
theorem mLift_V12 {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV12 (mLift ge_w) := by
  intro A B hBA hAAc
  have hAcBc := mLift_complement_reversal hRefl hTrans hBA
  exact mLift_trans hTrans hBA (mLift_trans hTrans hAAc hAcBc)

/-- V11 is valid for the m-lifting on finite posets (Fact 5 in
    @cite{holliday-icard-2013}). The ge half follows from V12; the strict
    half uses complement reversal + transitivity to derive a contradiction
    with the "probably A" hypothesis. -/
theorem mLift_V11 {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    patternV11 (mLift ge_w) := by
  intro A B hBA ⟨hAAc, hNotAcA⟩
  constructor
  · exact mLift_V12 ge_w hRefl hTrans A B hBA hAAc
  · intro hBcB
    apply hNotAcA
    have hBcA := mLift_trans hTrans hBcB hBA
    have hAcBcc := mLift_complement_reversal hRefl hTrans hBcA
    rw [compl_compl] at hAcBcc
    exact mLift_trans hTrans hAcBcc hBA

/-- V13 is valid for the m-lifting on finite posets (Fact 5 in
    @cite{holliday-icard-2013}). The ge half uses id on B (reflexivity);
    the strict half uses pigeonhole (|A∪B| > |B| since A\B nonempty,
    finiteness). -/
theorem mLift_V13 {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (_hRefl : ∀ w, ge_w w w) :
    patternV13 (mLift ge_w) := by
  intro A B ⟨_, hNotEmpty⟩
  have hABne : (A \ B).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hNotEmpty; rw [h]
    exact ⟨id, fun b hb => hb.elim, fun _ _ _ _ h => h⟩
  constructor
  · exact ⟨id, fun b hb => ⟨Set.mem_union_right A hb, _hRefl b⟩,
           fun _ _ _ _ h => h⟩
  · intro ⟨f, hf, hinj⟩
    have hle : (A ∪ B).ncard ≤ B.ncard :=
      Set.ncard_le_ncard_of_injOn f (fun b hb => (hf b hb).1)
        (fun b₁ hb₁ b₂ hb₂ heq => hinj b₁ b₂ hb₁ hb₂ heq) (Set.toFinite _)
    have hsub : B ⊂ A ∪ B := by
      constructor
      · exact Set.subset_union_right
      · intro h; obtain ⟨x, hx⟩ := hABne
        exact hx.2 (h (Set.mem_union_left B hx.1))
    have hlt : B.ncard < (A ∪ B).ncard :=
      Set.ncard_lt_ncard hsub (Set.toFinite _)
    omega

/-- I1 is **invalid** for the m-lifting (Fact 5 in @cite{holliday-icard-2013}).
    Counterexample: W = Fin 2, ge_w total. A = {0}, B = {0}, C = {1}.
    mLift A B and mLift A C both hold (singleton ↪ singleton), but
    ¬mLift A (B ∪ C) since |A| = 1 < 2 = |B ∪ C| (no injection). -/
theorem mLift_not_I1 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI1 (mLift ge_w) := by
  refine ⟨Fin 2, fun _ _ => True, fun _ => trivial, ?_⟩
  intro h
  -- I1 says: A ≿ B → A ≿ C → A ≿ (B ∪ C)
  -- Take A = {0}, B = {0}, C = {1}
  have hAB : mLift (fun (_ _ : Fin 2) => True) {(0 : Fin 2)} {0} :=
    ⟨id, fun b hb => ⟨hb, trivial⟩, fun _ _ _ _ h => h⟩
  have hAC : mLift (fun (_ _ : Fin 2) => True) {(0 : Fin 2)} {1} :=
    ⟨fun _ => 0, fun _ hb => ⟨rfl, trivial⟩,
     fun b₁ b₂ h1 h2 _ => by
       rw [Set.mem_singleton_iff] at h1 h2; rw [h1, h2]⟩
  have hresult := h {(0 : Fin 2)} {0} {1} hAB hAC
  -- hresult : mLift {0} ({0} ∪ {1}) = mLift {0} univ
  have huniv : ({0} : Set (Fin 2)) ∪ {1} = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]; omega
  rw [huniv] at hresult
  obtain ⟨f, hf, hinj⟩ := hresult
  -- f : Fin 2 → Fin 2 with f(b) ∈ {0} for all b, i.e. f = const 0
  have hf0 : f 0 ∈ ({0} : Set (Fin 2)) := (hf 0 (Set.mem_univ _)).1
  have hf1 : f 1 ∈ ({0} : Set (Fin 2)) := (hf 1 (Set.mem_univ _)).1
  rw [Set.mem_singleton_iff] at hf0 hf1
  -- f 0 = 0 and f 1 = 0, but f is injective on univ → 0 = 1, contradiction
  have := hinj 0 1 (Set.mem_univ _) (Set.mem_univ _) (by rw [hf0, hf1])
  exact absurd this (by omega)

/-- I2 is **invalid** for the m-lifting (Fact 5 in @cite{holliday-icard-2013}).
    Counterexample: W = Fin 3, ge_w total. A = {0,1}, B = univ.
    mLift A Aᶜ holds (|Aᶜ| = 1 ≤ 2 = |A|), but ¬mLift A univ
    since |A| = 2 < 3 = |univ|. -/
theorem mLift_not_I2 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI2 (mLift ge_w) := by
  refine ⟨Fin 3, fun _ _ => True, fun _ => trivial, ?_⟩
  intro h
  -- A = {0,1}, B = univ
  -- A ≿ Aᶜ: Aᶜ = {2}, need injection {2} → {0,1}, e.g. f(2) = 0
  have hAAc : mLift (fun (_ _ : Fin 3) => True) ({0, 1} : Set (Fin 3)) ({0, 1} : Set (Fin 3))ᶜ := by
    refine ⟨fun _ => 0, fun b hb => ⟨Set.mem_insert 0 {1}, trivial⟩, ?_⟩
    intro b₁ b₂ hb1 hb2 _
    -- b₁, b₂ ∈ {0,1}ᶜ = {2}
    have : b₁ ∈ ({0, 1} : Set (Fin 3))ᶜ := hb1
    have : b₂ ∈ ({0, 1} : Set (Fin 3))ᶜ := hb2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at *
    omega
  -- I2 gives: mLift A univ
  have hresult := h ({0, 1} : Set (Fin 3)) Set.univ hAAc
  obtain ⟨f, hf, hinj⟩ := hresult
  -- f : Fin 3 → Fin 3 with f(b) ∈ {0,1} for all b ∈ univ
  -- So f maps {0,1,2} → {0,1}: pigeonhole, not injective
  have h0 := (hf 0 (Set.mem_univ _)).1
  have h1 := (hf 1 (Set.mem_univ _)).1
  have h2 := (hf 2 (Set.mem_univ _)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1 h2
  -- f maps 3 elements to {0,1} — pigeonhole
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
    | (have := hinj 0 1 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)
    | (have := hinj 0 2 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)
    | (have := hinj 1 2 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)

/-- I3 is **invalid** for the m-lifting (Fact 5 in @cite{holliday-icard-2013}).
    Same counterexample as I2: W = Fin 3, ge_w total, A = {0,1}, B = univ.
    A ≿ Aᶜ (injection {2} → {0,1}) and ¬(Aᶜ ≿ A) (no injection {0,1} → {2}),
    so probably A. But ¬(A ≿ univ) by cardinality. -/
theorem mLift_not_I3 :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧ ¬patternI3 (mLift ge_w) := by
  refine ⟨Fin 3, fun _ _ => True, fun _ => trivial, ?_⟩
  intro h
  -- A = {0,1}, B = univ. probably A holds, but ¬mLift A univ.
  have hprob : probably (mLift (fun (_ _ : Fin 3) => True)) ({0, 1} : Set (Fin 3)) := by
    constructor
    · -- mLift A Aᶜ: Aᶜ = {2}, inject f(2) = 0
      refine ⟨fun _ => 0, fun b hb => ⟨Set.mem_insert 0 {1}, trivial⟩, ?_⟩
      intro b₁ b₂ hb1 hb2 _
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb1 hb2
      omega
    · -- ¬mLift Aᶜ A: Aᶜ = {2}, need injection {0,1} → {2}, impossible
      intro ⟨f, hf, hinj⟩
      have h0 := (hf 0 (Set.mem_insert 0 {1})).1
      have h1 := (hf 1 (Or.inr rfl : (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)))).1
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h0 h1
      have := hinj 0 1 (Set.mem_insert 0 {1}) (Or.inr rfl) (by omega)
      omega
  have hresult := h ({0, 1} : Set (Fin 3)) Set.univ hprob
  obtain ⟨f, hf, hinj⟩ := hresult
  have h0 := (hf 0 (Set.mem_univ _)).1
  have h1 := (hf 1 (Set.mem_univ _)).1
  have h2 := (hf 2 (Set.mem_univ _)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 h1 h2
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
    | (have := hinj 0 1 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)
    | (have := hinj 0 2 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)
    | (have := hinj 1 2 (Set.mem_univ _) (Set.mem_univ _) (by omega); omega)

-- ── GFC Preorder (Definition 2.7 / Theorem 3.2) ──

/-- The m-lifting is NOT total, even for total preorders on worlds.
    Counterexample: W = Fin 4, ge_w = (· ≥ ·), A = {3, 0}, B = {2, 1}.
    Neither A ≿ⁱ B (only 3 dominates 2, leaving nothing for 1) nor
    B ≿ⁱ A (nothing in B dominates 3). -/
theorem mLift_not_total :
    ∃ (W : Type) (ge_w : W → W → Prop),
      (∀ w, ge_w w w) ∧
      (∀ u v w, ge_w u v → ge_w v w → ge_w u w) ∧
      (∀ u v, ge_w u v ∨ ge_w v u) ∧
      ∃ A B : Set W, ¬mLift ge_w A B ∧ ¬mLift ge_w B A := by
  refine ⟨Fin 4, (· ≥ ·), fun w => le_refl w, fun u v w huv hvw => le_trans hvw huv,
    fun u v => le_total v u, {3, 0}, {2, 1}, ?_, ?_⟩
  · intro ⟨f, hf, hinj⟩
    have h2 := hf 2 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    have h1 := hf 1 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h2 h1
    have hf2 : f 2 = 3 := by omega
    have hf1 : f 1 = 3 := by omega
    exact absurd (hinj 2 1 (by simp) (by simp) (by rw [hf2, hf1])) (by omega)
  · intro ⟨f, hf, _⟩
    have h3 := hf 3 (by simp [Set.mem_insert_iff, Set.mem_singleton_iff])
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h3
    omega

/-- The m-lifting of a reflexive, transitive world ordering on finite W
    is a GFC preorder (@cite{harrison-trainor-holliday-icard-2018}, Theorem 3.2).

    This is the key structural result connecting world-ordering semantics
    to the axiomatic hierarchy: the injection extension ≿ⁱ (= mLift)
    satisfies all three GFC axiom groups — preorder (G), monotonicity (F),
    and complement reversal (C). -/
def mLift_toGFCPreorder {W : Type*} [Finite W] (ge_w : W → W → Prop)
    (hRefl : ∀ w, ge_w w w)
    (hTrans : ∀ u v w, ge_w u v → ge_w v w → ge_w u w) :
    GFCPreorder W where
  ge := mLift ge_w
  refl := mLift_axiomR hRefl
  trans := fun _ _ _ => mLift_trans hTrans
  mono := mLift_axiomT hRefl
  complRev := fun _ _ h => mLift_complement_reversal hRefl hTrans h

end MLift

end Core.Scale
