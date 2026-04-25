import Linglib.Core.Logic.Opposition.Aristotelian
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Partitions induced by logical fragments (skeleton)

Per @cite{demey-smessaert-2018} §3.1, Definitions 5–6.

Given a logical system `S` and a finite fragment `ℱ = {φ_1, ..., φ_m}`, the
partition `Π_S(ℱ)` is the set of *anchor formulas* — maximal-information
conjunctions of literals over ℱ that are S-consistent:

  Π_S(ℱ) := {α | α ≡_S ±φ_1 ∧ ... ∧ ±φ_m, α is S-consistent}

The anchor formulas are mutually exclusive and jointly exhaustive (Lemma 3),
forming a partition of the model class. Their cardinality `n = |Π_S(ℱ)|`
determines the bitstring length: `|𝔹(ℱ)| = 2^n`.

-/

namespace Core.Opposition

variable {W : Type*}

-- ============================================================================
-- §1. Polarity literals
-- ============================================================================

/-- A *literal* over a Boolean predicate: either the predicate itself or
    its negation. Used to build anchor formulas. -/
inductive Literal (W : Type*) where
  | pos (φ : W → Bool)
  | neg (φ : W → Bool)

/-- Interpret a literal as a Boolean predicate. -/
def Literal.eval : Literal W → W → Bool
  | .pos φ, w => φ w
  | .neg φ, w => !φ w

/-- A *polarity assignment* selects one literal per fragment formula. -/
abbrev PolarityAssignment (ι : Type) (W : Type*) := ι → (W → Bool) → Literal W

-- ============================================================================
-- §2. Anchor formulas (Definition 5)
-- ============================================================================

/-- The anchor formula for polarity assignment `σ` over fragment `φ`:
    the conjunction `±φ_1 ∧ ... ∧ ±φ_m` with signs given by σ. -/
def anchor {ι : Type} [Fintype ι] (φ : ι → W → Bool)
    (σ : ι → Bool) (w : W) : Bool :=
  decide (∀ i : ι, if σ i then (φ i w = true) else (φ i w = false))

/-- An anchor formula is *consistent* if it is satisfiable in some world. -/
def anchorConsistent {ι : Type} [Fintype ι] (φ : ι → W → Bool)
    (σ : ι → Bool) : Prop :=
  ∃ w : W, anchor φ σ w = true

/-- The partition of a fragment: all consistent polarity assignments. -/
def partition (ι : Type) [Fintype ι] [DecidableEq ι] (W : Type*) [Fintype W]
    (φ : ι → W → Bool) : Finset (ι → Bool) :=
  Finset.univ.filter (fun σ => decide (∃ w : W, anchor φ σ w = true))

-- ============================================================================
-- §3. Lemma 3 — mutual exclusivity and joint exhaustion
-- ============================================================================

/-- Two distinct anchor formulas are jointly inconsistent. -/
theorem anchor_mutually_exclusive {ι : Type} [Fintype ι]
    (φ : ι → W → Bool) (σ τ : ι → Bool) (h : σ ≠ τ) :
    ∀ w, ¬ (anchor φ σ w = true ∧ anchor φ τ w = true) := by
  intro w ⟨hσ, hτ⟩
  -- σ ≠ τ ⇒ ∃ i, σ i ≠ τ i
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra hAll
    push_neg at hAll
    exact h (funext hAll)
  -- Unpack both anchor conditions at index i
  rw [anchor, decide_eq_true_eq] at hσ hτ
  have hσi := hσ i
  have hτi := hτ i
  -- σ i ≠ τ i means one is true, the other false; derive contradiction on φ i w
  rcases hσ_val : σ i with _ | _ <;> rcases hτ_val : τ i with _ | _
  all_goals simp_all

/-- Every world satisfies exactly one anchor formula (joint exhaustion). -/
theorem anchor_jointly_exhaustive {ι : Type} [Fintype ι]
    (φ : ι → W → Bool) (w : W) :
    ∃ σ, anchor φ σ w = true := by
  -- Take σ i := φ i w; then anchor φ σ w trivially holds
  refine ⟨fun i => φ i w, ?_⟩
  rw [anchor, decide_eq_true_eq]
  intro i
  by_cases h : φ i w = true
  · simp [h]
  · have : φ i w = false := by cases hb : φ i w <;> simp_all
    simp [this]

-- ============================================================================
-- §4. Meet of partitions (Definition 6)
-- ============================================================================

/-- The meet of two partitions: anchor formulas of the union fragment.
    Per Lemma 4, `Π(ℱ₁ ∪ ℱ₂) = Π(ℱ₁) ∧ Π(ℱ₂)`. -/
def partitionMeet {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] {W : Type*} [Fintype W]
    (φ₁ : ι₁ → W → Bool) (φ₂ : ι₂ → W → Bool) :
    Finset ((ι₁ → Bool) × (ι₂ → Bool)) :=
  (Finset.univ.product Finset.univ).filter (fun p =>
    decide (∃ w : W, anchor φ₁ p.1 w = true ∧ anchor φ₂ p.2 w = true))

end Core.Opposition
