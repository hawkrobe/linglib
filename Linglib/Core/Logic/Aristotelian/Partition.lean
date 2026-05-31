import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Partitions induced by logical fragments

Per @cite{demey-smessaert-2018} §3.1. The partition of a finite fragment
`φ : ι → W → Bool` is its set of consistent *anchor formulas* — complete
conjunctions of literals `±φ i`. The anchors are mutually exclusive and jointly
exhaustive (Lemma 3), and their count is the bitstring length.

## Main declarations

* `anchor` — the anchor formula of a polarity assignment (Definition 5).
* `partition` — the consistent anchors of a fragment.
* `anchor_mutually_exclusive` / `anchor_jointly_exhaustive` — Lemma 3.
-/

namespace Aristotelian

variable {W : Type*}

/-! ### Polarity literals -/

/-- A literal over a Boolean predicate: the predicate or its negation. -/
inductive Literal (W : Type*) where
  | pos (φ : W → Bool)
  | neg (φ : W → Bool)

/-- Interpret a literal as a Boolean predicate. -/
def Literal.eval : Literal W → W → Bool
  | .pos φ, w => φ w
  | .neg φ, w => !φ w

/-- A polarity assignment selects one literal per fragment formula. -/
abbrev PolarityAssignment (ι : Type*) (W : Type*) := ι → (W → Bool) → Literal W

/-! ### Anchor formulas (Definition 5) -/

/-- The anchor formula for polarity assignment `σ`: the conjunction `±φ_1 ∧ ⋯ ∧ ±φ_m`. -/
def anchor {ι : Type*} [Fintype ι] (φ : ι → W → Bool)
    (σ : ι → Bool) (w : W) : Bool :=
  decide (∀ i : ι, if σ i then (φ i w = true) else (φ i w = false))

/-- An anchor formula is consistent if it is satisfiable in some world. -/
def anchorConsistent {ι : Type*} [Fintype ι] (φ : ι → W → Bool)
    (σ : ι → Bool) : Prop :=
  ∃ w : W, anchor φ σ w = true

/-- The partition of a fragment: all consistent polarity assignments. -/
def partition (ι : Type*) [Fintype ι] [DecidableEq ι] (W : Type*) [Fintype W]
    (φ : ι → W → Bool) : Finset (ι → Bool) :=
  Finset.univ.filter (fun σ => decide (∃ w : W, anchor φ σ w = true))

/-! ### Lemma 3 — mutual exclusivity and joint exhaustion -/

/-- Two distinct anchor formulas are jointly inconsistent. -/
theorem anchor_mutually_exclusive {ι : Type*} [Fintype ι]
    (φ : ι → W → Bool) (σ τ : ι → Bool) (h : σ ≠ τ) :
    ∀ w, ¬ (anchor φ σ w = true ∧ anchor φ τ w = true) := by
  intro w ⟨hσ, hτ⟩
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ τ i := by
    by_contra hAll
    push Not at hAll
    exact h (funext hAll)
  rw [anchor, decide_eq_true_eq] at hσ hτ
  have hσi := hσ i
  have hτi := hτ i
  rcases hσ_val : σ i with _ | _ <;> rcases hτ_val : τ i with _ | _
  all_goals simp_all

/-- Every world satisfies some anchor formula. -/
theorem anchor_jointly_exhaustive {ι : Type*} [Fintype ι]
    (φ : ι → W → Bool) (w : W) :
    ∃ σ, anchor φ σ w = true := by
  refine ⟨fun i => φ i w, ?_⟩
  rw [anchor, decide_eq_true_eq]
  intro i
  by_cases h : φ i w = true
  · simp [h]
  · have : φ i w = false := by cases hb : φ i w <;> simp_all
    simp [this]

/-! ### Meet of partitions (Definition 6) -/

/-- The meet of two partitions: anchors of the union fragment (Lemma 4). -/
def partitionMeet {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] {W : Type*} [Fintype W]
    (φ₁ : ι₁ → W → Bool) (φ₂ : ι₂ → W → Bool) :
    Finset ((ι₁ → Bool) × (ι₂ → Bool)) :=
  (Finset.univ.product Finset.univ).filter (fun p =>
    decide (∃ w : W, anchor φ₁ p.1 w = true ∧ anchor φ₂ p.2 w = true))

end Aristotelian
