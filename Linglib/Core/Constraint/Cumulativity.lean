import Linglib.Core.Constraint.Dequantization.OTLimit

/-!
# The Cumulativity Gap: HG ⊋ OT
@cite{pater-2009} @cite{coetzee-pater-2011} @cite{prince-2002}

Harmonic Grammar with non-negative weights is strictly more expressive than
Optimality Theory: every OT-realizable input→output mapping is HG-realizable
(via exponentially separated weights), but the converse fails. The
expressiveness gap is **cumulativity** — situations where the *sum* of
multiple low-weight constraint violations exceeds a single high-weight
violation. OT cannot express this; HG can.

This file states the gap as a theorem about *systemic* optimization problems
— a single grammar must simultaneously realize a target output for every
input. The single-tableau case (one input, one winner) does not exhibit the
gap; the gap appears only when multiple input-output pairs constrain a
shared global ranking/weighting.

## Definitions

- `SystemicProblem Input Output n` packages multi-input optimization data:
  inputs, candidates per input, n-dimensional violation profile, and the
  target mapping the grammar must realize.
- `HGRealizes` / `IsHGRealizable`: existence of a non-negative weighting
  under which the target output strictly minimizes weighted violations
  for every input.
- `OTRealizes` / `IsOTRealizable`: existence of a constraint permutation
  under which the target output strictly lex-dominates every alternative
  for every input.

## Theorems

- `ot_realizable_imp_hg_realizable`: forward containment via
  exponentially separated weights (lifts `lex_imp_lower_violations` to
  the multi-input setting).
- `hg_strictly_contains_ot`: strict-containment witness — the abstract
  Lyman's Law instance (3 inputs, 2 outputs each, 3 constraints) is
  HG-realizable but no OT ranking realizes it.

The Lyman's Law witness comes from @cite{coetzee-pater-2011} §4.2-4.3
(eq 18-19), originally @cite{ito-mester-1986} on Japanese loanword
voicing. It is the smallest known witness of the cumulativity gap.

## Where this is used

`Phenomena/Phonology/Studies/CoetzeePater2011.lean` instantiates the
abstract witness with concrete Japanese loanword forms (bobu, webbu,
guddo). Future studies of HG-vs-OT cumulativity (Pater 2009 stress
window cumulativity; French schwa; Tagalog nasal substitution) should
likewise consume `hg_strictly_contains_ot` rather than re-deriving the
gap per-paper.
-/

namespace Core.Constraint

open Core.Constraint.OT Finset

-- ============================================================================
-- § 1: Decidable Lex Comparison
-- ============================================================================

/-- `LexStrictlyBetter` on `Fin n → ℕ` is decidable: the existential ranges
    over `Fin n`, the witness predicates are over `Fin` with decidable
    equality and decidable order. Required for `decide`-based realizability
    checks on concrete instances. -/
instance decLexStrictlyBetter {n : ℕ} (va vb : Fin n → ℕ) :
    Decidable (LexStrictlyBetter va vb) := by
  unfold LexStrictlyBetter; infer_instance

-- ============================================================================
-- § 2: Systemic Optimization Problem
-- ============================================================================

/-- A multi-input optimization problem with a target mapping that a grammar
    must simultaneously realize for every input. The cumulativity gap lives
    here, not at the single-tableau level. -/
structure SystemicProblem (Input : Type*) (Output : Type*) (n : ℕ) where
  /-- The set of inputs the grammar handles. -/
  inputs : Finset Input
  /-- Candidate set for each input. -/
  cands : Input → Finset Output
  /-- Violation profile: `vp i o k` is the count of constraint `k` violations
      incurred by output `o` from input `i`. -/
  vp : Input → Output → Fin n → ℕ
  /-- The output the grammar must select for each input. -/
  target : Input → Output
  /-- Each target output is in its input's candidate set. -/
  target_mem : ∀ i ∈ inputs, target i ∈ cands i

namespace SystemicProblem

variable {Input Output : Type*} {n : ℕ}

/-- A weighting `w` **HG-realizes** the target if, for every input, the target
    output strictly minimizes the weighted violation sum among candidates. -/
def HGRealizes (P : SystemicProblem Input Output n) (w : Fin n → ℚ) : Prop :=
  ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
    weightedViolations w (P.vp i (P.target i)) <
    weightedViolations w (P.vp i o)

/-- A problem is **HG-realizable** if some non-negative weighting realizes
    the target. Restricting to non-negative weights matches @cite{pater-2009}'s
    standard HG framework; @cite{coetzee-pater-2011} §4.4 discusses the
    consequences of admitting negative weights (e.g., Tejano' realizability). -/
def IsHGRealizable (P : SystemicProblem Input Output n) : Prop :=
  ∃ w : Fin n → ℚ, (∀ k, 0 ≤ w k) ∧ P.HGRealizes w

/-- A constraint permutation `σ` **OT-realizes** the target if, for every
    input, the target output strictly lex-dominates every alternative under
    the ranking `σ` (smallest σ-index = highest-ranked constraint). -/
def OTRealizes (P : SystemicProblem Input Output n) (σ : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, o ≠ P.target i →
    LexStrictlyBetter
      (fun k : Fin n => P.vp i (P.target i) (σ k))
      (fun k : Fin n => P.vp i o (σ k))

/-- A problem is **OT-realizable** if some constraint permutation realizes
    the target. -/
def IsOTRealizable (P : SystemicProblem Input Output n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), P.OTRealizes σ

end SystemicProblem

-- ============================================================================
-- § 3: Forward Containment — OT ⊆ HG
-- ============================================================================

/-- Re-indexing weighted violations through a permutation. The weighting
    `w ∘ σ⁻¹` evaluated at violation profile `v` equals the weighting `w`
    evaluated at `v ∘ σ` — i.e., permuting weights is dual to permuting
    constraints. -/
private lemma weightedViolations_perm_reindex {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (w : Fin n → ℚ) (v : Fin n → ℕ) :
    weightedViolations (fun j => w (σ.symm j)) v =
    weightedViolations w (v ∘ σ) := by
  simp only [weightedViolations, Function.comp_apply]
  rw [← Equiv.sum_comp σ (fun j => w (σ.symm j) * (v j : ℚ))]
  apply Finset.sum_congr rfl
  intro k _
  simp [Equiv.symm_apply_apply]

/-- **Forward containment**: every OT-realizable systemic problem is
    HG-realizable, with concrete witness given by exponentially-separated
    weights `w(j) = (M+1)^(n-1-σ⁻¹(j))` permuted by the OT ranking.

    This lifts `lex_imp_lower_violations` from one tableau to the multi-input
    setting: the same exponentially-spaced weights work uniformly for every
    input because the lex-dominance of the target is preserved input-wise. -/
theorem ot_realizable_imp_hg_realizable {Input Output : Type*} {n : ℕ}
    (P : SystemicProblem Input Output n) (M : ℕ) (hM : 0 < M)
    (hbound : ∀ i ∈ P.inputs, ∀ o ∈ P.cands i, ∀ k, P.vp i o k ≤ M) :
    P.IsOTRealizable → P.IsHGRealizable := by
  rintro ⟨σ, hσ⟩
  refine ⟨fun j => expWeights n M (σ.symm j), ?_, ?_⟩
  · intro k
    exact (expWeights_pos n M (σ.symm k)).le
  · intro i hi o ho hne
    rw [weightedViolations_perm_reindex σ, weightedViolations_perm_reindex σ]
    apply lex_imp_lower_violations _ M
    · intro k
      exact ⟨hbound i hi (P.target i) (P.target_mem i hi) (σ k),
             hbound i hi o ho (σ k)⟩
    · exact expWeights_separated n M hM
    · exact hσ i hi o ho hne

-- ============================================================================
-- § 4: Strict Containment Witness — Abstract Lyman's Law
-- ============================================================================

namespace Cumulativity

/-- Abstract Lyman's Law violation profile. Three constraints:
    `F` (faithfulness, e.g., IDENT-VOICE), `M1` (markedness, e.g., OCP-VOICE),
    `M2` (markedness, e.g., \*VCE-GEM). Three inputs, each with two
    outputs (faithful = `true`, unfaithful = `false`).

    | input    | faithful profile | unfaithful profile |
    | -------- | ---------------- | ------------------ |
    | 0 (bobu) | `[F=0, M1=1, M2=0]` | `[F=1, M1=0, M2=0]` |
    | 1 (webbu)| `[F=0, M1=0, M2=1]` | `[F=1, M1=0, M2=0]` |
    | 2 (guddo)| `[F=0, M1=1, M2=1]` | `[F=1, M1=0, M2=0]` | -/
def lymanVp : Fin 3 → Bool → Fin 3 → ℕ
  | 0, true,  ⟨0, _⟩ => 0  | 0, true,  ⟨1, _⟩ => 1  | 0, true,  ⟨2, _⟩ => 0
  | 0, false, ⟨0, _⟩ => 1  | 0, false, ⟨1, _⟩ => 0  | 0, false, ⟨2, _⟩ => 0
  | 1, true,  ⟨0, _⟩ => 0  | 1, true,  ⟨1, _⟩ => 0  | 1, true,  ⟨2, _⟩ => 1
  | 1, false, ⟨0, _⟩ => 1  | 1, false, ⟨1, _⟩ => 0  | 1, false, ⟨2, _⟩ => 0
  | 2, true,  ⟨0, _⟩ => 0  | 2, true,  ⟨1, _⟩ => 1  | 2, true,  ⟨2, _⟩ => 1
  | 2, false, ⟨0, _⟩ => 1  | 2, false, ⟨1, _⟩ => 0  | 2, false, ⟨2, _⟩ => 0

/-- Target mapping: bobu and webbu surface faithfully (single voiced
    obstruent / single voiced geminate is tolerated); guddo devoices
    (cumulative pressure from both markedness violations exceeds the cost
    of a single faithfulness violation). -/
def lymanTarget : Fin 3 → Bool
  | 0 => true | 1 => true | 2 => false

/-- The abstract Lyman's Law systemic problem. -/
def lymanProblem : SystemicProblem (Fin 3) Bool 3 where
  inputs := Finset.univ
  cands := fun _ => Finset.univ
  vp := lymanVp
  target := lymanTarget
  target_mem := fun _ _ => Finset.mem_univ _

/-- HG witness weights: `[F=3, M1=2, M2=2]`. Each markedness weight is
    individually less than `F`, so faithfulness wins for inputs with at most
    one markedness violation (bobu, webbu); the *sum* `M1 + M2 = 4 > 3 = F`
    overrides faithfulness for guddo. -/
def lymanW : Fin 3 → ℚ
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 2

/-- The abstract Lyman's Law problem is HG-realizable with weights `[3,2,2]`. -/
theorem lyman_isHGRealizable : lymanProblem.IsHGRealizable := by
  refine ⟨lymanW, ?_, ?_⟩
  · intro ⟨k, hk⟩
    interval_cases k <;> (unfold lymanW; norm_num)
  · intro i _ o _ hne
    simp only [lymanProblem, weightedViolations, Fin.sum_univ_three]
    fin_cases i <;> cases o <;>
      first
      | (exfalso; exact hne rfl)
      | (simp only [lymanTarget, lymanVp, lymanW]; norm_num)

/-- The abstract Lyman's Law problem is **not** OT-realizable: no permutation
    of `{F, M1, M2}` lex-dominates the target for all three inputs. The
    structural argument:
    - bobu requires `F` to outrank `M1` (else faithful loses).
    - webbu requires `F` to outrank `M2` (else faithful loses).
    - guddo requires `F` *not* to be the top-ranked constraint (else
      unfaithful loses despite the cumulative pressure).

    The first two conditions place `F` above both markedness constraints,
    contradicting the third. The proof is closed by `decide` over the six
    permutations of `Fin 3` (using `decLexStrictlyBetter`). -/
theorem lyman_not_isOTRealizable : ¬ lymanProblem.IsOTRealizable := by
  show ¬ ∃ σ : Equiv.Perm (Fin 3),
    ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      ∀ o ∈ (Finset.univ : Finset Bool), o ≠ lymanTarget i →
        LexStrictlyBetter
          (fun k : Fin 3 => lymanVp i (lymanTarget i) (σ k))
          (fun k : Fin 3 => lymanVp i o (σ k))
  decide

end Cumulativity

/-- **The cumulativity gap**: HG with non-negative weights strictly contains
    OT. Some systemic problems are HG-realizable but no OT constraint
    ranking realizes them. The smallest witness — abstract Lyman's Law —
    is provided by `Cumulativity.lymanProblem`. -/
theorem hg_strictly_contains_ot :
    ∃ (Input Output : Type) (n : ℕ) (P : SystemicProblem Input Output n),
      P.IsHGRealizable ∧ ¬ P.IsOTRealizable :=
  ⟨Fin 3, Bool, 3, Cumulativity.lymanProblem,
    Cumulativity.lyman_isHGRealizable,
    Cumulativity.lyman_not_isOTRealizable⟩

end Core.Constraint
