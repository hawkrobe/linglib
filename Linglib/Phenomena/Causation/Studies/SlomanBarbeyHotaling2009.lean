import Linglib.Core.Causal.V2.SEM.Bool
import Linglib.Core.Causal.V2.SEM.Counterfactual
import Mathlib.Data.Finset.Card

/-!
# Sloman, Barbey & Hotaling (2009): A Causal Model Theory of *cause*/*enable*/*prevent*
@cite{sloman-barbey-hotaling-2009}

Cognitive Science 33(1): 21–50.

The foundational deterministic-binary statement of the **structural-equation
theory of causal verbs**: *cause*, *enable*, and *prevent* denote distinct
structural forms (Figure 4, eqs 2, 3, 4a–c). Subsequent literature has
generalized this to graded/probabilistic causation
(@cite{cao-white-lassiter-2025}), counterfactual simulation
(@cite{beller-gerstenberg-2025}), and refined necessity definitions
(@cite{nadathur-2024}). This file formalizes SBH 2009's specific
*structural* claims as the historical foundation.

## What is formalized

1. **The structural predicates** `Sloman.causeSem` and `Sloman.enableSem`.
   These are paper-specific predicates over the SEM's *graph shape*
   (parent-set cardinality), not over `develop` — purely structural,
   computable, decidable.

2. **Experiment 4 (Labeling)**: SBH's most testable production claim:
   1-link causal models are labeled "cause"; 2-link models (with an
   accessory) are labeled "enable". Theorems
   `oneLink_excludes_enable` and `twoLink_implies_enable` formalize
   the structural distinction.

3. **Distinctness theorem** witnessing that the SBH-style enable
   predicate is structurally distinct from the simple cause predicate
   (the disagreement with force-dynamic accounts that collapse them
   becomes theorem-provable).

## What is NOT formalized

- **Multi-premise inference (§4–§9)**: SBH's substitution composition
  has been superseded by counterfactual simulation
  (@cite{beller-gerstenberg-2025}).
- **Experiments 1–3 (certainty inequalities)**: graded SUF / Bayesian
  models predict these directly; deterministic SBH has no graded
  analogue (see @cite{cao-white-lassiter-2025}).
- **Truth-conditional `enableSem` over `develop`**: the structural
  predicate is the contemporary view; the develop-based version (with
  required-accessory truth conditions) reduces to a special case.

## Mathlib pattern

This study file demonstrates the V2 migration pattern: paper-specific
predicates live in the study file (namespaced `Sloman`); they reference
V2's `BoolSEM` / `CausalGraph` directly without going through legacy
hubs. Structural predicates avoid the `develop` noncomputable cascade.
-/

namespace SlomanBarbeyHotaling2009

open Core.Causal.V2 (BoolSEM CausalGraph)

variable {V : Type*}

-- ════════════════════════════════════════════════════
-- § Sloman's structural predicates (paper-specific)
-- ════════════════════════════════════════════════════

namespace Sloman

/-- **SBH eq (2): `B := A`** — Sloman's structural cause predicate.
    The effect has exactly one parent (the cause). -/
def causeSem (M : BoolSEM V) (cause effect : V) : Prop :=
  M.graph.parents effect = {cause}

instance [DecidableEq V] (M : BoolSEM V) (cause effect : V) :
    Decidable (causeSem M cause effect) :=
  inferInstanceAs (Decidable (_ = _))

/-- **SBH eq (3): `B := A ∧ X`** — Sloman's structural enable predicate.
    The effect has at least two parents, including the cause. The
    "accessory variable" (Sloman's X) is the second-or-later parent. -/
def enableSem (M : BoolSEM V) (cause effect : V) : Prop :=
  cause ∈ M.graph.parents effect ∧ 2 ≤ (M.graph.parents effect).card

instance [DecidableEq V] (M : BoolSEM V) (cause effect : V) :
    Decidable (enableSem M cause effect) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Sloman

-- ════════════════════════════════════════════════════
-- § Experiment 4 (Labeling): structural theorems
-- ════════════════════════════════════════════════════

/-- **Exp 4 / 1-link**: 1-link causal models satisfy `causeSem` and
    *exclude* `enableSem`. Maps SBH's empirical finding "participants
    label 1-link models as 'cause'" to a definitional fact about the
    structural form. -/
theorem oneLink_causeSem_excludes_enableSem [DecidableEq V]
    {M : BoolSEM V} {cause effect : V}
    (h : M.graph.parents effect = {cause}) :
    Sloman.causeSem M cause effect ∧ ¬ Sloman.enableSem M cause effect := by
  refine ⟨h, ?_⟩
  intro ⟨_, hCard⟩
  rw [h] at hCard
  simp at hCard

/-- **Exp 4 / 2-link**: 2-link causal models (with a distinct accessory)
    satisfy `enableSem` and *exclude* `causeSem`. Maps SBH's empirical
    finding "participants label 2-link models as 'enable'" to a
    definitional fact about the structural form. -/
theorem twoLink_enableSem_excludes_causeSem [DecidableEq V]
    {M : BoolSEM V} {cause accessory effect : V}
    (h_ne : cause ≠ accessory)
    (h : M.graph.parents effect = {cause, accessory}) :
    Sloman.enableSem M cause effect ∧ ¬ Sloman.causeSem M cause effect := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h]; simp
  · rw [h, Finset.card_pair h_ne]
  · intro hCause
    -- causeSem says parents = {cause}; we have parents = {cause, accessory} with accessory ≠ cause
    unfold Sloman.causeSem at hCause
    rw [h] at hCause
    have : accessory ∈ ({cause, accessory} : Finset V) := by simp
    rw [hCause] at this
    simp at this
    exact h_ne this.symm

-- ════════════════════════════════════════════════════
-- § Distinctness theorem
-- ════════════════════════════════════════════════════

/-- **`causeSem` and `enableSem` are mutually exclusive**.

    No `BoolSEM` simultaneously satisfies both predicates for the same
    cause/effect pair. The structural disagreement Sloman et al. argue
    against force-dynamic accounts (which collapse cause/enable
    truth-conditionally) becomes a theorem.

    Witness: the parent-set cardinality is 1 for `causeSem` but ≥ 2
    for `enableSem`. -/
theorem causeSem_excludes_enableSem [DecidableEq V] (M : BoolSEM V) (cause effect : V) :
    ¬ (Sloman.causeSem M cause effect ∧ Sloman.enableSem M cause effect) := by
  intro ⟨hCause, _, hCard⟩
  rw [hCause] at hCard
  simp at hCard

end SlomanBarbeyHotaling2009
