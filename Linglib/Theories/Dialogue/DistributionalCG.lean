import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Linglib.Core.Semantics.CommonGround
import Linglib.Core.Discourse.Commitment
import Linglib.Theories.Dialogue.CommitmentSpace

/-!
# Distributional Common Ground

@cite{anderson-2021}

A non-negative real-valued weight function over worlds, refining
@cite{stalnaker-2002}'s sharp set-membership context set with graded
plausibility. The probabilistic counterpart of `Core.CommonGround.CG W`.

## Substrate role

This file hosts:
- The `DistributionalCG W` structure with the `weight_nonneg`
  invariant.
- The `HasContextSet (DistributionalCG W) W` instance projecting to
  the positive-weight subset.
- The `HasSupport ℝ` instance enabling the polymorphic
  `CommitmentSpace W G` substrate to be hosted at `G = ℝ`.
- The `toCommitmentSpace` bridge from `DistributionalCG W` to
  `Dialogue.Krifka.CommitmentSpace W ℝ`, plus the support-equivalence
  theorem.

The Anderson 2021 study (`Phenomena/Dialogue/Studies/Anderson2021.lean`)
imports this substrate and adds the conversation-update + RSA-bridge
content on top.

## Why no `[CommitmentGrade ℝ]`

`HasSupport ℝ` is provided (`support g := 0 < g`); `CommitmentGrade ℝ`
is NOT, because the involution law
`support (complement g) ↔ ¬ support g` fails on unrestricted reals
(e.g., `0 < 1 - 1/2 = 1/2` AND `0 < 1/2`). A future `CommitmentGrade
NNReal` or `CommitmentGrade Probability` instance with proper laws
over `[0,1]` would unlock graded bipolar questions for probabilistic
frameworks.
-/

namespace Dialogue

open Core.CommonGround (ContextSet HasContextSet)
open Core.Discourse (DiscourseRole)
open Core.Discourse.Commitment (HasSupport IndexedWeightedCommitment CommitmentForce)

-- ════════════════════════════════════════════════════
-- § 1. DistributionalCG
-- ════════════════════════════════════════════════════

/-- A distributional common ground: a non-negative weight function
    over worlds (@cite{anderson-2021}). The probabilistic
    counterpart of @cite{stalnaker-2002}'s context set — instead of
    a sharp membership predicate (`W → Prop`), the CG assigns graded
    plausibility (`W → ℝ`). -/
structure DistributionalCG (W : Type*) where
  weight : W → ℝ
  weight_nonneg : ∀ w, 0 ≤ weight w

namespace DistributionalCG

variable {W : Type*}

/-- Uniform distributional CG: all worlds equally plausible (empty CG). -/
noncomputable def uniform : DistributionalCG W where
  weight _ := 1
  weight_nonneg _ := le_of_lt one_pos

/-- Bridge to classical context set: a world is "in the context" iff
    its weight is positive. Recovers @cite{stalnaker-2002}'s
    set-membership view from the distributional representation. -/
def toContextSet (cg : DistributionalCG W) : ContextSet W :=
  λ w => 0 < cg.weight w

/-- Uniform distributional CG maps to the trivial context set. -/
theorem uniform_toContextSet :
    (uniform : DistributionalCG W).toContextSet = ContextSet.trivial := by
  funext w
  simp only [toContextSet, uniform, ContextSet.trivial]
  exact propext ⟨λ _ => True.intro, λ _ => one_pos⟩

/-- A world with zero weight is excluded from the classical context set. -/
theorem zero_weight_excluded (cg : DistributionalCG W) (w : W)
    (h : cg.weight w = 0) : ¬cg.toContextSet w := by
  intro hpos
  simp only [toContextSet] at hpos
  linarith

end DistributionalCG

/-- A distributional CG projects to a context set: worlds with
    positive weight. -/
instance {W : Type*} : HasContextSet (DistributionalCG W) W where
  toContextSet := DistributionalCG.toContextSet

-- ════════════════════════════════════════════════════
-- § 2. HasSupport ℝ
-- ════════════════════════════════════════════════════

/-- `[HasSupport ℝ]` instance for distributional CGs.
    `support g := 0 < g` matches Anderson's "world has positive weight
    iff in CG" projection (cf. `DistributionalCG.toContextSet`).

    Provides ONLY `HasSupport ℝ`, NOT `CommitmentGrade ℝ`: the latter
    would require the involution law on `complement`, which fails on
    unrestricted reals. See module docstring. -/
instance : HasSupport ℝ where
  support g := 0 < g

-- ════════════════════════════════════════════════════
-- § 3. Bridge to polymorphic CommitmentSpace W ℝ
-- ════════════════════════════════════════════════════

/-- Bridge: a distributional CG embeds into a commitment space at
    `G = ℝ`. The speaker's distributional weights become a single
    `commit speaker .doxastic weight` entry in the root.

    Note: the `weight_nonneg` constraint on `DistributionalCG` is NOT
    propagated into `CommitmentSpace W ℝ` — the substrate doesn't
    enforce non-negativity. The bridge is sound in the
    `support`-projection direction but loses Anderson's structural
    invariant. -/
noncomputable def DistributionalCG.toCommitmentSpace {W : Type*}
    (cg : DistributionalCG W) :
    Dialogue.Krifka.CommitmentSpace W ℝ where
  root := [IndexedWeightedCommitment.commit .speaker .doxastic cg.weight]
  continuations := []

/-- Bridge theorem: the support of a distributional CG equals the
    `toContextSet` projection of the bridged commitment space.
    Demonstrates that the polymorphic substrate at `G = ℝ`
    faithfully captures Anderson's distributional CG when projected
    to its support. -/
theorem DistributionalCG.toCommitmentSpace_support {W : Type*}
    (cg : DistributionalCG W) (w : W) :
    (cg.toCommitmentSpace).toContextSet w ↔ cg.toContextSet w := by
  unfold toCommitmentSpace
  simp only [Dialogue.Krifka.CommitmentSpace.toContextSet, List.mem_singleton]
  constructor
  · intro h
    have := h _ rfl
    exact this
  · intro h _ heq
    rw [heq]
    exact h

end Dialogue
