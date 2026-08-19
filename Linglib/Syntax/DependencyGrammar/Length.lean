/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dependency length

The core quantity behind [futrell-gibson-2020]'s claim that natural
languages minimise total dependency length beyond what independent
constraints predict, together with [behaghel-1932]'s "Oberstes Gesetz"
threshold. Arc length is `Nat.dist` on positions; the total is a
`Finset` sum, so relabeling arguments are mathlib sum-reindexings.

`Graph.relabel` transports a graph along a position permutation — the
formal core of [futrell-gibson-2020]'s random-reordering baselines — and
`Graph.mirror` is relabeling along `Fin.rev`, with `totalLength_mirror`
recording that the head-final mirror of a graph has the same total
dependency length.
-/

namespace DependencyGrammar

variable {n : ℕ}

/-- Total dependency length: the sum of `Nat.dist` over all arcs — the
    quantity dependency-length minimisation is about. -/
def Graph.totalLength (g : Graph n) : Nat :=
  ∑ v : Fin n, ∑ w ∈ g.children v, Nat.dist v w

/-- Total dependency length reads only the arc structure, never the
    tokens. -/
theorem Graph.totalLength_words (g : Graph n) (words' : Fin n → Morphology.Word) :
    Graph.totalLength { g with words := words' } = g.totalLength := rfl

/-- [behaghel-1932]'s Oberstes Gesetz: every arc has length at most
    `threshold`. -/
def OberstesGesetz (g : Graph n) (threshold : Nat) : Prop :=
  ∀ ⦃v w⦄, g.Adj v w → Nat.dist v w ≤ threshold

instance (g : Graph n) (k : Nat) : Decidable (OberstesGesetz g k) :=
  inferInstanceAs (Decidable (∀ _, _))

/-! ### Relabeling: same structure, different linearization -/

/-- Transport a graph along a position permutation: arcs, tokens, and root
    move together, so the labeled structure is unchanged and only the
    linearization varies. -/
def Graph.relabel (g : Graph n) (σ : Equiv.Perm (Fin n)) : Graph n :=
  { words := g.words ∘ σ.symm
    label := λ v w => g.label (σ.symm v) (σ.symm w)
    root := σ g.root }

@[simp] theorem Graph.relabel_adj (g : Graph n) (σ : Equiv.Perm (Fin n))
    (v w : Fin n) : (g.relabel σ).Adj v w ↔ g.Adj (σ.symm v) (σ.symm w) :=
  Iff.rfl

/-- The head-final mirror: relabel along position reversal. -/
def Graph.mirror (g : Graph n) : Graph n := g.relabel Fin.revPerm

/-- Relabeling along an isometry of the positions preserves total
    dependency length. -/
theorem Graph.totalLength_relabel (g : Graph n) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ v w : Fin n, Nat.dist (σ v) (σ w) = Nat.dist v w) :
    (g.relabel σ).totalLength = g.totalLength := by
  unfold totalLength
  simp only [Graph.children, Finset.sum_filter]
  refine Fintype.sum_equiv σ.symm _ _ (λ v => ?_)
  refine Fintype.sum_equiv σ.symm _ _ (λ w => ?_)
  simp only [relabel_adj]
  by_cases h : g.Adj (σ.symm v) (σ.symm w) <;>
    simp [h, ← hσ (σ.symm v) (σ.symm w)]

/-- Position reversal preserves `Nat.dist`. -/
theorem _root_.Fin.dist_rev_rev (v w : Fin n) :
    Nat.dist v.rev w.rev = Nat.dist v w := by
  have hv := v.isLt
  have hw := w.isLt
  simp only [Nat.dist, Fin.val_rev]
  omega

/-- The mirror image of a graph has the same total dependency length —
    the head-final preference is the exact mirror of the head-initial one
    ([futrell-gibson-2020], examples (7)–(8)). -/
theorem Graph.totalLength_mirror (g : Graph n) :
    g.mirror.totalLength = g.totalLength :=
  g.totalLength_relabel _ (λ v w => Fin.dist_rev_rev v w)

end DependencyGrammar
