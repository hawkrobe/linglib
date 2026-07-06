/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.TraceCounting

/-!
# Trace-aware size measures on the contraction-quotient carrier
[marcolli-chomsky-berwick-2025]

The MCB size measures on `Nonplanar (α ⊕ β)`, where `Sum.inl` vertices carry lexical
decorations and `Sum.inr` vertices are trace-marker placeholders left by the Δ^c
coproduct. A trace leaf is a vertex but **not** an accessible term, so the trace-aware
counts subtract the marked-leaf count off the generic measures — and the trace-free
identity `σ = #V` fails on contraction quotients (`σᶜ ≠ #V`, MCB p. 66), witnessed
concretely at the end of the file.

## Main definitions

* `Nonplanar.accCountC`: trace-excluding accessible-term count `α − #traceLeaves`.
* `Forest.alphaC` / `Forest.sigmaC`: the trace-aware workspace measures.

## Main results

* `Nonplanar.accCountC_merge`: External Merge adds two accessible terms in the
  trace-aware count (MCB Lemma 1.6.3, eq. 1.6.5).
-/

namespace RootedTree

namespace Nonplanar

variable {α β : Type*} (a : α) (b : β)

/-- The **trace-excluding accessible-term count** `αᶜ(T) = α(T) − #traceLeaves(T)`:
    a trace leaf is a vertex but not an accessible term (MCB p. 66). Truncated
    subtraction handles the all-trace edge case. -/
def accCountC (t : Nonplanar (α ⊕ β)) : ℕ := t.accCount - t.traceLeafCount

@[simp] theorem accCountC_leaf_inl :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

/-- The truncation case: a bare trace leaf has `α = 0` but one marked leaf. -/
@[simp] theorem accCountC_leaf_inr :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

/-- The marked leaves of a tree are among its non-root vertices whenever the root is
    unmarked. -/
theorem traceLeafCount_le_accCount (t : Nonplanar (α ⊕ β))
    (h : t.traceLeafCount < t.numNodes) : t.traceLeafCount ≤ t.accCount := by
  rw [Nonplanar.accCount_eq_numNodes_sub_one]
  omega

/-- External Merge adds two accessible terms in the trace-aware count: the two
    children's roots become accessible (MCB Lemma 1.6.3, eq. 1.6.5). Needs each child
    to have a lexical vertex (`traceLeafCount < numNodes`), automatic for a real
    syntactic object. -/
theorem accCountC_merge (l r : Nonplanar (α ⊕ β))
    (hl : l.traceLeafCount < l.numNodes) (hr : r.traceLeafCount < r.numNodes) :
    (Nonplanar.node (Sum.inl a) {l, r}).accCountC = l.accCountC + r.accCountC + 2 := by
  have hw := Nonplanar.accCount_node_pair (Sum.inl a) l r
  have htl : (Nonplanar.node (Sum.inl a) {l, r}).traceLeafCount
      = l.traceLeafCount + r.traceLeafCount := by
    rw [traceLeafCount_node_inl]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl := l.traceLeafCount_le_accCount hl
  have hbr := r.traceLeafCount_le_accCount hr
  simp only [accCountC, htl, hw]
  omega

end Nonplanar

/-! ### Trace-aware workspace (forest) measures -/

namespace Forest

variable {α β : Type*}

/-- Trace-excluding accessible terms across a workspace, `αᶜ(F) = Σ αᶜ(Tᵢ)`. -/
def alphaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ :=
  (F.map Nonplanar.accCountC).sum

@[simp] theorem alphaC_zero : alphaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem alphaC_cons (T : Nonplanar (α ⊕ β))
    (F : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (T ::ₘ F) = T.accCountC + alphaC F := by
  simp only [alphaC, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alphaC_singleton (T : Nonplanar (α ⊕ β)) :
    alphaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC := by
  simp only [alphaC, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alphaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (F + G) = alphaC F + alphaC G := by
  simp only [alphaC, Multiset.map_add, Multiset.sum_add]

/-- Trace-aware workspace size `σᶜ(F) = b₀(F) + αᶜ(F)`. Unlike the generic `σ`, this
    is **not** the vertex count for contraction quotients (`σᶜ ≠ #V`, MCB p. 66): a
    trace leaf raises `#V` without raising `σᶜ`. -/
def sigmaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ := b₀ F + alphaC F

@[simp] theorem sigmaC_zero : sigmaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem sigmaC_cons (T : Nonplanar (α ⊕ β))
    (F : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (T ::ₘ F) = T.accCountC + 1 + sigmaC F := by
  simp only [sigmaC, b₀_cons, alphaC_cons]; omega
@[simp] theorem sigmaC_singleton (T : Nonplanar (α ⊕ β)) :
    sigmaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC + 1 := by
  simp only [sigmaC, b₀_singleton, alphaC_singleton]; omega
@[simp] theorem sigmaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (F + G) = sigmaC F + sigmaC G := by
  simp only [sigmaC, b₀_add, alphaC_add]; omega

end Forest

/-! ### The `σᶜ ≠ #V` caveat, concretely

A lexical root over a single trace leaf: `#V = 2` (root + trace leaf) but the trace
leaf contributes no accessible term, so `αᶜ = 0` and `σᶜ = 1`. -/

namespace Nonplanar

variable {α β : Type*}

/-- Minimal contraction-quotient witness for the `σᶜ ≠ #V` caveat. -/
private def traceWitness (a : α) (b : β) : Nonplanar (α ⊕ β) :=
  Nonplanar.mk (.node (Sum.inl a) [.node (Sum.inr b) []])

example (a : α) (b : β) : (traceWitness a b).numNodes = 2 := rfl
example (a : α) (b : β) : (traceWitness a b).traceLeafCount = 1 := rfl
example (a : α) (b : β) : (traceWitness a b).accCountC = 0 := rfl

/-- The trace leaf of `traceWitness` sits at depth 1, so `traceDepthSum = 1`. -/
example (a : α) (b : β) : (traceWitness a b).traceDepthSum = 1 := rfl

/-- A trace leaf two levels down contributes depth 2 to `traceDepthSum`. -/
example (a a' : α) (b : β) :
    Nonplanar.traceDepthSum
      (Nonplanar.mk (.node (Sum.inl a) [.node (Sum.inl a') [.node (Sum.inr b) []]])) = 2 := rfl

/-- Two trace leaves at depths 1 and 2 sum to 3 — the multi-extraction additivity
    `d_v = Σ d_{v_i}` of MCB rule 3. -/
example (a a' : α) (b b' : β) :
    Nonplanar.traceDepthSum
      (Nonplanar.mk (.node (Sum.inl a)
        [.node (Sum.inr b) [], .node (Sum.inl a') [.node (Sum.inr b') []]])) = 3 := rfl

/-- `σᶜ` undercounts `#V` on the contraction quotient: the trace leaf is a vertex but
    not an accessible term. -/
example (a : α) (b : β) :
    Forest.sigmaC ({traceWitness a b} : Multiset (Nonplanar (α ⊕ β))) ≠
      (({traceWitness a b} : Multiset (Nonplanar (α ⊕ β))).map
        Nonplanar.numNodes).sum := by
  simp only [Forest.sigmaC, Forest.b₀_singleton, Forest.alphaC_singleton,
    Multiset.map_singleton, Multiset.sum_singleton,
    show (traceWitness a b).accCountC = 0 from rfl,
    show (traceWitness a b).numNodes = 2 from rfl]
  decide

end Nonplanar

end RootedTree
