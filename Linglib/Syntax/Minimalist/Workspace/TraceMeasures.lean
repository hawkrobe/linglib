/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Conservation

open RoseTree RoseTree.Nonplanar

/-!
# MCB's letter vocabulary for the workspace measures
[marcolli-chomsky-berwick-2025]

MCB's letter names over the generic measures of `Core/Data/RoseTree/Count.lean`
and the trace measures of `Core/Combinatorics/RootedTree/Conservation.lean`:
`accCount` for `numEdges`; `b₀`, `alpha`, `sigma` for the forest measures; the
`p`-discounted variants (`accCountP`, `alphaP`, `sigmaP`); and their
instantiations at the trace-marker color class `Sum.isRight` (`accCountC`,
`alphaC`, `sigmaC`).

Domain vocabulary over Core substrate; consumed by the workspace conservation
laws (`Workspace/Conservation.lean`) and the Merge economy files.
-/

namespace RoseTree.Nonplanar

variable {α β : Type*} (p : α → Prop) [DecidablePred p]

/-! ### MCB's letter vocabulary for the generic measures -/

/-- MCB's accessible-term count: the edge count (every non-root vertex is an
    accessible term). -/
def accCount : Nonplanar α → ℕ := numEdges

@[simp] theorem accCount_leaf (a : α) : (leaf a : Nonplanar α).accCount = 0 :=
  numEdges_leaf a

theorem accCount_eq_numNodes_sub_one (t : Nonplanar α) :
    t.accCount = t.numNodes - 1 := rfl

theorem accCount_add_one (t : Nonplanar α) : t.accCount + 1 = t.numNodes :=
  numEdges_add_one t

theorem accCount_node (a : α) (F : Multiset (Nonplanar α)) :
    (node a F).accCount = (F.map numNodes).sum :=
  numEdges_node a F

theorem accCount_node_pair (a : α) (l r : Nonplanar α) :
    (node a {l, r}).accCount = l.accCount + r.accCount + 2 :=
  numEdges_node_pair a l r

/-- Accessible terms discounting the `p`-leaves. Truncated subtraction covers the
    single-`p`-leaf tree, whose root is its one leaf. -/
def accCountP (t : Nonplanar α) : ℕ :=
  t.numEdges - t.leafCountP p

/-- Adjoining a root (not counted by `p`) above a pair adds two discounted
    accessible terms. -/
theorem accCountP_node_pair (a : α)
    (l r : Nonplanar α) (hpa : ¬p a)
    (hl : l.leafCountP p < l.numNodes) (hr : r.leafCountP p < r.numNodes) :
    (Nonplanar.node a {l, r}).accCountP p = l.accCountP p + r.accCountP p + 2 := by
  have hw := numEdges_node_pair a l r
  have htl : (Nonplanar.node a {l, r}).leafCountP p = l.leafCountP p + r.leafCountP p := by
    rw [leafCountP_node_of_not p a _ hpa]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton]
  have hbl := leafCountP_le_numEdges p l hl
  have hbr := leafCountP_le_numEdges p r hr
  simp only [accCountP, htl, hw]
  omega

/-- The trace-excluding accessible-term count `αᶜ(T) = α(T) − #traceLeaves(T)`. -/
def accCountC : Nonplanar (α ⊕ β) → ℕ := accCountP (·.isRight = true)

@[simp] theorem accCountC_leaf_inl (a : α) :
    (leaf (Sum.inl a) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

@[simp] theorem accCountC_leaf_inr (b : β) :
    (leaf (Sum.inr b) : Nonplanar (α ⊕ β)).accCountC = 0 := rfl

theorem accCountC_eq (t : Nonplanar (α ⊕ β)) :
    t.accCountC = t.accCount - t.traceLeafCount := rfl

theorem traceLeafCount_le_accCount (t : Nonplanar (α ⊕ β))
    (h : t.traceLeafCount < t.numNodes) : t.traceLeafCount ≤ t.accCount :=
  leafCountP_le_numEdges _ t h

/-- External Merge adds two accessible terms in the trace-aware count
    (MCB Lemma 1.6.3, eq. 1.6.5). -/
theorem accCountC_merge (a : α) (l r : Nonplanar (α ⊕ β))
    (hl : l.traceLeafCount < l.numNodes) (hr : r.traceLeafCount < r.numNodes) :
    (Nonplanar.node (Sum.inl a) {l, r}).accCountC = l.accCountC + r.accCountC + 2 :=
  accCountP_node_pair _ _ l r (by simp) hl hr

end RoseTree.Nonplanar

namespace Forest

variable {α β : Type*} (p : α → Prop) [DecidablePred p]

/-! ### MCB's letter vocabulary for the forest measures -/

/-- The number of component trees of a workspace (MCB's zeroth Betti number). -/
def b₀ : Multiset (Nonplanar α) → ℕ := Multiset.card

@[simp] theorem b₀_zero : b₀ (0 : Multiset (Nonplanar α)) = 0 := Multiset.card_zero
@[simp] theorem b₀_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    b₀ (T ::ₘ F) = b₀ F + 1 := Multiset.card_cons T F
@[simp] theorem b₀_singleton (T : Nonplanar α) :
    b₀ ({T} : Multiset (Nonplanar α)) = 1 := Multiset.card_singleton T
@[simp] theorem b₀_add (F G : Multiset (Nonplanar α)) :
    b₀ (F + G) = b₀ F + b₀ G := Multiset.card_add F G

/-- MCB's workspace measure `α`: the total accessible-term (edge) count. -/
def alpha : Multiset (Nonplanar α) → ℕ := numEdges

@[simp] theorem alpha_zero : alpha (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem alpha_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    alpha (T ::ₘ F) = T.accCount + alpha F := numEdges_cons T F
@[simp] theorem alpha_singleton (T : Nonplanar α) :
    alpha ({T} : Multiset (Nonplanar α)) = T.accCount := numEdges_singleton T
@[simp] theorem alpha_add (F G : Multiset (Nonplanar α)) :
    alpha (F + G) = alpha F + alpha G := numEdges_add F G

/-- MCB's workspace size `σ = b₀ + α`: the total vertex count
    (`sigma_eq_sum_numNodes`). -/
def sigma (F : Multiset (Nonplanar α)) : ℕ := b₀ F + alpha F

@[simp] theorem sigma_zero : sigma (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem sigma_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    sigma (T ::ₘ F) = T.numNodes + sigma F := by
  simp only [sigma, b₀_cons, alpha_cons, ← Nonplanar.accCount_add_one]
  omega
@[simp] theorem sigma_singleton (T : Nonplanar α) :
    sigma ({T} : Multiset (Nonplanar α)) = T.numNodes := by
  simp only [sigma, b₀_singleton, alpha_singleton, ← Nonplanar.accCount_add_one]
  omega
@[simp] theorem sigma_add (F G : Multiset (Nonplanar α)) :
    sigma (F + G) = sigma F + sigma G := by
  simp only [sigma, b₀_add, alpha_add]; omega

/-- `sigma` is the total vertex count: the forest case of `#V = b₀ + #E`. -/
theorem sigma_eq_sum_numNodes (F : Multiset (Nonplanar α)) :
    sigma F = (F.map Nonplanar.numNodes).sum :=
  (numNodes_eq_card_add_numEdges F).symm

/-- Discounted accessible terms across a workspace. -/
def alphaP (F : Multiset (Nonplanar α)) : ℕ :=
  (F.map (Nonplanar.accCountP p)).sum

@[simp] theorem alphaP_zero :
    alphaP p (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem alphaP_cons (T : Nonplanar α)
    (F : Multiset (Nonplanar α)) : alphaP p (T ::ₘ F) = T.accCountP p + alphaP p F := by
  simp only [alphaP, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alphaP_singleton (T : Nonplanar α) :
    alphaP p ({T} : Multiset (Nonplanar α)) = T.accCountP p := by
  simp only [alphaP, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alphaP_add
    (F G : Multiset (Nonplanar α)) : alphaP p (F + G) = alphaP p F + alphaP p G := by
  simp only [alphaP, Multiset.map_add, Multiset.sum_add]

/-- Discounted workspace size: components plus discounted accessible terms. Unlike
    `sigma`, this is not the vertex count when counted leaves exist. -/
def sigmaP (F : Multiset (Nonplanar α)) : ℕ :=
  b₀ F + alphaP p F

@[simp] theorem sigmaP_zero :
    sigmaP p (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem sigmaP_cons (T : Nonplanar α)
    (F : Multiset (Nonplanar α)) : sigmaP p (T ::ₘ F) = T.accCountP p + 1 + sigmaP p F := by
  simp only [sigmaP, b₀_cons, alphaP_cons]; omega
@[simp] theorem sigmaP_singleton (T : Nonplanar α) :
    sigmaP p ({T} : Multiset (Nonplanar α)) = T.accCountP p + 1 := by
  simp only [sigmaP, b₀_singleton, alphaP_singleton]; omega
@[simp] theorem sigmaP_add
    (F G : Multiset (Nonplanar α)) : sigmaP p (F + G) = sigmaP p F + sigmaP p G := by
  simp only [sigmaP, b₀_add, alphaP_add]; omega

/-- Trace-excluding accessible terms across a workspace, `αᶜ(F) = Σ αᶜ(Tᵢ)`. -/
def alphaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ := alphaP (·.isRight = true) F

theorem alphaC_eq (F : Multiset (Nonplanar (α ⊕ β))) :
    alphaC F = (F.map Nonplanar.accCountC).sum := rfl

@[simp] theorem alphaC_zero : alphaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem alphaC_cons (T : Nonplanar (α ⊕ β)) (F : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (T ::ₘ F) = T.accCountC + alphaC F :=
  alphaP_cons _ T F
@[simp] theorem alphaC_singleton (T : Nonplanar (α ⊕ β)) :
    alphaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC :=
  alphaP_singleton _ T
@[simp] theorem alphaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    alphaC (F + G) = alphaC F + alphaC G :=
  alphaP_add _ F G

/-- Trace-aware workspace size `σᶜ(F) = b₀(F) + αᶜ(F)`; not the vertex count for
    contraction quotients (`σᶜ ≠ #V`, MCB p. 66). -/
def sigmaC (F : Multiset (Nonplanar (α ⊕ β))) : ℕ := sigmaP (·.isRight = true) F

theorem sigmaC_eq (F : Multiset (Nonplanar (α ⊕ β))) : sigmaC F = b₀ F + alphaC F := rfl

@[simp] theorem sigmaC_zero : sigmaC (0 : Multiset (Nonplanar (α ⊕ β))) = 0 := rfl
@[simp] theorem sigmaC_cons (T : Nonplanar (α ⊕ β)) (F : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (T ::ₘ F) = T.accCountC + 1 + sigmaC F :=
  sigmaP_cons _ T F
@[simp] theorem sigmaC_singleton (T : Nonplanar (α ⊕ β)) :
    sigmaC ({T} : Multiset (Nonplanar (α ⊕ β))) = T.accCountC + 1 :=
  sigmaP_singleton _ T
@[simp] theorem sigmaC_add (F G : Multiset (Nonplanar (α ⊕ β))) :
    sigmaC (F + G) = sigmaC F + sigmaC G :=
  sigmaP_add _ F G

end Forest

