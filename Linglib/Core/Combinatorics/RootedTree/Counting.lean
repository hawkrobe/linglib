import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Size counting on nonplanar rooted trees and workspaces

The MCB size measures for syntactic-object combinatorics
([marcolli-chomsky-berwick-2025]), on the canonical `Nonplanar` carrier.
A *workspace* (forest) is a `Multiset (Nonplanar α)`; MCB foregrounds the
measures `b₀`/`α`/`σ` on workspaces (eq. 1.6.1), with a single tree as the
one-component case. The tree-level `accCount` is the recursive primitive that
`α` folds over.

These build directly on the lifted `Nonplanar.numNodes` (= MCB's `#V`); the
legacy planar `Decorated`/`AdmissibleCut` substrate provided the same measures
over the unfaithful planar-binary `TraceTree`.

## Main definitions

* `Nonplanar.accCount` — accessible-term count `α(T) = #V(T) - 1` (tree primitive).
* `Forest.b₀` — number of component trees (Betti number).
* `Forest.alpha` — total accessible terms `α(F) = Σ α(Tᵢ)`.
* `Forest.sigma` — workspace size `σ(F) = b₀(F) + α(F)`.

## Main results

* `Nonplanar.accCount_merge` — external Merge adds two accessible terms (eq. 1.6.5).
* `Forest.sigma_eq_sum_numNodes` — `σ(F) = #V(F)` (eq. 1.2.6); unconditional on the
  generic carrier (no trace leaves). The contraction-quotient exception
  (`σᶜ ≠ #V`, MCB p.66) lives in `TraceCounting`.

## TODO

* Trace-aware `accCountC`/`alphaC`/`sigmaC` and the complexity grading `#L`
  on lexical leaves (`leafCountSO0`) over `Nonplanar (α ⊕ β)` (`TraceCounting.lean`);
  builds on the carrier `Nonplanar.numLeaves`.
* The admissible-cut layer (`Fintype`-enumerable cuts + extraction identities 1.6.7/1.6.8).
-/

namespace RootedTree

namespace Nonplanar

variable {α : Type*}

/-- The **accessible-term count** `α(T) = #V(T) - 1`: every vertex of a
syntactic object except its root (MCB eq. 1.2.5). -/
def accCount (t : Nonplanar α) : ℕ := t.numNodes - 1

@[simp] theorem accCount_leaf (a : α) : (leaf a : Nonplanar α).accCount = 0 := by
  simp [accCount]

theorem accCount_eq_numNodes_sub_one (t : Nonplanar α) : t.accCount = t.numNodes - 1 := rfl

/-- External Merge of two syntactic objects adds exactly two accessible terms
(MCB Lemma 1.6.3, eq. 1.6.5). -/
theorem accCount_merge (a : α) (l r : Nonplanar α) :
    (node a {l, r}).accCount = l.accCount + r.accCount + 2 := by
  have hl := l.numNodes_pos
  have hr := r.numNodes_pos
  simp only [accCount, numNodes_node, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
  omega

end Nonplanar

/-! ## Workspace (forest) measures

A workspace is a `Multiset (Nonplanar α)`. MCB's primitive workspace measures
are `b₀` (component count) and `α` (accessible terms); `σ` is derived. -/

namespace Forest

variable {α : Type*}

/-- The number of component trees in a workspace — MCB's `b₀`, the Betti
number `b₀(F) = #I` (eq. 1.6.1). -/
def b₀ (F : Multiset (Nonplanar α)) : ℕ := Multiset.card F

@[simp] theorem b₀_zero : b₀ (0 : Multiset (Nonplanar α)) = 0 := Multiset.card_zero
@[simp] theorem b₀_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    b₀ (T ::ₘ F) = b₀ F + 1 := Multiset.card_cons T F
@[simp] theorem b₀_singleton (T : Nonplanar α) :
    b₀ ({T} : Multiset (Nonplanar α)) = 1 := Multiset.card_singleton T
@[simp] theorem b₀_add (F G : Multiset (Nonplanar α)) :
    b₀ (F + G) = b₀ F + b₀ G := Multiset.card_add F G

/-- Total accessible terms across the workspace, `α(F) = Σ α(Tᵢ)` (eq. 1.2.4). -/
def alpha (F : Multiset (Nonplanar α)) : ℕ := (F.map Nonplanar.accCount).sum

@[simp] theorem alpha_zero : alpha (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem alpha_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    alpha (T ::ₘ F) = T.accCount + alpha F := by
  simp only [alpha, Multiset.map_cons, Multiset.sum_cons]
@[simp] theorem alpha_singleton (T : Nonplanar α) :
    alpha ({T} : Multiset (Nonplanar α)) = T.accCount := by
  simp only [alpha, Multiset.map_singleton, Multiset.sum_singleton]
@[simp] theorem alpha_add (F G : Multiset (Nonplanar α)) :
    alpha (F + G) = alpha F + alpha G := by
  simp only [alpha, Multiset.map_add, Multiset.sum_add]

/-- Workspace size `σ(F) = b₀(F) + α(F)` (MCB eq. 1.6.1): components plus
accessible terms. For trace-free workspaces this is the total vertex count
(`sigma_eq_sum_numNodes`); it is *not* the vertex count for contraction quotients
(a trace leaf is a vertex but not an accessible term, MCB p.66). -/
def sigma (F : Multiset (Nonplanar α)) : ℕ := b₀ F + alpha F

@[simp] theorem sigma_zero : sigma (0 : Multiset (Nonplanar α)) = 0 := rfl
@[simp] theorem sigma_cons (T : Nonplanar α) (F : Multiset (Nonplanar α)) :
    sigma (T ::ₘ F) = T.numNodes + sigma F := by
  have hT := T.numNodes_pos
  simp only [sigma, b₀_cons, alpha_cons, Nonplanar.accCount_eq_numNodes_sub_one]
  omega
@[simp] theorem sigma_add (F G : Multiset (Nonplanar α)) :
    sigma (F + G) = sigma F + sigma G := by
  simp only [sigma, b₀_add, alpha_add]; omega

/-- `σ(F) = #V(F)`, the total vertex count (MCB eq. 1.2.6). Unconditional on the
generic carrier, where every `accCount` is `numNodes − 1`; the contraction-quotient
exception lives in `TraceCounting`. -/
theorem sigma_eq_sum_numNodes (F : Multiset (Nonplanar α)) :
    sigma F = (F.map Nonplanar.numNodes).sum := by
  induction F using Multiset.induction with
  | empty => rfl
  | cons T F ih => rw [sigma_cons, ih, Multiset.map_cons, Multiset.sum_cons]

end Forest

end RootedTree
