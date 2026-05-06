import Linglib.Core.Combinatorics.RootedTree.Decorated

/-!
# Forest size measures (b₀, α, σ)
@cite{marcolli-chomsky-berwick-2025} §1.2 (Definition 1.2.2) + §1.6.1

Three counting functions on a `TraceForest α β`:

- **`b₀(F)` — number of components**: the cardinality of `F` as a multiset.
  The "Betti number" of the forest in topological notation.
- **`α(F)` — accessible terms**: per MCB Def 1.2.2 (the "more precise
  discussion" of the §1.1 prose-definition on book p. 21: "the accessible
  terms of a syntactic object T are the subtrees T_v, with v a non-root
  vertex of T"), `α(F) = Σ_T #Acc(T)`. For a `TraceTree`, every vertex
  is the root of some subtree, so `#Acc(T) = #V(T) - 1 = T.size - 1`.
- **`σ(F)` — total of components plus accessible terms** (MCB §1.6.1):
  `σ(F) = b₀(F) + α(F)`.

Lemma 1.6.3 (book §1.6.2) supplies counting identities for these under
`merge` (the `.node` constructor) and under cut-quotients; this file
proves the merge-side identities (`accCount_node`, `sigma_node`),
matching MCB eq. 1.6.5 / 1.6.6. The cut-quotient identities (eq. 1.6.7-
1.6.10) need `AdmissibleCut` substrate and live elsewhere.

Generic over leaf alphabet `α` and trace alphabet `β`. Pure combinatorial
substrate — no Hopf algebra dependency.
-/

namespace ConnesKreimer

variable {α β : Type*}

/-- Number of accessible terms of a tree: `#V(T) - 1` per MCB Def 1.2.2,
    where accessible terms are subtrees `T_v` with `v` a non-root vertex
    of `T` (book p. 21). -/
def TraceTree.accCount : TraceTree α β → Nat := fun T => T.size - 1

@[simp] theorem TraceTree.accCount_leaf (a : α) :
    (TraceTree.leaf a : TraceTree α β).accCount = 0 := rfl

@[simp] theorem TraceTree.accCount_trace (b : β) :
    (TraceTree.trace b : TraceTree α β).accCount = 0 := rfl

@[simp] theorem TraceTree.accCount_node (l r : TraceTree α β) :
    (TraceTree.node l r).accCount = l.size + r.size := by
  show (1 + l.size + r.size) - 1 = l.size + r.size
  omega

/-- **MCB Lemma 1.6.3 eq. 1.6.5** (book p. 65): `α(M(T_v, T_w)) = α(T_v) +
    α(T_w) + 2`. Trivially follows from `accCount_node` plus `size_pos`. -/
theorem TraceTree.accCount_merge (T_v T_w : TraceTree α β) :
    (TraceTree.node T_v T_w).accCount = T_v.accCount + T_w.accCount + 2 := by
  rw [TraceTree.accCount_node]
  show T_v.size + T_w.size = T_v.size - 1 + (T_w.size - 1) + 2
  have := T_v.size_pos
  have := T_w.size_pos
  omega

/-- `b₀(F)` — the number of components of the forest `F`. M-C-B
    Definition 1.2.2 (Trees and Forests, §1.2). -/
def TraceForest.b₀ (F : TraceForest α β) : Nat := Multiset.card F

@[simp] theorem TraceForest.b₀_zero :
    TraceForest.b₀ (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.b₀_singleton (T : TraceTree α β) :
    TraceForest.b₀ ({T} : TraceForest α β) = 1 := by
  unfold b₀; exact Multiset.card_singleton _

@[simp] theorem TraceForest.b₀_cons (T : TraceTree α β) (F : TraceForest α β) :
    TraceForest.b₀ (T ::ₘ F) = 1 + F.b₀ := by
  show Multiset.card (T ::ₘ F) = 1 + Multiset.card F
  rw [Multiset.card_cons]; omega

@[simp] theorem TraceForest.b₀_add (F G : TraceForest α β) :
    TraceForest.b₀ (F + G) = F.b₀ + G.b₀ :=
  Multiset.card_add F G

/-- `α(F)` — total number of accessible terms across all components of `F`.
    M-C-B Definition 1.2.2 / §1.6.1 (eq. 1.6.1). -/
def TraceForest.alpha (F : TraceForest α β) : Nat :=
  Multiset.sum (Multiset.map TraceTree.accCount F)

@[simp] theorem TraceForest.alpha_zero :
    TraceForest.alpha (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.alpha_singleton (T : TraceTree α β) :
    TraceForest.alpha ({T} : TraceForest α β) = T.accCount := by
  unfold alpha
  rw [Multiset.map_singleton, Multiset.sum_singleton]

@[simp] theorem TraceForest.alpha_cons (T : TraceTree α β) (F : TraceForest α β) :
    TraceForest.alpha (T ::ₘ F) = T.accCount + F.alpha := by
  show Multiset.sum (Multiset.map _ (T ::ₘ F)) = T.accCount + Multiset.sum _
  rw [Multiset.map_cons, Multiset.sum_cons]

@[simp] theorem TraceForest.alpha_add (F G : TraceForest α β) :
    TraceForest.alpha (F + G) = F.alpha + G.alpha := by
  show Multiset.sum (Multiset.map _ (F + G)) = _
  rw [Multiset.map_add, Multiset.sum_add]
  rfl

/-- `σ(F) = b₀(F) + α(F)` — total accessible-terms-of-forest measure
    (M-C-B §1.6.1 eq. 1.6.1). Equals `#Acc'(F)` where `Acc'` counts each
    component's root as its own accessible term. -/
def TraceForest.sigma (F : TraceForest α β) : Nat := F.b₀ + F.alpha

@[simp] theorem TraceForest.sigma_zero :
    TraceForest.sigma (0 : TraceForest α β) = 0 := by
  unfold sigma; simp only [b₀_zero, alpha_zero]

@[simp] theorem TraceForest.sigma_singleton (T : TraceTree α β) :
    TraceForest.sigma ({T} : TraceForest α β) = 1 + T.accCount := by
  unfold sigma; rw [b₀_singleton, alpha_singleton]

@[simp] theorem TraceForest.sigma_cons (T : TraceTree α β) (F : TraceForest α β) :
    TraceForest.sigma (T ::ₘ F) = 1 + T.accCount + F.sigma := by
  unfold sigma; rw [b₀_cons, alpha_cons]; omega

@[simp] theorem TraceForest.sigma_add (F G : TraceForest α β) :
    TraceForest.sigma (F + G) = F.sigma + G.sigma := by
  unfold sigma; rw [b₀_add, alpha_add]; omega

/-- **MCB Lemma 1.6.3 eq. 1.6.6** (book p. 65): `σ(M(T_v, T_w)) = σ(T_v) +
    σ(T_w) + 1` at the singleton-forest level. -/
theorem TraceForest.sigma_merge_singleton (T_v T_w : TraceTree α β) :
    TraceForest.sigma ({TraceTree.node T_v T_w} : TraceForest α β)
      = TraceForest.sigma ({T_v} : TraceForest α β)
        + TraceForest.sigma ({T_w} : TraceForest α β) + 1 := by
  rw [sigma_singleton, sigma_singleton, sigma_singleton,
      TraceTree.accCount_merge]
  omega

end ConnesKreimer
