import Linglib.Core.Combinatorics.RootedTree.Decorated

/-!
# Forest size measures (b₀, α, σ)
@cite{marcolli-chomsky-berwick-2025} §1.2.2 (Definition 1.2.2) + §1.6.1 (eq. 1.6.1)

Three counting functions on a `TraceForest α β`:

- **`b₀(F)` — number of components**: the cardinality of `F` as a multiset.
  The "Betti number" of the forest in topological notation. Implemented
  as `Multiset.card`.

- **`α(F)` — number of accessible terms**: per MCB Def 1.2.2 + 1.6.1,
  `α(F) = Σ_T #Acc(T)` where `Acc(T) = {T_v | v ∈ V_int(T)}` and
  `V_int(T) := V(T) \ {root}` (M-C-B's "internal" excludes the root vertex
  but **includes leaves** — verified against `AdmissibleCut.lean`'s
  Crucial reading section). For a `TraceTree`, `#V(T) = T.size`, so
  `#Acc(T) = T.size - 1`.

- **`σ(F)` — total of components plus accessible terms (eq. 1.6.1)**:
  `σ(F) = b₀(F) + α(F)`.

These are the size measures used in linguistic-side downstream theories
(e.g., MCB's Definition 1.6.1 Minimal Yield principle) to constrain how
forest-transforming operations affect counts. Generic over leaf alphabet
`α` and trace alphabet `β`. Pure combinatorial substrate — no Hopf
algebra dependency.
-/

namespace ConnesKreimer

variable {α β : Type*}

/-- Number of accessible terms of a tree: `#V(T) - 1` per MCB Def 1.2.2,
    where `V_int(T) = V(T) \ {root}` includes leaves and traces. -/
def TraceTree.accCount : TraceTree α β → Nat := fun T => T.size - 1

@[simp] theorem TraceTree.accCount_leaf (a : α) :
    (TraceTree.leaf a : TraceTree α β).accCount = 0 := rfl

@[simp] theorem TraceTree.accCount_trace (b : β) :
    (TraceTree.trace b : TraceTree α β).accCount = 0 := rfl

@[simp] theorem TraceTree.accCount_node (l r : TraceTree α β) :
    (TraceTree.node l r).accCount = l.size + r.size := by
  show (1 + l.size + r.size) - 1 = l.size + r.size
  omega

/-- `b₀(F)` — the number of components of the workspace `F`. M-C-B
    Definition 1.2.2 (book p. 22). -/
def TraceForest.b0 (F : TraceForest α β) : Nat := Multiset.card F

@[simp] theorem TraceForest.b0_zero :
    TraceForest.b0 (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.b0_singleton (T : TraceTree α β) :
    TraceForest.b0 ({T} : TraceForest α β) = 1 := by
  simp [b0]

@[simp] theorem TraceForest.b0_cons (T : TraceTree α β) (F : TraceForest α β) :
    TraceForest.b0 (T ::ₘ F) = 1 + F.b0 := by
  show Multiset.card (T ::ₘ F) = 1 + Multiset.card F
  rw [Multiset.card_cons]; omega

@[simp] theorem TraceForest.b0_add (F G : TraceForest α β) :
    TraceForest.b0 (F + G) = F.b0 + G.b0 := by
  show Multiset.card (F + G) = Multiset.card F + Multiset.card G
  exact Multiset.card_add F G

/-- `α(F)` — total number of accessible terms across all components of `F`.
    M-C-B Definition 1.2.2 / Definition 1.6.1 (book pp. 22, 63). -/
def TraceForest.alpha (F : TraceForest α β) : Nat :=
  Multiset.sum (Multiset.map TraceTree.accCount F)

@[simp] theorem TraceForest.alpha_zero :
    TraceForest.alpha (0 : TraceForest α β) = 0 := rfl

@[simp] theorem TraceForest.alpha_singleton (T : TraceTree α β) :
    TraceForest.alpha ({T} : TraceForest α β) = T.accCount := by
  simp [alpha]

@[simp] theorem TraceForest.alpha_cons (T : TraceTree α β) (F : TraceForest α β) :
    TraceForest.alpha (T ::ₘ F) = T.accCount + F.alpha := by
  show Multiset.sum (Multiset.map _ (T ::ₘ F)) = T.accCount + Multiset.sum _
  rw [Multiset.map_cons, Multiset.sum_cons]

@[simp] theorem TraceForest.alpha_add (F G : TraceForest α β) :
    TraceForest.alpha (F + G) = F.alpha + G.alpha := by
  show Multiset.sum (Multiset.map _ (F + G)) = _
  rw [Multiset.map_add, Multiset.sum_add]
  rfl

/-- `σ(F) = b₀(F) + α(F)` — total accessible-terms-of-workspace measure
    (M-C-B eq. 1.6.1, book p. 62). Equals `#Acc'(F)` where `Acc'`
    counts each component's root as its own accessible term. -/
def TraceForest.sigma (F : TraceForest α β) : Nat := F.b0 + F.alpha

@[simp] theorem TraceForest.sigma_zero :
    TraceForest.sigma (0 : TraceForest α β) = 0 := by
  simp [sigma]

@[simp] theorem TraceForest.sigma_singleton (T : TraceTree α β) :
    TraceForest.sigma ({T} : TraceForest α β) = 1 + T.accCount := by
  simp [sigma]

@[simp] theorem TraceForest.sigma_add (F G : TraceForest α β) :
    TraceForest.sigma (F + G) = F.sigma + G.sigma := by
  simp [sigma]; omega

end ConnesKreimer
