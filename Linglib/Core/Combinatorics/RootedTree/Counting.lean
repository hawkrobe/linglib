import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Size counting on nonplanar rooted trees

The MCB size measures for syntactic-object combinatorics
([marcolli-chomsky-berwick-2025]), on the canonical `Nonplanar` carrier.
These permutation-invariant counts build directly on the lifted
`Nonplanar.weight`; the legacy planar `Decorated`/`AdmissibleCut` substrate
provided the same measures over the unfaithful planar-binary `TraceTree`.

## Main definitions

* `Nonplanar.accCount` — accessible-term count `α(T) = #V(T) - 1`.

## Main results

* `Nonplanar.accCount_merge` — external Merge `M(T_v, T_w)` adds two accessible
  terms (MCB Lemma 1.6.3, eq. 1.6.5).

## TODO

* Forest measures `b₀`/`alpha`/`sigma` on `Multiset (Nonplanar α)`.
* Trace-aware `nonTraceSize`/`accCountC` on `Nonplanar (α ⊕ β)` (contraction count).
* The admissible-cut layer (`Fintype`-enumerable cuts + conservation lemmas).
-/

namespace RootedTree.Nonplanar

variable {α : Type*}

/-- The **accessible-term count** `α(T) = #V(T) - 1`: the number of proper
subterms of a syntactic object. -/
def accCount (t : Nonplanar α) : Nat := t.weight - 1

@[simp] theorem accCount_leaf (a : α) : (leaf a : Nonplanar α).accCount = 0 := by
  simp only [accCount, weight_leaf]

theorem accCount_eq_weight_sub_one (t : Nonplanar α) : t.accCount = t.weight - 1 := rfl

/-- External Merge of two syntactic objects adds exactly two accessible terms
(MCB Lemma 1.6.3, eq. 1.6.5). -/
theorem accCount_merge (a : α) (l r : Nonplanar α) :
    (node a {l, r}).accCount = l.accCount + r.accCount + 2 := by
  have hl := l.weight_pos
  have hr := r.weight_pos
  simp only [accCount, weight_node, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton]
  omega

end RootedTree.Nonplanar
