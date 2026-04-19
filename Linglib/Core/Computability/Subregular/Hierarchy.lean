import Linglib.Core.Computability.Subregular.LocallyTestable
import Linglib.Core.Computability.Subregular.Tier

/-!
# Subregular Hierarchy: Inclusion Theorems

Inclusions between the local subregular classes formalized in this directory.
This is the language-theoretic skeleton of Lambert (2022) Figure 3.1
@cite{lambert-2022}, restricted to the local (factor-based) classes:

```
   SL_k  ⊆  LT_k          (presence-of-factor only; ignore order/multiplicity)
   SL_k  ⊆  TSL_k         (TSL with universal tier reduces to SL)
   LT_k  ⊆  LTT_{k,t}     (set-of-factors as t = 1 saturated count)
```

The vertical inclusion across `k` (SL_k ⊆ SL_{k+1}, etc.) is genuine but
non-trivial to prove: `boundary k` and `boundary (k+1)` differ in their
edge padding, so a `k`-factor of `boundary k w` does not embed verbatim into
a `(k+1)`-factor of `boundary (k+1) w`. The standard textbook construction
uses the equivalent finite-state characterization (each level adds one
state of memory, inclusion is then immediate), which we don't yet have
infrastructure for. Deferred.

The *piecewise* counterparts (SP_k, TSP_k) and the strict-separation
witnesses live in their own files (`Subregular/Piecewise.lean` once added;
separations require concrete counterexample languages).
-/

namespace Core.Computability.Subregular

universe u

variable {α : Type u}

-- ============================================================================
-- § 1: SL_k ⊆ LT_k
-- ============================================================================

/-- Every SL_k language is LT_k. -/
theorem IsSLk.toIsLTk {k : ℕ} {L : Language α} (h : IsSLk k L) : IsLTk k L :=
  isSLk_imp_isLTk h

-- ============================================================================
-- § 2: SL_k ⊆ TSL_k
-- ============================================================================

/-- Every SL_k language is TSL_k: take the universal tier (every symbol on
    tier), so projection is the identity and the TSL grammar's `lang`
    reduces to the underlying SL grammar's `lang`. -/
theorem IsSLk.toIsTSLk {k : ℕ} {L : Language α} (h : IsSLk k L) :
    TSLGrammar.IsTSLk k L := by
  obtain ⟨G, rfl⟩ := h
  refine ⟨⟨fun _ => True, fun _ => isTrue trivial, G.permitted⟩, ?_⟩
  funext w
  show TSLGrammar.lang _ w = G.lang w
  simp only [SLGrammar.lang, TSLGrammar.lang, project_univ]

-- ============================================================================
-- § 3: LT_k ⊆ LTT_{k,t}
-- ============================================================================

/-- **LT_k ⊆ LTT_{k,t}** for `t ≥ 1`. Strings with the same saturated factor
    counts have the same factor *set* (since a count of `0` is preserved by
    saturation iff the factor is absent), so closure under count-equivalence
    implies closure under set-equivalence. -/
theorem IsLTk.toIsLTTk [DecidableEq α] {k t : ℕ} (ht : 1 ≤ t)
    {L : Language α} (h : IsLTk k L) : IsLTTk k t L := by
  intro w₁ w₂ heq
  apply h
  ext f
  have key : ∀ w : List α, f ∈ factorSet k w ↔ 0 < factorCount k t f w := by
    intro w
    simp only [factorSet, Set.mem_setOf_eq, factorCount, lt_min_iff,
               List.count_pos_iff]
    exact ⟨fun hf => ⟨ht, hf⟩, fun ⟨_, hf⟩ => hf⟩
  rw [key w₁, key w₂, heq f]

end Core.Computability.Subregular
